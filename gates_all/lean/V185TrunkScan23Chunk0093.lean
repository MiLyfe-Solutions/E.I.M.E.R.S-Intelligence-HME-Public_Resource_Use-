import V185TrunkScan23Chunk0092

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_551669 : List Nat := [1, 3, 6, 1, 1, 2, 1, 2, 6]
def baseStart_551669 : Nat := 118140960795 + 551669 * 2 ^ 59
def prefixEnd_551669 : Nat := 4983230072969 + 3 ^ 40 * 551669 * 2
def baseEnd_551669 : Nat := 31474595465034147355603

theorem tailTrace_551669 : CollatzResearch.WordTrace tailWord_551669 prefixEnd_551669 31474595465034147355603 := by
  unfold tailWord_551669
  simp only [CollatzResearch.WordTrace]
  refine ⟨20121021438404905409266061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13414014292269936939510707 20121021438404905409266061)
  ·
    refine ⟨7545383039401839528474773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20121021438404905409266061 7545383039401839528474773)
    ·
      refine ⟨353689829971961227897255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7545383039401839528474773 353689829971961227897255)
      ·
        refine ⟨530534744957941841845883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353689829971961227897255 530534744957941841845883)
        ·
          refine ⟨795802117436912762768825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530534744957941841845883 795802117436912762768825)
          ·
            refine ⟨596851588077684572076619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 795802117436912762768825 596851588077684572076619)
            ·
              refine ⟨895277382116526858114929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596851588077684572076619 895277382116526858114929)
              ·
                refine ⟨671458036587395143586197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895277382116526858114929 671458036587395143586197)
                ·
                  refine ⟨31474595465034147355603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 671458036587395143586197 31474595465034147355603)
                  ·
                    rfl

theorem cell23_551669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 6].length) (baseStart_551669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551669 prefixEnd_551669 := by exact prefixLift 551669
  have htrace : WordTrace (prefixWord ++ tailWord_551669) baseStart_551669 baseEnd_551669 := by
    simpa [prefixWord, tailWord_551669, baseEnd_551669] using wordTrace_append hprefix tailTrace_551669
  have hstable : (prefixWord ++ tailWord_551669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551669).length < 2 ^ (prefixWord ++ tailWord_551669).sum := by decide
  have hdescent : baseEnd_551669 < baseStart_551669 := by decide
  rcases family_descends (prefixWord ++ tailWord_551669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551671 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_551671 : Nat := 118140960795 + 551671 * 2 ^ 59
def prefixEnd_551671 : Nat := 4983230072969 + 3 ^ 40 * 551671 * 2
def baseEnd_551671 : Nat := 283272386146616318375417

theorem tailTrace_551671 : CollatzResearch.WordTrace tailWord_551671 prefixEnd_551671 283272386146616318375417 := by
  unfold tailWord_551671
  simp only [CollatzResearch.WordTrace]
  refine ⟨20121094384397659750838867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13414062922931773167225911 20121094384397659750838867)
  ·
    refine ⟨30181641576596489626258301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20121094384397659750838867 30181641576596489626258301)
    ·
      refine ⟨11318115591223683609846863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30181641576596489626258301 11318115591223683609846863)
      ·
        refine ⟨16977173386835525414770295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11318115591223683609846863 16977173386835525414770295)
        ·
          refine ⟨25465760080253288122155443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16977173386835525414770295 25465760080253288122155443)
          ·
            refine ⟨38198640120379932183233165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25465760080253288122155443 38198640120379932183233165)
            ·
              refine ⟨14324490045142474568712437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38198640120379932183233165 14324490045142474568712437)
              ·
                refine ⟨1342920941732106990816791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14324490045142474568712437 1342920941732106990816791)
                ·
                  refine ⟨2014381412598160486225187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342920941732106990816791 2014381412598160486225187)
                  ·
                    refine ⟨3021572118897240729337781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2014381412598160486225187 3021572118897240729337781)
                    ·
                      refine ⟨283272386146616318375417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3021572118897240729337781 283272386146616318375417)
                      ·
                        rfl

theorem cell23_551671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_551671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551671 prefixEnd_551671 := by exact prefixLift 551671
  have htrace : WordTrace (prefixWord ++ tailWord_551671) baseStart_551671 baseEnd_551671 := by
    simpa [prefixWord, tailWord_551671, baseEnd_551671] using wordTrace_append hprefix tailTrace_551671
  have hstable : (prefixWord ++ tailWord_551671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551671).length < 2 ^ (prefixWord ++ tailWord_551671).sum := by decide
  have hdescent : baseEnd_551671 < baseStart_551671 := by decide
  rcases family_descends (prefixWord ++ tailWord_551671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551681 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_551681 : Nat := 118140960795 + 551681 * 2 ^ 59
def prefixEnd_551681 : Nat := 4983230072969 + 3 ^ 40 * 551681 * 2
def baseEnd_551681 : Nat := 283277520953161279250371

theorem tailTrace_551681 : CollatzResearch.WordTrace tailWord_551681 prefixEnd_551681 283277520953161279250371 := by
  unfold tailWord_551681
  simp only [CollatzResearch.WordTrace]
  refine ⟨20121459114361431458702897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13414306076240954305801931 20121459114361431458702897)
  ·
    refine ⟨15091094335771073594027173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20121459114361431458702897 15091094335771073594027173)
    ·
      refine ⟨2829580187957076298880095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15091094335771073594027173 2829580187957076298880095)
      ·
        refine ⟨4244370281935614448320143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2829580187957076298880095 4244370281935614448320143)
        ·
          refine ⟨6366555422903421672480215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244370281935614448320143 6366555422903421672480215)
          ·
            refine ⟨9549833134355132508720323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6366555422903421672480215 9549833134355132508720323)
            ·
              refine ⟨14324749701532698763080485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9549833134355132508720323 14324749701532698763080485)
              ·
                refine ⟨2685890569037381018077591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14324749701532698763080485 2685890569037381018077591)
                ·
                  refine ⟨4028835853556071527116387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685890569037381018077591 4028835853556071527116387)
                  ·
                    refine ⟨6043253780334107290674581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4028835853556071527116387 6043253780334107290674581)
                    ·
                      refine ⟨283277520953161279250371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6043253780334107290674581 283277520953161279250371)
                      ·
                        rfl

theorem cell23_551681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_551681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551681 prefixEnd_551681 := by exact prefixLift 551681
  have htrace : WordTrace (prefixWord ++ tailWord_551681) baseStart_551681 baseEnd_551681 := by
    simpa [prefixWord, tailWord_551681, baseEnd_551681] using wordTrace_append hprefix tailTrace_551681
  have hstable : (prefixWord ++ tailWord_551681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551681).length < 2 ^ (prefixWord ++ tailWord_551681).sum := by decide
  have hdescent : baseEnd_551681 < baseStart_551681 := by decide
  rcases family_descends (prefixWord ++ tailWord_551681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551688 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_551688 : Nat := 118140960795 + 551688 * 2 ^ 59
def prefixEnd_551688 : Nat := 4983230072969 + 3 ^ 40 * 551688 * 2
def baseEnd_551688 : Nat := 283281115317742751862839

theorem tailTrace_551688 : CollatzResearch.WordTrace tailWord_551688 prefixEnd_551688 283281115317742751862839 := by
  unfold tailWord_551688
  simp only [CollatzResearch.WordTrace]
  refine ⟨10060857212668035827103859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13414476283557381102805145 10060857212668035827103859)
  ·
    refine ⟨15091285819002053740655789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10060857212668035827103859 15091285819002053740655789)
    ·
      refine ⟨5659232182125770152745921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15091285819002053740655789 5659232182125770152745921)
      ·
        refine ⟨4244424136594327614559441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5659232182125770152745921 4244424136594327614559441)
        ·
          refine ⟨3183318102445745710919581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4244424136594327614559441 3183318102445745710919581)
          ·
            refine ⟨1193744288417154641594843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3183318102445745710919581 1193744288417154641594843)
            ·
              refine ⟨1790616432625731962392265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193744288417154641594843 1790616432625731962392265)
              ·
                refine ⟨1342962324469298971794199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1790616432625731962392265 1342962324469298971794199)
                ·
                  refine ⟨2014443486703948457691299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342962324469298971794199 2014443486703948457691299)
                  ·
                    refine ⟨3021665230055922686536949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2014443486703948457691299 3021665230055922686536949)
                    ·
                      refine ⟨283281115317742751862839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3021665230055922686536949 283281115317742751862839)
                      ·
                        rfl

theorem cell23_551688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_551688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551688 prefixEnd_551688 := by exact prefixLift 551688
  have htrace : WordTrace (prefixWord ++ tailWord_551688) baseStart_551688 baseEnd_551688 := by
    simpa [prefixWord, tailWord_551688, baseEnd_551688] using wordTrace_append hprefix tailTrace_551688
  have hstable : (prefixWord ++ tailWord_551688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551688).length < 2 ^ (prefixWord ++ tailWord_551688).sum := by decide
  have hdescent : baseEnd_551688 < baseStart_551688 := by decide
  rcases family_descends (prefixWord ++ tailWord_551688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551695 : List Nat := [1, 1, 2, 1, 1, 1, 9, 1, 2, 4]
def baseStart_551695 : Nat := 118140960795 + 551695 * 2 ^ 59
def prefixEnd_551695 : Nat := 4983230072969 + 3 ^ 40 * 551695 * 2
def baseEnd_551695 : Nat := 94428236560774741491769

theorem tailTrace_551695 : CollatzResearch.WordTrace tailWord_551695 prefixEnd_551695 94428236560774741491769 := by
  unfold tailWord_551695
  simp only [CollatzResearch.WordTrace]
  refine ⟨20121969736310711849712539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13414646490873807899808359 20121969736310711849712539)
  ·
    refine ⟨30182954604466067774568809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20121969736310711849712539 30182954604466067774568809)
    ·
      refine ⟨22637215953349550830926607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30182954604466067774568809 22637215953349550830926607)
      ·
        refine ⟨33955823930024326246389911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22637215953349550830926607 33955823930024326246389911)
        ·
          refine ⟨50933735895036489369584867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33955823930024326246389911 50933735895036489369584867)
          ·
            refine ⟨76400603842554734054377301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50933735895036489369584867 76400603842554734054377301)
            ·
              refine ⟨447659788139969144849867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 76400603842554734054377301 447659788139969144849867)
              ·
                refine ⟨671489682209953717274801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447659788139969144849867 671489682209953717274801)
                ·
                  refine ⟨503617261657465287956101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 671489682209953717274801 503617261657465287956101)
                  ·
                    refine ⟨94428236560774741491769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 503617261657465287956101 94428236560774741491769)
                    ·
                      rfl

theorem cell23_551695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 2, 4].length) (baseStart_551695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551695 prefixEnd_551695 := by exact prefixLift 551695
  have htrace : WordTrace (prefixWord ++ tailWord_551695) baseStart_551695 baseEnd_551695 := by
    simpa [prefixWord, tailWord_551695, baseEnd_551695] using wordTrace_append hprefix tailTrace_551695
  have hstable : (prefixWord ++ tailWord_551695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551695).length < 2 ^ (prefixWord ++ tailWord_551695).sum := by decide
  have hdescent : baseEnd_551695 < baseStart_551695 := by decide
  rcases family_descends (prefixWord ++ tailWord_551695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551708 : List Nat := [2, 2, 3, 1, 1, 3, 4, 7]
def baseStart_551708 : Nat := 118140960795 + 551708 * 2 ^ 59
def prefixEnd_551708 : Nat := 4983230072969 + 3 ^ 40 * 551708 * 2
def baseEnd_551708 : Nat := 10492273515956765689361

theorem tailTrace_551708 : CollatzResearch.WordTrace tailWord_551708 prefixEnd_551708 10492273515956765689361 := by
  unfold tailWord_551708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10061221942631807534967889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13414962590175743379957185 10061221942631807534967889)
  ·
    refine ⟨7545916456973855651225917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10061221942631807534967889 7545916456973855651225917)
    ·
      refine ⟨2829718671365195869209719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7545916456973855651225917 2829718671365195869209719)
      ·
        refine ⟨4244578007047793803814579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2829718671365195869209719 4244578007047793803814579)
        ·
          refine ⟨6366867010571690705721869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244578007047793803814579 6366867010571690705721869)
          ·
            refine ⟨2387575128964384014645701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6366867010571690705721869 2387575128964384014645701)
            ·
              refine ⟨447670336680822002746069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2387575128964384014645701 447670336680822002746069)
              ·
                refine ⟨10492273515956765689361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 447670336680822002746069 10492273515956765689361)
                ·
                  rfl

theorem cell23_551708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 7].length) (baseStart_551708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551708 prefixEnd_551708 := by exact prefixLift 551708
  have htrace : WordTrace (prefixWord ++ tailWord_551708) baseStart_551708 baseEnd_551708 := by
    simpa [prefixWord, tailWord_551708, baseEnd_551708] using wordTrace_append hprefix tailTrace_551708
  have hstable : (prefixWord ++ tailWord_551708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551708).length < 2 ^ (prefixWord ++ tailWord_551708).sum := by decide
  have hdescent : baseEnd_551708 < baseStart_551708 := by decide
  rcases family_descends (prefixWord ++ tailWord_551708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551722 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_551722 : Nat := 118140960795 + 551722 * 2 ^ 59
def prefixEnd_551722 : Nat := 4983230072969 + 3 ^ 40 * 551722 * 2
def baseEnd_551722 : Nat := 283298573659995618837683

theorem tailTrace_551722 : CollatzResearch.WordTrace tailWord_551722 prefixEnd_551722 283298573659995618837683 := by
  unfold tailWord_551722
  simp only [CollatzResearch.WordTrace]
  refine ⟨5030738626803223865236355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13415303004808596973963613 5030738626803223865236355)
  ·
    refine ⟨7546107940204835797854533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5030738626803223865236355 7546107940204835797854533)
    ·
      refine ⟨1414895238788406712097725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7546107940204835797854533 1414895238788406712097725)
      ·
        refine ⟨530585714545652517036647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1414895238788406712097725 530585714545652517036647)
        ·
          refine ⟨795878571818478775554971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530585714545652517036647 795878571818478775554971)
          ·
            refine ⟨1193817857727718163332457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795878571818478775554971 1193817857727718163332457)
            ·
              refine ⟨895363393295788622499343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1193817857727718163332457 895363393295788622499343)
              ·
                refine ⟨1343045089943682933749015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895363393295788622499343 1343045089943682933749015)
                ·
                  refine ⟨2014567634915524400623523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343045089943682933749015 2014567634915524400623523)
                  ·
                    refine ⟨3021851452373286600935285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2014567634915524400623523 3021851452373286600935285)
                    ·
                      refine ⟨283298573659995618837683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3021851452373286600935285 283298573659995618837683)
                      ·
                        rfl

theorem cell23_551722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_551722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551722 prefixEnd_551722 := by exact prefixLift 551722
  have htrace : WordTrace (prefixWord ++ tailWord_551722) baseStart_551722 baseEnd_551722 := by
    simpa [prefixWord, tailWord_551722, baseEnd_551722] using wordTrace_append hprefix tailTrace_551722
  have hstable : (prefixWord ++ tailWord_551722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551722).length < 2 ^ (prefixWord ++ tailWord_551722).sum := by decide
  have hdescent : baseEnd_551722 < baseStart_551722 := by decide
  rcases family_descends (prefixWord ++ tailWord_551722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551735 : List Nat := [1, 1, 3, 1, 2, 1, 4, 4, 2, 1, 3]
def baseStart_551735 : Nat := 118140960795 + 551735 * 2 ^ 59
def prefixEnd_551735 : Nat := 4983230072969 + 3 ^ 40 * 551735 * 2
def baseEnd_551735 : Nat := 283305248908504067975123

theorem tailTrace_551735 : CollatzResearch.WordTrace tailWord_551735 prefixEnd_551735 283305248908504067975123 := by
  unfold tailWord_551735
  simp only [CollatzResearch.WordTrace]
  refine ⟨20123428656165798681168659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13415619104110532454112439 20123428656165798681168659)
  ·
    refine ⟨30185142984248698021752989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20123428656165798681168659 30185142984248698021752989)
    ·
      refine ⟨11319428619093261758157371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30185142984248698021752989 11319428619093261758157371)
      ·
        refine ⟨16979142928639892637236057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11319428619093261758157371 16979142928639892637236057)
        ·
          refine ⟨12734357196479919477927043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16979142928639892637236057 12734357196479919477927043)
          ·
            refine ⟨19101535794719879216890565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12734357196479919477927043 19101535794719879216890565)
            ·
              refine ⟨3581537961509977353166981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19101535794719879216890565 3581537961509977353166981)
              ·
                refine ⟨671538367783120753718809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3581537961509977353166981 671538367783120753718809)
                ·
                  refine ⟨503653775837340565289107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 671538367783120753718809 503653775837340565289107)
                  ·
                    refine ⟨755480663756010847933661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 503653775837340565289107 755480663756010847933661)
                    ·
                      refine ⟨283305248908504067975123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 755480663756010847933661 283305248908504067975123)
                      ·
                        rfl

theorem cell23_551735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_551735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551735 prefixEnd_551735 := by exact prefixLift 551735
  have htrace : WordTrace (prefixWord ++ tailWord_551735) baseStart_551735 baseEnd_551735 := by
    simpa [prefixWord, tailWord_551735, baseEnd_551735] using wordTrace_append hprefix tailTrace_551735
  have hstable : (prefixWord ++ tailWord_551735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551735).length < 2 ^ (prefixWord ++ tailWord_551735).sum := by decide
  have hdescent : baseEnd_551735 < baseStart_551735 := by decide
  rcases family_descends (prefixWord ++ tailWord_551735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551751 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 1, 8]
def baseStart_551751 : Nat := 118140960795 + 551751 * 2 ^ 59
def prefixEnd_551751 : Nat := 4983230072969 + 3 ^ 40 * 551751 * 2
def baseEnd_551751 : Nat := 94437821532992001791683

theorem tailTrace_551751 : CollatzResearch.WordTrace tailWord_551751 prefixEnd_551751 94437821532992001791683 := by
  unfold tailWord_551751
  simp only [CollatzResearch.WordTrace]
  refine ⟨20124012224107833413751107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13416008149405222275834071 20124012224107833413751107)
  ·
    refine ⟨30186018336161750120626661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20124012224107833413751107 30186018336161750120626661)
    ·
      refine ⟨5659878438030328147617499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30186018336161750120626661 5659878438030328147617499)
      ·
        refine ⟨8489817657045492221426249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5659878438030328147617499 8489817657045492221426249)
        ·
          refine ⟨6367363242784119166069687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8489817657045492221426249 6367363242784119166069687)
          ·
            refine ⟨9551044864176178749104531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6367363242784119166069687 9551044864176178749104531)
            ·
              refine ⟨14326567296264268123656797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9551044864176178749104531 14326567296264268123656797)
              ·
                refine ⟨5372462736099100546371299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14326567296264268123656797 5372462736099100546371299)
                ·
                  refine ⟨8058694104148650819556949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5372462736099100546371299 8058694104148650819556949)
                  ·
                    refine ⟨94437821532992001791683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8058694104148650819556949 94437821532992001791683)
                    ·
                      rfl

theorem cell23_551751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_551751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551751 prefixEnd_551751 := by exact prefixLift 551751
  have htrace : WordTrace (prefixWord ++ tailWord_551751) baseStart_551751 baseEnd_551751 := by
    simpa [prefixWord, tailWord_551751, baseEnd_551751] using wordTrace_append hprefix tailTrace_551751
  have hstable : (prefixWord ++ tailWord_551751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551751).length < 2 ^ (prefixWord ++ tailWord_551751).sum := by decide
  have hdescent : baseEnd_551751 < baseStart_551751 := by decide
  rcases family_descends (prefixWord ++ tailWord_551751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551775 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 1, 4, 2]
def baseStart_551775 : Nat := 118140960795 + 551775 * 2 ^ 59
def prefixEnd_551775 : Nat := 4983230072969 + 3 ^ 40 * 551775 * 2
def baseEnd_551775 : Nat := 283325788134683911474939

theorem tailTrace_551775 : CollatzResearch.WordTrace tailWord_551775 prefixEnd_551775 283325788134683911474939 := by
  unfold tailWord_551775
  simp only [CollatzResearch.WordTrace]
  refine ⟨20124887576020885512624779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13416591717347257008416519 20124887576020885512624779)
  ·
    refine ⟨30187331364031328268937169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20124887576020885512624779 30187331364031328268937169)
    ·
      refine ⟨22640498523023496201702877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30187331364031328268937169 22640498523023496201702877)
      ·
        refine ⟨8490186946133811075638579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22640498523023496201702877 8490186946133811075638579)
        ·
          refine ⟨12735280419200716613457869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8490186946133811075638579 12735280419200716613457869)
          ·
            refine ⟨4775730157200268730046701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12735280419200716613457869 4775730157200268730046701)
            ·
              refine ⟨1790898808950100773767513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4775730157200268730046701 1790898808950100773767513)
              ·
                refine ⟨1343174106712575580325635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1790898808950100773767513 1343174106712575580325635)
                ·
                  refine ⟨2014761160068863370488453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343174106712575580325635 2014761160068863370488453)
                  ·
                    refine ⟨377767717512911881966585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2014761160068863370488453 377767717512911881966585)
                    ·
                      refine ⟨283325788134683911474939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 377767717512911881966585 283325788134683911474939)
                      ·
                        rfl

theorem cell23_551775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_551775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551775 prefixEnd_551775 := by exact prefixLift 551775
  have htrace : WordTrace (prefixWord ++ tailWord_551775) baseStart_551775 baseEnd_551775 := by
    simpa [prefixWord, tailWord_551775, baseEnd_551775] using wordTrace_append hprefix tailTrace_551775
  have hstable : (prefixWord ++ tailWord_551775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551775).length < 2 ^ (prefixWord ++ tailWord_551775).sum := by decide
  have hdescent : baseEnd_551775 < baseStart_551775 := by decide
  rcases family_descends (prefixWord ++ tailWord_551775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551779 : List Nat := [1, 1, 1, 5, 3, 2, 3, 1, 1, 3, 2]
def baseStart_551779 : Nat := 118140960795 + 551779 * 2 ^ 59
def prefixEnd_551779 : Nat := 4983230072969 + 3 ^ 40 * 551779 * 2
def baseEnd_551779 : Nat := 283327842057301895824921

theorem tailTrace_551779 : CollatzResearch.WordTrace tailWord_551779 prefixEnd_551779 283327842057301895824921 := by
  unfold tailWord_551779
  simp only [CollatzResearch.WordTrace]
  refine ⟨20125033468006394195770391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13416688978670929463846927 20125033468006394195770391)
  ·
    refine ⟨30187550202009591293655587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20125033468006394195770391 30187550202009591293655587)
    ·
      refine ⟨45281325303014386940483381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30187550202009591293655587 45281325303014386940483381)
      ·
        refine ⟨4245124247157598775670317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45281325303014386940483381 4245124247157598775670317)
        ·
          refine ⟨1591921592684099540876369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4245124247157598775670317 1591921592684099540876369)
          ·
            refine ⟨1193941194513074655657277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1591921592684099540876369 1193941194513074655657277)
            ·
              refine ⟨447727947942402995871479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1193941194513074655657277 447727947942402995871479)
              ·
                refine ⟨671591921913604493807219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447727947942402995871479 671591921913604493807219)
                ·
                  refine ⟨1007387882870406740710829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 671591921913604493807219 1007387882870406740710829)
                  ·
                    refine ⟨377770456076402527766561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1007387882870406740710829 377770456076402527766561)
                    ·
                      refine ⟨283327842057301895824921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 377770456076402527766561 283327842057301895824921)
                      ·
                        rfl

theorem cell23_551779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_551779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551779 prefixEnd_551779 := by exact prefixLift 551779
  have htrace : WordTrace (prefixWord ++ tailWord_551779) baseStart_551779 baseEnd_551779 := by
    simpa [prefixWord, tailWord_551779, baseEnd_551779] using wordTrace_append hprefix tailTrace_551779
  have hstable : (prefixWord ++ tailWord_551779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551779).length < 2 ^ (prefixWord ++ tailWord_551779).sum := by decide
  have hdescent : baseEnd_551779 < baseStart_551779 := by decide
  rcases family_descends (prefixWord ++ tailWord_551779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551788 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_551788 : Nat := 118140960795 + 551788 * 2 ^ 59
def prefixEnd_551788 : Nat := 4983230072969 + 3 ^ 40 * 551788 * 2
def baseEnd_551788 : Nat := 283332463383192360612379

theorem tailTrace_551788 : CollatzResearch.WordTrace tailWord_551788 prefixEnd_551788 283332463383192360612379 := by
  unfold tailWord_551788
  simp only [CollatzResearch.WordTrace]
  refine ⟨10062680862486894366424009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13416907816649192488565345 10062680862486894366424009)
  ·
    refine ⟨7547010646865170774818007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10062680862486894366424009 7547010646865170774818007)
    ·
      refine ⟨11320515970297756162227011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7547010646865170774818007 11320515970297756162227011)
      ·
        refine ⟨16980773955446634243340517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11320515970297756162227011 16980773955446634243340517)
        ·
          refine ⟨3183895116646243920626347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16980773955446634243340517 3183895116646243920626347)
          ·
            refine ⟨4775842674969365880939521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3183895116646243920626347 4775842674969365880939521)
            ·
              refine ⟨3581882006227024410704641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4775842674969365880939521 3581882006227024410704641)
              ·
                refine ⟨2686411504670268308028481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3581882006227024410704641 2686411504670268308028481)
                ·
                  refine ⟨2014808628502701231021361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2686411504670268308028481 2014808628502701231021361)
                  ·
                    refine ⟨1511106471377025923266021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2014808628502701231021361 1511106471377025923266021)
                    ·
                      refine ⟨283332463383192360612379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1511106471377025923266021 283332463383192360612379)
                      ·
                        rfl

theorem cell23_551788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_551788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551788 prefixEnd_551788 := by exact prefixLift 551788
  have htrace : WordTrace (prefixWord ++ tailWord_551788) baseStart_551788 baseEnd_551788 := by
    simpa [prefixWord, tailWord_551788, baseEnd_551788] using wordTrace_append hprefix tailTrace_551788
  have hstable : (prefixWord ++ tailWord_551788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551788).length < 2 ^ (prefixWord ++ tailWord_551788).sum := by decide
  have hdescent : baseEnd_551788 < baseStart_551788 := by decide
  rcases family_descends (prefixWord ++ tailWord_551788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551791 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 7]
def baseStart_551791 : Nat := 118140960795 + 551791 * 2 ^ 59
def prefixEnd_551791 : Nat := 4983230072969 + 3 ^ 40 * 551791 * 2
def baseEnd_551791 : Nat := 283334003825155848874865

theorem tailTrace_551791 : CollatzResearch.WordTrace tailWord_551791 prefixEnd_551791 283334003825155848874865 := by
  unfold tailWord_551791
  simp only [CollatzResearch.WordTrace]
  refine ⟨20125471143962920245207227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13416980762641946830138151 20125471143962920245207227)
  ·
    refine ⟨30188206715944380367810841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20125471143962920245207227 30188206715944380367810841)
    ·
      refine ⟨22641155036958285275858131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30188206715944380367810841 22641155036958285275858131)
      ·
        refine ⟨33961732555437427913787197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22641155036958285275858131 33961732555437427913787197)
        ·
          refine ⟨12735649708289035467670199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33961732555437427913787197 12735649708289035467670199)
          ·
            refine ⟨19103474562433553201505299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12735649708289035467670199 19103474562433553201505299)
            ·
              refine ⟨28655211843650329802257949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19103474562433553201505299 28655211843650329802257949)
              ·
                refine ⟨10745704441368873675846731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28655211843650329802257949 10745704441368873675846731)
                ·
                  refine ⟨16118556662053310513770097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10745704441368873675846731 16118556662053310513770097)
                  ·
                    refine ⟨12088917496539982885327573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16118556662053310513770097 12088917496539982885327573)
                    ·
                      refine ⟨283334003825155848874865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12088917496539982885327573 283334003825155848874865)
                      ·
                        rfl

theorem cell23_551791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_551791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551791 prefixEnd_551791 := by exact prefixLift 551791
  have htrace : WordTrace (prefixWord ++ tailWord_551791) baseStart_551791 baseEnd_551791 := by
    simpa [prefixWord, tailWord_551791, baseEnd_551791] using wordTrace_append hprefix tailTrace_551791
  have hstable : (prefixWord ++ tailWord_551791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551791).length < 2 ^ (prefixWord ++ tailWord_551791).sum := by decide
  have hdescent : baseEnd_551791 < baseStart_551791 := by decide
  rcases family_descends (prefixWord ++ tailWord_551791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551792 : List Nat := [2, 1, 1, 1, 4, 1, 3, 4, 2, 2, 2]
def baseStart_551792 : Nat := 118140960795 + 551792 * 2 ^ 59
def prefixEnd_551792 : Nat := 4983230072969 + 3 ^ 40 * 551792 * 2
def baseEnd_551792 : Nat := 283334517305810344962361

theorem tailTrace_551792 : CollatzResearch.WordTrace tailWord_551792 prefixEnd_551792 283334517305810344962361 := by
  unfold tailWord_551792
  simp only [CollatzResearch.WordTrace]
  refine ⟨10062753808479648707996815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13417005077972864943995753 10062753808479648707996815)
  ·
    refine ⟨15094130712719473061995223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10062753808479648707996815 15094130712719473061995223)
    ·
      refine ⟨22641196069079209592992835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15094130712719473061995223 22641196069079209592992835)
      ·
        refine ⟨33961794103618814389489253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22641196069079209592992835 33961794103618814389489253)
        ·
          refine ⟨6367836394428527698029235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33961794103618814389489253 6367836394428527698029235)
          ·
            refine ⟨9551754591642791547043853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6367836394428527698029235 9551754591642791547043853)
            ·
              refine ⟨3581907971866046830141445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9551754591642791547043853 3581907971866046830141445)
              ·
                refine ⟨671607744724883780651521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3581907971866046830141445 671607744724883780651521)
                ·
                  refine ⟨503705808543662835488641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 671607744724883780651521 503705808543662835488641)
                  ·
                    refine ⟨377779356407747126616481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 503705808543662835488641 377779356407747126616481)
                    ·
                      refine ⟨283334517305810344962361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 377779356407747126616481 283334517305810344962361)
                      ·
                        rfl

theorem cell23_551792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 2, 2, 2].length) (baseStart_551792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551792 prefixEnd_551792 := by exact prefixLift 551792
  have htrace : WordTrace (prefixWord ++ tailWord_551792) baseStart_551792 baseEnd_551792 := by
    simpa [prefixWord, tailWord_551792, baseEnd_551792] using wordTrace_append hprefix tailTrace_551792
  have hstable : (prefixWord ++ tailWord_551792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551792).length < 2 ^ (prefixWord ++ tailWord_551792).sum := by decide
  have hdescent : baseEnd_551792 < baseStart_551792 := by decide
  rcases family_descends (prefixWord ++ tailWord_551792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551830 : List Nat := [5, 3, 1, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_551830 : Nat := 118140960795 + 551830 * 2 ^ 59
def prefixEnd_551830 : Nat := 4983230072969 + 3 ^ 40 * 551830 * 2
def baseEnd_551830 : Nat := 283354029570681196287187

theorem tailTrace_551830 : CollatzResearch.WordTrace tailWord_551830 prefixEnd_551830 283354029570681196287187 := by
  unfold tailWord_551830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1257930849426351869117309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13417929060547753270584629 1257930849426351869117309)
  ·
    refine ⟨471724068534881950918991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1257930849426351869117309 471724068534881950918991)
    ·
      refine ⟨707586102802322926378487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 471724068534881950918991 707586102802322926378487)
      ·
        refine ⟨1061379154203484389567731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 707586102802322926378487 1061379154203484389567731)
        ·
          refine ⟨1592068731305226584351597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061379154203484389567731 1592068731305226584351597)
          ·
            refine ⟨597025774239459969131849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1592068731305226584351597 597025774239459969131849)
            ·
              refine ⟨447769330679594976848887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597025774239459969131849 447769330679594976848887)
              ·
                refine ⟨671653996019392465273331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447769330679594976848887 671653996019392465273331)
                ·
                  refine ⟨1007480994029088697909997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 671653996019392465273331 1007480994029088697909997)
                  ·
                    refine ⟨377805372760908261716249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1007480994029088697909997 377805372760908261716249)
                    ·
                      refine ⟨283354029570681196287187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 377805372760908261716249 283354029570681196287187)
                      ·
                        rfl

theorem cell23_551830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_551830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551830 prefixEnd_551830 := by exact prefixLift 551830
  have htrace : WordTrace (prefixWord ++ tailWord_551830) baseStart_551830 baseEnd_551830 := by
    simpa [prefixWord, tailWord_551830, baseEnd_551830] using wordTrace_append hprefix tailTrace_551830
  have hstable : (prefixWord ++ tailWord_551830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551830).length < 2 ^ (prefixWord ++ tailWord_551830).sum := by decide
  have hdescent : baseEnd_551830 < baseStart_551830 := by decide
  rcases family_descends (prefixWord ++ tailWord_551830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551908 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_551908 : Nat := 118140960795 + 551908 * 2 ^ 59
def prefixEnd_551908 : Nat := 4983230072969 + 3 ^ 40 * 551908 * 2
def baseEnd_551908 : Nat := 283394081061731891111827

theorem tailTrace_551908 : CollatzResearch.WordTrace tailWord_551908 prefixEnd_551908 283394081061731891111827 := by
  unfold tailWord_551908
  simp only [CollatzResearch.WordTrace]
  refine ⟨10064869242269524613608189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13419825656359366151477585 10064869242269524613608189)
  ·
    refine ⟨3774325965851071730103071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10064869242269524613608189 3774325965851071730103071)
    ·
      refine ⟨5661488948776607595154607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3774325965851071730103071 5661488948776607595154607)
      ·
        refine ⟨8492233423164911392731911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5661488948776607595154607 8492233423164911392731911)
        ·
          refine ⟨12738350134747367089097867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8492233423164911392731911 12738350134747367089097867)
          ·
            refine ⟨19107525202121050633646801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12738350134747367089097867 19107525202121050633646801)
            ·
              refine ⟨14330643901590787975235101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19107525202121050633646801 14330643901590787975235101)
              ·
                refine ⟨5373991463096545490713163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14330643901590787975235101 5373991463096545490713163)
                ·
                  refine ⟨8060987194644818236069745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5373991463096545490713163 8060987194644818236069745)
                  ·
                    refine ⟨6045740395983613677052309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8060987194644818236069745 6045740395983613677052309)
                    ·
                      refine ⟨283394081061731891111827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6045740395983613677052309 283394081061731891111827)
                      ·
                        rfl

theorem cell23_551908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_551908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551908 prefixEnd_551908 := by exact prefixLift 551908
  have htrace : WordTrace (prefixWord ++ tailWord_551908) baseStart_551908 baseEnd_551908 := by
    simpa [prefixWord, tailWord_551908, baseEnd_551908] using wordTrace_append hprefix tailTrace_551908
  have hstable : (prefixWord ++ tailWord_551908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551908).length < 2 ^ (prefixWord ++ tailWord_551908).sum := by decide
  have hdescent : baseEnd_551908 < baseStart_551908 := by decide
  rcases family_descends (prefixWord ++ tailWord_551908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551959 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 2, 3, 2]
def baseStart_551959 : Nat := 118140960795 + 551959 * 2 ^ 59
def prefixEnd_551959 : Nat := 4983230072969 + 3 ^ 40 * 551959 * 2
def baseEnd_551959 : Nat := 283420268575111191574093

theorem tailTrace_551959 : CollatzResearch.WordTrace tailWord_551959 prefixEnd_551959 283420268575111191574093 := by
  unfold tailWord_551959
  simp only [CollatzResearch.WordTrace]
  refine ⟨20131598607354284937322931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13421065738236189958215287 20131598607354284937322931)
  ·
    refine ⟨30197397911031427405984397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20131598607354284937322931 30197397911031427405984397)
    ·
      refine ⟨11324024216636785277244149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30197397911031427405984397 11324024216636785277244149)
      ·
        refine ⟨1061627270309698619741639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11324024216636785277244149 1061627270309698619741639)
        ·
          refine ⟨1592440905464547929612459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061627270309698619741639 1592440905464547929612459)
          ·
            refine ⟨2388661358196821894418689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592440905464547929612459 2388661358196821894418689)
            ·
              refine ⟨1791496018647616420814017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388661358196821894418689 1791496018647616420814017)
              ·
                refine ⟨1343622013985712315610513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791496018647616420814017 1343622013985712315610513)
                ·
                  refine ⟨1007716510489284236707885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1343622013985712315610513 1007716510489284236707885)
                  ·
                    refine ⟨377893691433481588765457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1007716510489284236707885 377893691433481588765457)
                    ·
                      refine ⟨283420268575111191574093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 377893691433481588765457 283420268575111191574093)
                      ·
                        rfl

theorem cell23_551959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_551959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551959 prefixEnd_551959 := by exact prefixLift 551959
  have htrace : WordTrace (prefixWord ++ tailWord_551959) baseStart_551959 baseEnd_551959 := by
    simpa [prefixWord, tailWord_551959, baseEnd_551959] using wordTrace_append hprefix tailTrace_551959
  have hstable : (prefixWord ++ tailWord_551959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551959).length < 2 ^ (prefixWord ++ tailWord_551959).sum := by decide
  have hdescent : baseEnd_551959 < baseStart_551959 := by decide
  rcases family_descends (prefixWord ++ tailWord_551959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551972 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_551972 : Nat := 118140960795 + 551972 * 2 ^ 59
def prefixEnd_551972 : Nat := 4983230072969 + 3 ^ 40 * 551972 * 2
def baseEnd_551972 : Nat := 283426943823619640711533

theorem tailTrace_551972 : CollatzResearch.WordTrace tailWord_551972 prefixEnd_551972 283426943823619640711533 := by
  unfold tailWord_551972
  simp only [CollatzResearch.WordTrace]
  refine ⟨10066036378153594078773085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13421381837538125438364113 10066036378153594078773085)
  ·
    refine ⟨3774763641807597779539907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10066036378153594078773085 3774763641807597779539907)
    ·
      refine ⟨5662145462711396669309861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3774763641807597779539907 5662145462711396669309861)
      ·
        refine ⟨1061652274258386875495599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5662145462711396669309861 1061652274258386875495599)
        ·
          refine ⟨1592478411387580313243399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061652274258386875495599 1592478411387580313243399)
          ·
            refine ⟨2388717617081370469865099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592478411387580313243399 2388717617081370469865099)
            ·
              refine ⟨3583076425622055704797649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2388717617081370469865099 3583076425622055704797649)
              ·
                refine ⟨2687307319216541778598237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3583076425622055704797649 2687307319216541778598237)
                ·
                  refine ⟨1007740244706203166974339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2687307319216541778598237 1007740244706203166974339)
                  ·
                    refine ⟨1511610367059304750461509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1007740244706203166974339 1511610367059304750461509)
                    ·
                      refine ⟨283426943823619640711533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1511610367059304750461509 283426943823619640711533)
                      ·
                        rfl

theorem cell23_551972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_551972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551972 prefixEnd_551972 := by exact prefixLift 551972
  have htrace : WordTrace (prefixWord ++ tailWord_551972) baseStart_551972 baseEnd_551972 := by
    simpa [prefixWord, tailWord_551972, baseEnd_551972] using wordTrace_append hprefix tailTrace_551972
  have hstable : (prefixWord ++ tailWord_551972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551972).length < 2 ^ (prefixWord ++ tailWord_551972).sum := by decide
  have hdescent : baseEnd_551972 < baseStart_551972 := by decide
  rcases family_descends (prefixWord ++ tailWord_551972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551982 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_551982 : Nat := 118140960795 + 551982 * 2 ^ 59
def prefixEnd_551982 : Nat := 4983230072969 + 3 ^ 40 * 551982 * 2
def baseEnd_551982 : Nat := 94477359543388200528829

theorem tailTrace_551982 : CollatzResearch.WordTrace tailWord_551982 prefixEnd_551982 94477359543388200528829 := by
  unfold tailWord_551982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2516554685783869983176275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13421624990847306576940133 2516554685783869983176275)
  ·
    refine ⟨3774832028675804974764413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2516554685783869983176275 3774832028675804974764413)
    ·
      refine ⟨1415562010753426865536655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3774832028675804974764413 1415562010753426865536655)
      ·
        refine ⟨2123343016130140298304983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1415562010753426865536655 2123343016130140298304983)
        ·
          refine ⟨3185014524195210447457475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2123343016130140298304983 3185014524195210447457475)
          ·
            refine ⟨4777521786292815671186213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3185014524195210447457475 4777521786292815671186213)
            ·
              refine ⟨895785334929902938347415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4777521786292815671186213 895785334929902938347415)
              ·
                refine ⟨1343678002394854407521123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895785334929902938347415 1343678002394854407521123)
                ·
                  refine ⟨2015517003592281611281685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343678002394854407521123 2015517003592281611281685)
                  ·
                    refine ⟨94477359543388200528829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2015517003592281611281685 94477359543388200528829)
                    ·
                      rfl

theorem cell23_551982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_551982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551982 prefixEnd_551982 := by exact prefixLift 551982
  have htrace : WordTrace (prefixWord ++ tailWord_551982) baseStart_551982 baseEnd_551982 := by
    simpa [prefixWord, tailWord_551982, baseEnd_551982] using wordTrace_append hprefix tailTrace_551982
  have hstable : (prefixWord ++ tailWord_551982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551982).length < 2 ^ (prefixWord ++ tailWord_551982).sum := by decide
  have hdescent : baseEnd_551982 < baseStart_551982 := by decide
  rcases family_descends (prefixWord ++ tailWord_551982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551992 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 3, 2, 3]
def baseStart_551992 : Nat := 118140960795 + 551992 * 2 ^ 59
def prefixEnd_551992 : Nat := 4983230072969 + 3 ^ 40 * 551992 * 2
def baseEnd_551992 : Nat := 283437213436709562461441

theorem tailTrace_551992 : CollatzResearch.WordTrace tailWord_551992 prefixEnd_551992 283437213436709562461441 := by
  unfold tailWord_551992
  simp only [CollatzResearch.WordTrace]
  refine ⟨10066401108117365786637115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13421868144156487715516153 10066401108117365786637115)
  ·
    refine ⟨15099601662176048679955673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10066401108117365786637115 15099601662176048679955673)
    ·
      refine ⟨11324701246632036509966755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15099601662176048679955673 11324701246632036509966755)
      ·
        refine ⟨16987051869948054764950133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11324701246632036509966755 16987051869948054764950133)
        ·
          refine ⟨1592536112807630134214075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16987051869948054764950133 1592536112807630134214075)
          ·
            refine ⟨2388804169211445201321113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592536112807630134214075 2388804169211445201321113)
            ·
              refine ⟨1791603126908583900990835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388804169211445201321113 1791603126908583900990835)
              ·
                refine ⟨2687404690362875851486253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791603126908583900990835 2687404690362875851486253)
                ·
                  refine ⟨1007776758886078444307345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2687404690362875851486253 1007776758886078444307345)
                  ·
                    refine ⟨755832569164558833230509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1007776758886078444307345 755832569164558833230509)
                    ·
                      refine ⟨283437213436709562461441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 755832569164558833230509 283437213436709562461441)
                      ·
                        rfl

theorem cell23_551992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_551992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551992 prefixEnd_551992 := by exact prefixLift 551992
  have htrace : WordTrace (prefixWord ++ tailWord_551992) baseStart_551992 baseEnd_551992 := by
    simpa [prefixWord, tailWord_551992, baseEnd_551992] using wordTrace_append hprefix tailTrace_551992
  have hstable : (prefixWord ++ tailWord_551992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551992).length < 2 ^ (prefixWord ++ tailWord_551992).sum := by decide
  have hdescent : baseEnd_551992 < baseStart_551992 := by decide
  rcases family_descends (prefixWord ++ tailWord_551992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552006 : List Nat := [6, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_552006 : Nat := 118140960795 + 552006 * 2 ^ 59
def prefixEnd_552006 : Nat := 4983230072969 + 3 ^ 40 * 552006 * 2
def baseEnd_552006 : Nat := 283444402165872507686377

theorem tailTrace_552006 : CollatzResearch.WordTrace tailWord_552006 prefixEnd_552006 283444402165872507686377 := by
  unfold tailWord_552006
  simp only [CollatzResearch.WordTrace]
  refine ⟨629166026193250373883871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13422208558789341309522581 629166026193250373883871)
  ·
    refine ⟨943749039289875560825807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 629166026193250373883871 943749039289875560825807)
    ·
      refine ⟨1415623558934813341238711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 943749039289875560825807 1415623558934813341238711)
      ·
        refine ⟨2123435338402220011858067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1415623558934813341238711 2123435338402220011858067)
        ·
          refine ⟨3185153007603330017787101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2123435338402220011858067 3185153007603330017787101)
          ·
            refine ⟨1194432377851248756670163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3185153007603330017787101 1194432377851248756670163)
            ·
              refine ⟨1791648566776873135005245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194432377851248756670163 1791648566776873135005245)
              ·
                refine ⟨671868212541327425626967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1791648566776873135005245 671868212541327425626967)
                ·
                  refine ⟨1007802318811991138440451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 671868212541327425626967 1007802318811991138440451)
                  ·
                    refine ⟨1511703478217986707660677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1007802318811991138440451 1511703478217986707660677)
                    ·
                      refine ⟨283444402165872507686377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1511703478217986707660677 283444402165872507686377)
                      ·
                        rfl

theorem cell23_552006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_552006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552006 prefixEnd_552006 := by exact prefixLift 552006
  have htrace : WordTrace (prefixWord ++ tailWord_552006) baseStart_552006 baseEnd_552006 := by
    simpa [prefixWord, tailWord_552006, baseEnd_552006] using wordTrace_append hprefix tailTrace_552006
  have hstable : (prefixWord ++ tailWord_552006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552006).length < 2 ^ (prefixWord ++ tailWord_552006).sum := by decide
  have hdescent : baseEnd_552006 < baseStart_552006 := by decide
  rcases family_descends (prefixWord ++ tailWord_552006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552039 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_552039 : Nat := 118140960795 + 552039 * 2 ^ 59
def prefixEnd_552039 : Nat := 4983230072969 + 3 ^ 40 * 552039 * 2
def baseEnd_552039 : Nat := 283461347027470878573725

theorem tailTrace_552039 : CollatzResearch.WordTrace tailWord_552039 prefixEnd_552039 283461347027470878573725 := by
  unfold tailWord_552039
  simp only [CollatzResearch.WordTrace]
  refine ⟨20134516447064458600235171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13423010964709639066823447 20134516447064458600235171)
  ·
    refine ⟨30201774670596687900352757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20134516447064458600235171 30201774670596687900352757)
    ·
      refine ⟨2831416375368439490658071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30201774670596687900352757 2831416375368439490658071)
      ·
        refine ⟨4247124563052659235987107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2831416375368439490658071 4247124563052659235987107)
        ·
          refine ⟨6370686844578988853980661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4247124563052659235987107 6370686844578988853980661)
          ·
            refine ⟨597251891679280205060687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6370686844578988853980661 597251891679280205060687)
            ·
              refine ⟨895877837518920307591031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597251891679280205060687 895877837518920307591031)
              ·
                refine ⟨1343816756278380461386547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895877837518920307591031 1343816756278380461386547)
                ·
                  refine ⟨2015725134417570692079821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343816756278380461386547 2015725134417570692079821)
                  ·
                    refine ⟨755896925406589009529933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2015725134417570692079821 755896925406589009529933)
                    ·
                      refine ⟨283461347027470878573725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 755896925406589009529933 283461347027470878573725)
                      ·
                        rfl

theorem cell23_552039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_552039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552039 prefixEnd_552039 := by exact prefixLift 552039
  have htrace : WordTrace (prefixWord ++ tailWord_552039) baseStart_552039 baseEnd_552039 := by
    simpa [prefixWord, tailWord_552039, baseEnd_552039] using wordTrace_append hprefix tailTrace_552039
  have hstable : (prefixWord ++ tailWord_552039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552039).length < 2 ^ (prefixWord ++ tailWord_552039).sum := by decide
  have hdescent : baseEnd_552039 < baseStart_552039 := by decide
  rcases family_descends (prefixWord ++ tailWord_552039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552075 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 4]
def baseStart_552075 : Nat := 118140960795 + 552075 * 2 ^ 59
def prefixEnd_552075 : Nat := 4983230072969 + 3 ^ 40 * 552075 * 2
def baseEnd_552075 : Nat := 283479832331032737723559

theorem tailTrace_552075 : CollatzResearch.WordTrace tailWord_552075 prefixEnd_552075 283479832331032737723559 := by
  unfold tailWord_552075
  simp only [CollatzResearch.WordTrace]
  refine ⟨20135829474934036748545679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13423886316622691165697119 20135829474934036748545679)
  ·
    refine ⟨30203744212401055122818519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20135829474934036748545679 30203744212401055122818519)
    ·
      refine ⟨45305616318601582684227779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30203744212401055122818519 45305616318601582684227779)
      ·
        refine ⟨67958424477902374026341669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45305616318601582684227779 67958424477902374026341669)
        ·
          refine ⟨12742204589606695129939063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67958424477902374026341669 12742204589606695129939063)
          ·
            refine ⟨19113306884410042694908595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12742204589606695129939063 19113306884410042694908595)
            ·
              refine ⟨28669960326615064042362893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19113306884410042694908595 28669960326615064042362893)
              ·
                refine ⟨10751235122480649015886085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28669960326615064042362893 10751235122480649015886085)
                ·
                  refine ⟨2015856585465121690478641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10751235122480649015886085 2015856585465121690478641)
                  ·
                    refine ⟨1511892439098841267858981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2015856585465121690478641 1511892439098841267858981)
                    ·
                      refine ⟨283479832331032737723559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1511892439098841267858981 283479832331032737723559)
                      ·
                        rfl

theorem cell23_552075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 4].length) (baseStart_552075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552075 prefixEnd_552075 := by exact prefixLift 552075
  have htrace : WordTrace (prefixWord ++ tailWord_552075) baseStart_552075 baseEnd_552075 := by
    simpa [prefixWord, tailWord_552075, baseEnd_552075] using wordTrace_append hprefix tailTrace_552075
  have hstable : (prefixWord ++ tailWord_552075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552075).length < 2 ^ (prefixWord ++ tailWord_552075).sum := by decide
  have hdescent : baseEnd_552075 < baseStart_552075 := by decide
  rcases family_descends (prefixWord ++ tailWord_552075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552085 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 7]
def baseStart_552085 : Nat := 118140960795 + 552085 * 2 ^ 59
def prefixEnd_552085 : Nat := 4983230072969 + 3 ^ 40 * 552085 * 2
def baseEnd_552085 : Nat := 31498329681953077622057

theorem tailTrace_552085 : CollatzResearch.WordTrace tailWord_552085 prefixEnd_552085 31498329681953077622057 := by
  unfold tailWord_552085
  simp only [CollatzResearch.WordTrace]
  refine ⟨20136194204897808456409709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13424129469931872304273139 20136194204897808456409709)
  ·
    refine ⟨7551072826836678171153641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20136194204897808456409709 7551072826836678171153641)
    ·
      refine ⟨5663304620127508628365231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7551072826836678171153641 5663304620127508628365231)
      ·
        refine ⟨8494956930191262942547847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5663304620127508628365231 8494956930191262942547847)
        ·
          refine ⟨12742435395286894413821771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8494956930191262942547847 12742435395286894413821771)
          ·
            refine ⟨19113653092930341620732657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12742435395286894413821771 19113653092930341620732657)
            ·
              refine ⟨14335239819697756215549493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19113653092930341620732657 14335239819697756215549493)
              ·
                refine ⟨1343928733096664645207765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14335239819697756215549493 1343928733096664645207765)
                ·
                  refine ⟨31498329681953077622057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1343928733096664645207765 31498329681953077622057)
                  ·
                    rfl

theorem cell23_552085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_552085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552085 prefixEnd_552085 := by exact prefixLift 552085
  have htrace : WordTrace (prefixWord ++ tailWord_552085) baseStart_552085 baseEnd_552085 := by
    simpa [prefixWord, tailWord_552085, baseEnd_552085] using wordTrace_append hprefix tailTrace_552085
  have hstable : (prefixWord ++ tailWord_552085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552085).length < 2 ^ (prefixWord ++ tailWord_552085).sum := by decide
  have hdescent : baseEnd_552085 < baseStart_552085 := by decide
  rcases family_descends (prefixWord ++ tailWord_552085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552096 : List Nat := [2, 1, 1, 4, 2, 1, 3, 3, 2, 2, 2]
def baseStart_552096 : Nat := 118140960795 + 552096 * 2 ^ 59
def prefixEnd_552096 : Nat := 4983230072969 + 3 ^ 40 * 552096 * 2
def baseEnd_552096 : Nat := 283490615424777155560963

theorem tailTrace_552096 : CollatzResearch.WordTrace tailWord_552096 prefixEnd_552096 283490615424777155560963 := by
  unfold tailWord_552096
  simp only [CollatzResearch.WordTrace]
  refine ⟨10068297703928978667530071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13424396938571971556706761 10068297703928978667530071)
  ·
    refine ⟨15102446555893468001295107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10068297703928978667530071 15102446555893468001295107)
    ·
      refine ⟨22653669833840202001942661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15102446555893468001295107 22653669833840202001942661)
      ·
        refine ⟨4247563093845037875364249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22653669833840202001942661 4247563093845037875364249)
        ·
          refine ⟨3185672320383778406523187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4247563093845037875364249 3185672320383778406523187)
          ·
            refine ⟨4778508480575667609784781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3185672320383778406523187 4778508480575667609784781)
            ·
              refine ⟨1791940680215875353669293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4778508480575667609784781 1791940680215875353669293)
              ·
                refine ⟨671977755080953257625985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1791940680215875353669293 671977755080953257625985)
                ·
                  refine ⟨503983316310714943219489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 671977755080953257625985 503983316310714943219489)
                  ·
                    refine ⟨377987487233036207414617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 503983316310714943219489 377987487233036207414617)
                    ·
                      refine ⟨283490615424777155560963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 377987487233036207414617 283490615424777155560963)
                      ·
                        rfl

theorem cell23_552096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_552096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552096 prefixEnd_552096 := by exact prefixLift 552096
  have htrace : WordTrace (prefixWord ++ tailWord_552096) baseStart_552096 baseEnd_552096 := by
    simpa [prefixWord, tailWord_552096, baseEnd_552096] using wordTrace_append hprefix tailTrace_552096
  have hstable : (prefixWord ++ tailWord_552096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552096).length < 2 ^ (prefixWord ++ tailWord_552096).sum := by decide
  have hdescent : baseEnd_552096 < baseStart_552096 := by decide
  rcases family_descends (prefixWord ++ tailWord_552096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552115 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 1, 7]
def baseStart_552115 : Nat := 118140960795 + 552115 * 2 ^ 59
def prefixEnd_552115 : Nat := 4983230072969 + 3 ^ 40 * 552115 * 2
def baseEnd_552115 : Nat := 94500123852404193741125

theorem tailTrace_552115 : CollatzResearch.WordTrace tailWord_552115 prefixEnd_552115 94500123852404193741125 := by
  unfold tailWord_552115
  simp only [CollatzResearch.WordTrace]
  refine ⟨20137288394789123580001799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13424858929859415720001199 20137288394789123580001799)
  ·
    refine ⟨30205932592183685370002699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20137288394789123580001799 30205932592183685370002699)
    ·
      refine ⟨45308898888275528055004049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30205932592183685370002699 45308898888275528055004049)
      ·
        refine ⟨33981674166206646041253037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45308898888275528055004049 33981674166206646041253037)
        ·
          refine ⟨12743127812327492265469889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33981674166206646041253037 12743127812327492265469889)
          ·
            refine ⟨9557345859245619199102417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12743127812327492265469889 9557345859245619199102417)
            ·
              refine ⟨7168009394434214399326813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9557345859245619199102417 7168009394434214399326813)
              ·
                refine ⟨2688003522912830399747555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7168009394434214399326813 2688003522912830399747555)
                ·
                  refine ⟨4032005284369245599621333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2688003522912830399747555 4032005284369245599621333)
                  ·
                    refine ⟨94500123852404193741125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4032005284369245599621333 94500123852404193741125)
                    ·
                      rfl

theorem cell23_552115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 7].length) (baseStart_552115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552115 prefixEnd_552115 := by exact prefixLift 552115
  have htrace : WordTrace (prefixWord ++ tailWord_552115) baseStart_552115 baseEnd_552115 := by
    simpa [prefixWord, tailWord_552115, baseEnd_552115] using wordTrace_append hprefix tailTrace_552115
  have hstable : (prefixWord ++ tailWord_552115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552115).length < 2 ^ (prefixWord ++ tailWord_552115).sum := by decide
  have hdescent : baseEnd_552115 < baseStart_552115 := by decide
  rcases family_descends (prefixWord ++ tailWord_552115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552145 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 2, 8]
def baseStart_552145 : Nat := 118140960795 + 552145 * 2 ^ 59
def prefixEnd_552145 : Nat := 4983230072969 + 3 ^ 40 * 552145 * 2
def baseEnd_552145 : Nat := 94505258658949154616079

theorem tailTrace_552145 : CollatzResearch.WordTrace tailWord_552145 prefixEnd_552145 94505258658949154616079 := by
  unfold tailWord_552145
  simp only [CollatzResearch.WordTrace]
  refine ⟨20138382584680438703593889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13425588389786959135729259 20138382584680438703593889)
  ·
    refine ⟨15103786938510329027695417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20138382584680438703593889 15103786938510329027695417)
    ·
      refine ⟨11327840203882746770771563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15103786938510329027695417 11327840203882746770771563)
      ·
        refine ⟨16991760305824120156157345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11327840203882746770771563 16991760305824120156157345)
        ·
          refine ⟨12743820229368090117118009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16991760305824120156157345 12743820229368090117118009)
          ·
            refine ⟨9557865172026067587838507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12743820229368090117118009 9557865172026067587838507)
            ·
              refine ⟨14336797758039101381757761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9557865172026067587838507 14336797758039101381757761)
              ·
                refine ⟨10752598318529326036318321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14336797758039101381757761 10752598318529326036318321)
                ·
                  refine ⟨8064448738896994527238741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10752598318529326036318321 8064448738896994527238741)
                  ·
                    refine ⟨94505258658949154616079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8064448738896994527238741 94505258658949154616079)
                    ·
                      rfl

theorem cell23_552145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_552145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552145 prefixEnd_552145 := by exact prefixLift 552145
  have htrace : WordTrace (prefixWord ++ tailWord_552145) baseStart_552145 baseEnd_552145 := by
    simpa [prefixWord, tailWord_552145, baseEnd_552145] using wordTrace_append hprefix tailTrace_552145
  have hstable : (prefixWord ++ tailWord_552145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552145).length < 2 ^ (prefixWord ++ tailWord_552145).sum := by decide
  have hdescent : baseEnd_552145 < baseStart_552145 := by decide
  rcases family_descends (prefixWord ++ tailWord_552145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552155 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 5]
def baseStart_552155 : Nat := 118140960795 + 552155 * 2 ^ 59
def prefixEnd_552155 : Nat := 4983230072969 + 3 ^ 40 * 552155 * 2
def baseEnd_552155 : Nat := 283520910783392424723191

theorem tailTrace_552155 : CollatzResearch.WordTrace tailWord_552155 prefixEnd_552155 283520910783392424723191 := by
  unfold tailWord_552155
  simp only [CollatzResearch.WordTrace]
  refine ⟨20138747314644210411457919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13425831543096140274305279 20138747314644210411457919)
  ·
    refine ⟨30208120971966315617186879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20138747314644210411457919 30208120971966315617186879)
    ·
      refine ⟨45312181457949473425780319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30208120971966315617186879 45312181457949473425780319)
      ·
        refine ⟨67968272186924210138670479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45312181457949473425780319 67968272186924210138670479)
        ·
          refine ⟨101952408280386315208005719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67968272186924210138670479 101952408280386315208005719)
          ·
            refine ⟨152928612420579472812008579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101952408280386315208005719 152928612420579472812008579)
            ·
              refine ⟨229392918630869209218012869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152928612420579472812008579 229392918630869209218012869)
              ·
                refine ⟨43011172243287976728377413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229392918630869209218012869 43011172243287976728377413)
                ·
                  refine ⟨8064594795616495636570765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43011172243287976728377413 8064594795616495636570765)
                  ·
                    refine ⟨3024223048356185863714037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8064594795616495636570765 3024223048356185863714037)
                    ·
                      refine ⟨283520910783392424723191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3024223048356185863714037 283520910783392424723191)
                      ·
                        rfl

theorem cell23_552155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 5].length) (baseStart_552155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552155 prefixEnd_552155 := by exact prefixLift 552155
  have htrace : WordTrace (prefixWord ++ tailWord_552155) baseStart_552155 baseEnd_552155 := by
    simpa [prefixWord, tailWord_552155, baseEnd_552155] using wordTrace_append hprefix tailTrace_552155
  have hstable : (prefixWord ++ tailWord_552155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552155).length < 2 ^ (prefixWord ++ tailWord_552155).sum := by decide
  have hdescent : baseEnd_552155 < baseStart_552155 := by decide
  rcases family_descends (prefixWord ++ tailWord_552155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552196 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_552196 : Nat := 118140960795 + 552196 * 2 ^ 59
def prefixEnd_552196 : Nat := 4983230072969 + 3 ^ 40 * 552196 * 2
def baseEnd_552196 : Nat := 94513987830075588103501

theorem tailTrace_552196 : CollatzResearch.WordTrace tailWord_552196 prefixEnd_552196 94513987830075588103501 := by
  unfold tailWord_552196
  simp only [CollatzResearch.WordTrace]
  refine ⟨10070121353747837206850221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13426828471663782942466961 10070121353747837206850221)
  ·
    refine ⟨3776295507655438952568833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10070121353747837206850221 3776295507655438952568833)
    ·
      refine ⟨2832221630741579214426625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3776295507655438952568833 2832221630741579214426625)
      ·
        refine ⟨2124166223056184410819969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2832221630741579214426625 2124166223056184410819969)
        ·
          refine ⟨1593124667292138308114977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2124166223056184410819969 1593124667292138308114977)
          ·
            refine ⟨1194843500469103731086233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1593124667292138308114977 1194843500469103731086233)
            ·
              refine ⟨896132625351827798314675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1194843500469103731086233 896132625351827798314675)
              ·
                refine ⟨1344198938027741697472013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896132625351827798314675 1344198938027741697472013)
                ·
                  refine ⟨504074601760403136552005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1344198938027741697472013 504074601760403136552005)
                  ·
                    refine ⟨94513987830075588103501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 504074601760403136552005 94513987830075588103501)
                    ·
                      rfl

theorem cell23_552196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_552196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552196 prefixEnd_552196 := by exact prefixLift 552196
  have htrace : WordTrace (prefixWord ++ tailWord_552196) baseStart_552196 baseEnd_552196 := by
    simpa [prefixWord, tailWord_552196, baseEnd_552196] using wordTrace_append hprefix tailTrace_552196
  have hstable : (prefixWord ++ tailWord_552196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552196).length < 2 ^ (prefixWord ++ tailWord_552196).sum := by decide
  have hdescent : baseEnd_552196 < baseStart_552196 := by decide
  rcases family_descends (prefixWord ++ tailWord_552196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552209 : List Nat := [1, 2, 2, 1, 1, 4, 5, 1, 6]
def baseStart_552209 : Nat := 118140960795 + 552209 * 2 ^ 59
def prefixEnd_552209 : Nat := 4983230072969 + 3 ^ 40 * 552209 * 2
def baseEnd_552209 : Nat := 31505404304303912605327

theorem tailTrace_552209 : CollatzResearch.WordTrace tailWord_552209 prefixEnd_552209 31505404304303912605327 := by
  unfold tailWord_552209
  simp only [CollatzResearch.WordTrace]
  refine ⟨20140716856448577633923681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13427144570965718422615787 20140716856448577633923681)
  ·
    refine ⟨15105537642336433225442761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20140716856448577633923681 15105537642336433225442761)
    ·
      refine ⟨11329153231752324919082071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15105537642336433225442761 11329153231752324919082071)
      ·
        refine ⟨16993729847628487378623107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11329153231752324919082071 16993729847628487378623107)
        ·
          refine ⟨25490594771442731067934661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16993729847628487378623107 25490594771442731067934661)
          ·
            refine ⟨4779486519645512075237749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25490594771442731067934661 4779486519645512075237749)
            ·
              refine ⟨448076861216766757053539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4779486519645512075237749 448076861216766757053539)
              ·
                refine ⟨672115291825150135580309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448076861216766757053539 672115291825150135580309)
                ·
                  refine ⟨31505404304303912605327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 672115291825150135580309 31505404304303912605327)
                  ·
                    rfl

theorem cell23_552209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 6].length) (baseStart_552209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552209 prefixEnd_552209 := by exact prefixLift 552209
  have htrace : WordTrace (prefixWord ++ tailWord_552209) baseStart_552209 baseEnd_552209 := by
    simpa [prefixWord, tailWord_552209, baseEnd_552209] using wordTrace_append hprefix tailTrace_552209
  have hstable : (prefixWord ++ tailWord_552209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552209).length < 2 ^ (prefixWord ++ tailWord_552209).sum := by decide
  have hdescent : baseEnd_552209 < baseStart_552209 := by decide
  rcases family_descends (prefixWord ++ tailWord_552209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552272 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 6]
def baseStart_552272 : Nat := 118140960795 + 552272 * 2 ^ 59
def prefixEnd_552272 : Nat := 4983230072969 + 3 ^ 40 * 552272 * 2
def baseEnd_552272 : Nat := 283580988019968466960153

theorem tailTrace_552272 : CollatzResearch.WordTrace tailWord_552272 prefixEnd_552272 283580988019968466960153 := by
  unfold tailWord_552272
  simp only [CollatzResearch.WordTrace]
  refine ⟨10071507327610169696733535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13428676436813559595644713 10071507327610169696733535)
  ·
    refine ⟨15107260991415254545100303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10071507327610169696733535 15107260991415254545100303)
    ·
      refine ⟨22660891487122881817650455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15107260991415254545100303 22660891487122881817650455)
      ·
        refine ⟨33991337230684322726475683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22660891487122881817650455 33991337230684322726475683)
        ·
          refine ⟨50987005846026484089713525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33991337230684322726475683 50987005846026484089713525)
          ·
            refine ⟨4780031798064982883410643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50987005846026484089713525 4780031798064982883410643)
            ·
              refine ⟨7170047697097474325115965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4780031798064982883410643 7170047697097474325115965)
              ·
                refine ⟨2688767886411552871918487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7170047697097474325115965 2688767886411552871918487)
                ·
                  refine ⟨4033151829617329307877731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2688767886411552871918487 4033151829617329307877731)
                  ·
                    refine ⟨6049727744425993961816597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4033151829617329307877731 6049727744425993961816597)
                    ·
                      refine ⟨283580988019968466960153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6049727744425993961816597 283580988019968466960153)
                      ·
                        rfl

theorem cell23_552272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_552272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552272 prefixEnd_552272 := by exact prefixLift 552272
  have htrace : WordTrace (prefixWord ++ tailWord_552272) baseStart_552272 baseEnd_552272 := by
    simpa [prefixWord, tailWord_552272, baseEnd_552272] using wordTrace_append hprefix tailTrace_552272
  have hstable : (prefixWord ++ tailWord_552272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552272).length < 2 ^ (prefixWord ++ tailWord_552272).sum := by decide
  have hdescent : baseEnd_552272 < baseStart_552272 := by decide
  rcases family_descends (prefixWord ++ tailWord_552272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552282 : List Nat := [3, 1, 1, 2, 1, 2, 4, 9]
def baseStart_552282 : Nat := 118140960795 + 552282 * 2 ^ 59
def prefixEnd_552282 : Nat := 4983230072969 + 3 ^ 40 * 552282 * 2
def baseEnd_552282 : Nat := 10503189734315312142041

theorem tailTrace_552282 : CollatzResearch.WordTrace tailWord_552282 prefixEnd_552282 10503189734315312142041 := by
  unfold tailWord_552282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5035844846296027775332775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13428919590122740734220733 5035844846296027775332775)
  ·
    refine ⟨7553767269444041662999163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5035844846296027775332775 7553767269444041662999163)
    ·
      refine ⟨11330650904166062494498745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7553767269444041662999163 11330650904166062494498745)
      ·
        refine ⟨8497988178124546870874059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11330650904166062494498745 8497988178124546870874059)
        ·
          refine ⟨12746982267186820306311089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8497988178124546870874059 12746982267186820306311089)
          ·
            refine ⟨9560236700390115229733317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12746982267186820306311089 9560236700390115229733317)
            ·
              refine ⟨1792544381323146605574997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9560236700390115229733317 1792544381323146605574997)
              ·
                refine ⟨10503189734315312142041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1792544381323146605574997 10503189734315312142041)
                ·
                  rfl

theorem cell23_552282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 9].length) (baseStart_552282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552282 prefixEnd_552282 := by exact prefixLift 552282
  have htrace : WordTrace (prefixWord ++ tailWord_552282) baseStart_552282 baseEnd_552282 := by
    simpa [prefixWord, tailWord_552282, baseEnd_552282] using wordTrace_append hprefix tailTrace_552282
  have hstable : (prefixWord ++ tailWord_552282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552282).length < 2 ^ (prefixWord ++ tailWord_552282).sum := by decide
  have hdescent : baseEnd_552282 < baseStart_552282 := by decide
  rcases family_descends (prefixWord ++ tailWord_552282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552319 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 1, 9, 2]
def baseStart_552319 : Nat := 118140960795 + 552319 * 2 ^ 59
def prefixEnd_552319 : Nat := 4983230072969 + 3 ^ 40 * 552319 * 2
def baseEnd_552319 : Nat := 283605121610729783072437

theorem tailTrace_552319 : CollatzResearch.WordTrace tailWord_552319 prefixEnd_552319 283605121610729783072437 := by
  unfold tailWord_552319
  simp only [CollatzResearch.WordTrace]
  refine ⟨20144728886050066420428011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13429819257366710946952007 20144728886050066420428011)
  ·
    refine ⟨30217093329075099630642017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20144728886050066420428011 30217093329075099630642017)
    ·
      refine ⟨22662819996806324722981513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30217093329075099630642017 22662819996806324722981513)
      ·
        refine ⟨16997114997604743542236135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22662819996806324722981513 16997114997604743542236135)
        ·
          refine ⟨25495672496407115313354203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16997114997604743542236135 25495672496407115313354203)
          ·
            refine ⟨38243508744610672970031305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25495672496407115313354203 38243508744610672970031305)
            ·
              refine ⟨28682631558458004727523479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38243508744610672970031305 28682631558458004727523479)
              ·
                refine ⟨43023947337687007091285219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28682631558458004727523479 43023947337687007091285219)
                ·
                  refine ⟨64535921006530510636927829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43023947337687007091285219 64535921006530510636927829)
                  ·
                    refine ⟨378140162147639710763249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 64535921006530510636927829 378140162147639710763249)
                    ·
                      refine ⟨283605121610729783072437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 378140162147639710763249 283605121610729783072437)
                      ·
                        rfl

theorem cell23_552319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 9, 2].length) (baseStart_552319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552319 prefixEnd_552319 := by exact prefixLift 552319
  have htrace : WordTrace (prefixWord ++ tailWord_552319) baseStart_552319 baseEnd_552319 := by
    simpa [prefixWord, tailWord_552319, baseEnd_552319] using wordTrace_append hprefix tailTrace_552319
  have hstable : (prefixWord ++ tailWord_552319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552319).length < 2 ^ (prefixWord ++ tailWord_552319).sum := by decide
  have hdescent : baseEnd_552319 < baseStart_552319 := by decide
  rcases family_descends (prefixWord ++ tailWord_552319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552359 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 4, 6]
def baseStart_552359 : Nat := 118140960795 + 552359 * 2 ^ 59
def prefixEnd_552359 : Nat := 4983230072969 + 3 ^ 40 * 552359 * 2
def baseEnd_552359 : Nat := 94541886945636542190751

theorem tailTrace_552359 : CollatzResearch.WordTrace tailWord_552359 prefixEnd_552359 94541886945636542190751 := by
  unfold tailWord_552359
  simp only [CollatzResearch.WordTrace]
  refine ⟨20146187805905153251884131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13430791870603435501256087 20146187805905153251884131)
  ·
    refine ⟨30219281708857729877826197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20146187805905153251884131 30219281708857729877826197)
    ·
      refine ⟨1416528830102706088023103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30219281708857729877826197 1416528830102706088023103)
      ·
        refine ⟨2124793245154059132034655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1416528830102706088023103 2124793245154059132034655)
        ·
          refine ⟨3187189867731088698051983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2124793245154059132034655 3187189867731088698051983)
          ·
            refine ⟨4780784801596633047077975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3187189867731088698051983 4780784801596633047077975)
            ·
              refine ⟨7171177202394949570616963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4780784801596633047077975 7171177202394949570616963)
              ·
                refine ⟨10756765803592424355925445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7171177202394949570616963 10756765803592424355925445)
                ·
                  refine ⟨2016893588173579566736021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10756765803592424355925445 2016893588173579566736021)
                  ·
                    refine ⟨94541886945636542190751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2016893588173579566736021 94541886945636542190751)
                    ·
                      rfl

theorem cell23_552359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_552359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552359 prefixEnd_552359 := by exact prefixLift 552359
  have htrace : WordTrace (prefixWord ++ tailWord_552359) baseStart_552359 baseEnd_552359 := by
    simpa [prefixWord, tailWord_552359, baseEnd_552359] using wordTrace_append hprefix tailTrace_552359
  have hstable : (prefixWord ++ tailWord_552359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552359).length < 2 ^ (prefixWord ++ tailWord_552359).sum := by decide
  have hdescent : baseEnd_552359 < baseStart_552359 := by decide
  rcases family_descends (prefixWord ++ tailWord_552359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552360 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_552360 : Nat := 118140960795 + 552360 * 2 ^ 59
def prefixEnd_552360 : Nat := 4983230072969 + 3 ^ 40 * 552360 * 2
def baseEnd_552360 : Nat := 283626174317564122659749

theorem tailTrace_552360 : CollatzResearch.WordTrace tailWord_552360 prefixEnd_552360 283626174317564122659749 := by
  unfold tailWord_552360
  simp only [CollatzResearch.WordTrace]
  refine ⟨10073112139450765211335267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13430816185934353615113689 10073112139450765211335267)
  ·
    refine ⟨15109668209176147817002901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10073112139450765211335267 15109668209176147817002901)
    ·
      refine ⟨708265697305131928922011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15109668209176147817002901 708265697305131928922011)
      ·
        refine ⟨1062398545957697893383017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 708265697305131928922011 1062398545957697893383017)
        ·
          refine ⟨796798909468273420037263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1062398545957697893383017 796798909468273420037263)
          ·
            refine ⟨1195198364202410130055895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796798909468273420037263 1195198364202410130055895)
            ·
              refine ⟨1792797546303615195083843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195198364202410130055895 1792797546303615195083843)
              ·
                refine ⟨2689196319455422792625765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792797546303615195083843 2689196319455422792625765)
                ·
                  refine ⟨504224309897891773617331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2689196319455422792625765 504224309897891773617331)
                  ·
                    refine ⟨756336464846837660425997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 504224309897891773617331 756336464846837660425997)
                    ·
                      refine ⟨283626174317564122659749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 756336464846837660425997 283626174317564122659749)
                      ·
                        rfl

theorem cell23_552360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_552360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552360 prefixEnd_552360 := by exact prefixLift 552360
  have htrace : WordTrace (prefixWord ++ tailWord_552360) baseStart_552360 baseEnd_552360 := by
    simpa [prefixWord, tailWord_552360, baseEnd_552360] using wordTrace_append hprefix tailTrace_552360
  have hstable : (prefixWord ++ tailWord_552360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552360).length < 2 ^ (prefixWord ++ tailWord_552360).sum := by decide
  have hdescent : baseEnd_552360 < baseStart_552360 := by decide
  rcases family_descends (prefixWord ++ tailWord_552360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552383 : List Nat := [1, 1, 2, 2, 2, 1, 1, 7, 2, 2, 2]
def baseStart_552383 : Nat := 118140960795 + 552383 * 2 ^ 59
def prefixEnd_552383 : Nat := 4983230072969 + 3 ^ 40 * 552383 * 2
def baseEnd_552383 : Nat := 283637984372617532672143

theorem tailTrace_552383 : CollatzResearch.WordTrace tailWord_552383 prefixEnd_552383 283637984372617532672143 := by
  unfold tailWord_552383
  simp only [CollatzResearch.WordTrace]
  refine ⟨20147063157818205350757803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13431375438545470233838535 20147063157818205350757803)
  ·
    refine ⟨30220594736727308026136705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20147063157818205350757803 30220594736727308026136705)
    ·
      refine ⟨22665446052545481019602529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30220594736727308026136705 22665446052545481019602529)
      ·
        refine ⟨16999084539409110764701897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22665446052545481019602529 16999084539409110764701897)
        ·
          refine ⟨12749313404556833073526423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16999084539409110764701897 12749313404556833073526423)
          ·
            refine ⟨19123970106835249610289635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12749313404556833073526423 19123970106835249610289635)
            ·
              refine ⟨28685955160252874415434453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19123970106835249610289635 28685955160252874415434453)
              ·
                refine ⟨672327074068426744111745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28685955160252874415434453 672327074068426744111745)
                ·
                  refine ⟨504245305551320058083809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 672327074068426744111745 504245305551320058083809)
                  ·
                    refine ⟨378183979163490043562857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 504245305551320058083809 378183979163490043562857)
                    ·
                      refine ⟨283637984372617532672143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 378183979163490043562857 283637984372617532672143)
                      ·
                        rfl

theorem cell23_552383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 2, 2].length) (baseStart_552383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552383 prefixEnd_552383 := by exact prefixLift 552383
  have htrace : WordTrace (prefixWord ++ tailWord_552383) baseStart_552383 baseEnd_552383 := by
    simpa [prefixWord, tailWord_552383, baseEnd_552383] using wordTrace_append hprefix tailTrace_552383
  have hstable : (prefixWord ++ tailWord_552383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552383).length < 2 ^ (prefixWord ++ tailWord_552383).sum := by decide
  have hdescent : baseEnd_552383 < baseStart_552383 := by decide
  rcases family_descends (prefixWord ++ tailWord_552383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552399 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 3]
def baseStart_552399 : Nat := 118140960795 + 552399 * 2 ^ 59
def prefixEnd_552399 : Nat := 4983230072969 + 3 ^ 40 * 552399 * 2
def baseEnd_552399 : Nat := 283646200063089470072069

theorem tailTrace_552399 : CollatzResearch.WordTrace tailWord_552399 prefixEnd_552399 283646200063089470072069 := by
  unfold tailWord_552399
  simp only [CollatzResearch.WordTrace]
  refine ⟨20147646725760240083340251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13431764483840160055560167 20147646725760240083340251)
  ·
    refine ⟨30221470088640360125010377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20147646725760240083340251 30221470088640360125010377)
    ·
      refine ⟨22666102566480270093757783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30221470088640360125010377 22666102566480270093757783)
      ·
        refine ⟨33999153849720405140636675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22666102566480270093757783 33999153849720405140636675)
        ·
          refine ⟨50998730774580607710955013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33999153849720405140636675 50998730774580607710955013)
          ·
            refine ⟨9562262020233863945804065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50998730774580607710955013 9562262020233863945804065)
            ·
              refine ⟨7171696515175397959353049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9562262020233863945804065 7171696515175397959353049)
              ·
                refine ⟨5378772386381548469514787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7171696515175397959353049 5378772386381548469514787)
                ·
                  refine ⟨8068158579572322704272181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5378772386381548469514787 8068158579572322704272181)
                  ·
                    refine ⟨756389866834905253525517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8068158579572322704272181 756389866834905253525517)
                    ·
                      refine ⟨283646200063089470072069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 756389866834905253525517 283646200063089470072069)
                      ·
                        rfl

theorem cell23_552399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 3].length) (baseStart_552399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552399 prefixEnd_552399 := by exact prefixLift 552399
  have htrace : WordTrace (prefixWord ++ tailWord_552399) baseStart_552399 baseEnd_552399 := by
    simpa [prefixWord, tailWord_552399, baseEnd_552399] using wordTrace_append hprefix tailTrace_552399
  have hstable : (prefixWord ++ tailWord_552399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552399).length < 2 ^ (prefixWord ++ tailWord_552399).sum := by decide
  have hdescent : baseEnd_552399 < baseStart_552399 := by decide
  rcases family_descends (prefixWord ++ tailWord_552399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552434 : List Nat := [3, 2, 1, 4, 1, 3, 2, 1, 2, 2, 2]
def baseStart_552434 : Nat := 118140960795 + 552434 * 2 ^ 59
def prefixEnd_552434 : Nat := 4983230072969 + 3 ^ 40 * 552434 * 2
def baseEnd_552434 : Nat := 283664171885996833134409

theorem tailTrace_552434 : CollatzResearch.WordTrace tailWord_552434 prefixEnd_552434 283664171885996833134409 := by
  unfold tailWord_552434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5037230820158360265216089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13432615520422294040576237 5037230820158360265216089)
  ·
    refine ⟨3777923115118770198912067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5037230820158360265216089 3777923115118770198912067)
    ·
      refine ⟨5666884672678155298368101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3777923115118770198912067 5666884672678155298368101)
      ·
        refine ⟨1062540876127154118444019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5666884672678155298368101 1062540876127154118444019)
        ·
          refine ⟨1593811314190731177666029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062540876127154118444019 1593811314190731177666029)
          ·
            refine ⟨597679242821524191624761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1593811314190731177666029 597679242821524191624761)
            ·
              refine ⟨448259432116143143718571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597679242821524191624761 448259432116143143718571)
              ·
                refine ⟨672389148174214715577857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448259432116143143718571 672389148174214715577857)
                ·
                  refine ⟨504291861130661036683393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 672389148174214715577857 504291861130661036683393)
                  ·
                    refine ⟨378218895847995777512545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 504291861130661036683393 378218895847995777512545)
                    ·
                      refine ⟨283664171885996833134409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 378218895847995777512545 283664171885996833134409)
                      ·
                        rfl

theorem cell23_552434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_552434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552434 prefixEnd_552434 := by exact prefixLift 552434
  have htrace : WordTrace (prefixWord ++ tailWord_552434) baseStart_552434 baseEnd_552434 := by
    simpa [prefixWord, tailWord_552434, baseEnd_552434] using wordTrace_append hprefix tailTrace_552434
  have hstable : (prefixWord ++ tailWord_552434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552434).length < 2 ^ (prefixWord ++ tailWord_552434).sum := by decide
  have hdescent : baseEnd_552434 < baseStart_552434 := by decide
  rcases family_descends (prefixWord ++ tailWord_552434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552439 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_552439 : Nat := 118140960795 + 552439 * 2 ^ 59
def prefixEnd_552439 : Nat := 4983230072969 + 3 ^ 40 * 552439 * 2
def baseEnd_552439 : Nat := 283666739289269313571885

theorem tailTrace_552439 : CollatzResearch.WordTrace tailWord_552439 prefixEnd_552439 283666739289269313571885 := by
  unfold tailWord_552439
  simp only [CollatzResearch.WordTrace]
  refine ⟨20149105645615326914796371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13432737097076884609864247 20149105645615326914796371)
  ·
    refine ⟨30223658468422990372194557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20149105645615326914796371 30223658468422990372194557)
    ·
      refine ⟨11333871925658621389572959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30223658468422990372194557 11333871925658621389572959)
      ·
        refine ⟨17000807888487932084359439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11333871925658621389572959 17000807888487932084359439)
        ·
          refine ⟨25501211832731898126539159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17000807888487932084359439 25501211832731898126539159)
          ·
            refine ⟨38251817749097847189808739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25501211832731898126539159 38251817749097847189808739)
            ·
              refine ⟨57377726623646770784713109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38251817749097847189808739 57377726623646770784713109)
              ·
                refine ⟨2689580935483442380533427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57377726623646770784713109 2689580935483442380533427)
                ·
                  refine ⟨4034371403225163570800141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2689580935483442380533427 4034371403225163570800141)
                  ·
                    refine ⟨1512889276209436339050053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4034371403225163570800141 1512889276209436339050053)
                    ·
                      refine ⟨283666739289269313571885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1512889276209436339050053 283666739289269313571885)
                      ·
                        rfl

theorem cell23_552439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_552439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552439 prefixEnd_552439 := by exact prefixLift 552439
  have htrace : WordTrace (prefixWord ++ tailWord_552439) baseStart_552439 baseEnd_552439 := by
    simpa [prefixWord, tailWord_552439, baseEnd_552439] using wordTrace_append hprefix tailTrace_552439
  have hstable : (prefixWord ++ tailWord_552439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552439).length < 2 ^ (prefixWord ++ tailWord_552439).sum := by decide
  have hdescent : baseEnd_552439 < baseStart_552439 := by decide
  rcases family_descends (prefixWord ++ tailWord_552439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552456 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_552456 : Nat := 118140960795 + 552456 * 2 ^ 59
def prefixEnd_552456 : Nat := 4983230072969 + 3 ^ 40 * 552456 * 2
def baseEnd_552456 : Nat := 283675468460395747059307

theorem tailTrace_552456 : CollatzResearch.WordTrace tailWord_552456 prefixEnd_552456 283675468460395747059307 := by
  unfold tailWord_552456
  simp only [CollatzResearch.WordTrace]
  refine ⟨10074862843276869409082611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13433150457702492545443481 10074862843276869409082611)
  ·
    refine ⟨15112294264915304113623917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10074862843276869409082611 15112294264915304113623917)
    ·
      refine ⟨5667110349343239042608969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15112294264915304113623917 5667110349343239042608969)
      ·
        refine ⟨4250332762007429281956727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5667110349343239042608969 4250332762007429281956727)
        ·
          refine ⟨6375499143011143922935091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4250332762007429281956727 6375499143011143922935091)
          ·
            refine ⟨9563248714516715884402637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6375499143011143922935091 9563248714516715884402637)
            ·
              refine ⟨3586218267943768456650989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9563248714516715884402637 3586218267943768456650989)
              ·
                refine ⟨1344831850478913171244121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3586218267943768456650989 1344831850478913171244121)
                ·
                  refine ⟨1008623887859184878433091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1344831850478913171244121 1008623887859184878433091)
                  ·
                    refine ⟨1512935831788777317649637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1008623887859184878433091 1512935831788777317649637)
                    ·
                      refine ⟨283675468460395747059307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1512935831788777317649637 283675468460395747059307)
                      ·
                        rfl

theorem cell23_552456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_552456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552456 prefixEnd_552456 := by exact prefixLift 552456
  have htrace : WordTrace (prefixWord ++ tailWord_552456) baseStart_552456 baseEnd_552456 := by
    simpa [prefixWord, tailWord_552456, baseEnd_552456] using wordTrace_append hprefix tailTrace_552456
  have hstable : (prefixWord ++ tailWord_552456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552456).length < 2 ^ (prefixWord ++ tailWord_552456).sum := by decide
  have hdescent : baseEnd_552456 < baseStart_552456 := by decide
  rcases family_descends (prefixWord ++ tailWord_552456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552479 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 8]
def baseStart_552479 : Nat := 118140960795 + 552479 * 2 ^ 59
def prefixEnd_552479 : Nat := 4983230072969 + 3 ^ 40 * 552479 * 2
def baseEnd_552479 : Nat := 31520808723938795230189

theorem tailTrace_552479 : CollatzResearch.WordTrace tailWord_552479 prefixEnd_552479 31520808723938795230189 := by
  unfold tailWord_552479
  simp only [CollatzResearch.WordTrace]
  refine ⟨20150564565470413746252491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13433709710313609164168327 20150564565470413746252491)
  ·
    refine ⟨30225846848205620619378737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20150564565470413746252491 30225846848205620619378737)
    ·
      refine ⟨22669385136154215464534053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30225846848205620619378737 22669385136154215464534053)
      ·
        refine ⟨4250509713028915399600135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22669385136154215464534053 4250509713028915399600135)
        ·
          refine ⟨6375764569543373099400203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4250509713028915399600135 6375764569543373099400203)
          ·
            refine ⟨9563646854315059649100305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6375764569543373099400203 9563646854315059649100305)
            ·
              refine ⟨7172735140736294736825229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9563646854315059649100305 7172735140736294736825229)
              ·
                refine ⟨2689775677776110526309461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7172735140736294736825229 2689775677776110526309461)
                ·
                  refine ⟨31520808723938795230189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2689775677776110526309461 31520808723938795230189)
                  ·
                    rfl

theorem cell23_552479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 8].length) (baseStart_552479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552479 prefixEnd_552479 := by exact prefixLift 552479
  have htrace : WordTrace (prefixWord ++ tailWord_552479) baseStart_552479 baseEnd_552479 := by
    simpa [prefixWord, tailWord_552479, baseEnd_552479] using wordTrace_append hprefix tailTrace_552479
  have hstable : (prefixWord ++ tailWord_552479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552479).length < 2 ^ (prefixWord ++ tailWord_552479).sum := by decide
  have hdescent : baseEnd_552479 < baseStart_552479 := by decide
  rcases family_descends (prefixWord ++ tailWord_552479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552533 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 4, 3, 2]
def baseStart_552533 : Nat := 118140960795 + 552533 * 2 ^ 59
def prefixEnd_552533 : Nat := 4983230072969 + 3 ^ 40 * 552533 * 2
def baseEnd_552533 : Nat := 283715006470791945796453

theorem tailTrace_552533 : CollatzResearch.WordTrace tailWord_552533 prefixEnd_552533 283715006470791945796453 := by
  unfold tailWord_552533
  simp only [CollatzResearch.WordTrace]
  refine ⟨20152534107274780968718253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13435022738183187312478835 20152534107274780968718253)
  ·
    refine ⟨7557200290228042863269345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20152534107274780968718253 7557200290228042863269345)
    ·
      refine ⟨5667900217671032147452009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7557200290228042863269345 5667900217671032147452009)
      ·
        refine ⟨4250925163253274110589007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5667900217671032147452009 4250925163253274110589007)
        ·
          refine ⟨6376387744879911165883511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4250925163253274110589007 6376387744879911165883511)
          ·
            refine ⟨9564581617319866748825267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6376387744879911165883511 9564581617319866748825267)
            ·
              refine ⟨14346872425979800123237901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9564581617319866748825267 14346872425979800123237901)
              ·
                refine ⟨5380077159742425046214213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14346872425979800123237901 5380077159742425046214213)
                ·
                  refine ⟨1008764467451704696165165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5380077159742425046214213 1008764467451704696165165)
                  ·
                    refine ⟨378286675294389261061937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1008764467451704696165165 378286675294389261061937)
                    ·
                      refine ⟨283715006470791945796453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 378286675294389261061937 283715006470791945796453)
                      ·
                        rfl

theorem cell23_552533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_552533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552533 prefixEnd_552533 := by exact prefixLift 552533
  have htrace : WordTrace (prefixWord ++ tailWord_552533) baseStart_552533 baseEnd_552533 := by
    simpa [prefixWord, tailWord_552533, baseEnd_552533] using wordTrace_append hprefix tailTrace_552533
  have hstable : (prefixWord ++ tailWord_552533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552533).length < 2 ^ (prefixWord ++ tailWord_552533).sum := by decide
  have hdescent : baseEnd_552533 < baseStart_552533 := by decide
  rcases family_descends (prefixWord ++ tailWord_552533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552534 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_552534 : Nat := 118140960795 + 552534 * 2 ^ 59
def prefixEnd_552534 : Nat := 4983230072969 + 3 ^ 40 * 552534 * 2
def baseEnd_552534 : Nat := 94571839983815480627983

theorem tailTrace_552534 : CollatzResearch.WordTrace tailWord_552534 prefixEnd_552534 94571839983815480627983 := by
  unfold tailWord_552534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259535661266947383719041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13435047053514105426336437 1259535661266947383719041)
  ·
    refine ⟨944651745950210537789281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1259535661266947383719041 944651745950210537789281)
    ·
      refine ⟨708488809462657903341961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 944651745950210537789281 708488809462657903341961)
      ·
        refine ⟨531366607096993427506471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 708488809462657903341961 531366607096993427506471)
        ·
          refine ⟨797049910645490141259707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531366607096993427506471 797049910645490141259707)
          ·
            refine ⟨1195574865968235211889561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797049910645490141259707 1195574865968235211889561)
            ·
              refine ⟨896681149476176408917171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1195574865968235211889561 896681149476176408917171)
              ·
                refine ⟨1345021724214264613375757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896681149476176408917171 1345021724214264613375757)
                ·
                  refine ⟨504383146580349230015909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1345021724214264613375757 504383146580349230015909)
                  ·
                    refine ⟨94571839983815480627983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 504383146580349230015909 94571839983815480627983)
                    ·
                      rfl

theorem cell23_552534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_552534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552534 prefixEnd_552534 := by exact prefixLift 552534
  have htrace : WordTrace (prefixWord ++ tailWord_552534) baseStart_552534 baseEnd_552534 := by
    simpa [prefixWord, tailWord_552534, baseEnd_552534] using wordTrace_append hprefix tailTrace_552534
  have hstable : (prefixWord ++ tailWord_552534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552534).length < 2 ^ (prefixWord ++ tailWord_552534).sum := by decide
  have hdescent : baseEnd_552534 < baseStart_552534 := by decide
  rcases family_descends (prefixWord ++ tailWord_552534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552540 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_552540 : Nat := 118140960795 + 552540 * 2 ^ 59
def prefixEnd_552540 : Nat := 4983230072969 + 3 ^ 40 * 552540 * 2
def baseEnd_552540 : Nat := 283718600835373418408921

theorem tailTrace_552540 : CollatzResearch.WordTrace tailWord_552540 prefixEnd_552540 283718600835373418408921 := by
  unfold tailWord_552540
  simp only [CollatzResearch.WordTrace]
  refine ⟨10076394709124710582111537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13435192945499614109482049 10076394709124710582111537)
  ·
    refine ⟨7557296031843532936583653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10076394709124710582111537 7557296031843532936583653)
    ·
      refine ⟨1416993005970662425609435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7557296031843532936583653 1416993005970662425609435)
      ·
        refine ⟨2125489508955993638414153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1416993005970662425609435 2125489508955993638414153)
        ·
          refine ⟨1594117131716995228810615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2125489508955993638414153 1594117131716995228810615)
          ·
            refine ⟨2391175697575492843215923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594117131716995228810615 2391175697575492843215923)
            ·
              refine ⟨3586763546363239264823885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2391175697575492843215923 3586763546363239264823885)
              ·
                refine ⟨1345036329886214724308957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3586763546363239264823885 1345036329886214724308957)
                ·
                  refine ⟨504388623707330521615859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1345036329886214724308957 504388623707330521615859)
                  ·
                    refine ⟨756582935560995782423789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 504388623707330521615859 756582935560995782423789)
                    ·
                      refine ⟨283718600835373418408921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 756582935560995782423789 283718600835373418408921)
                      ·
                        rfl

theorem cell23_552540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_552540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552540 prefixEnd_552540 := by exact prefixLift 552540
  have htrace : WordTrace (prefixWord ++ tailWord_552540) baseStart_552540 baseEnd_552540 := by
    simpa [prefixWord, tailWord_552540, baseEnd_552540] using wordTrace_append hprefix tailTrace_552540
  have hstable : (prefixWord ++ tailWord_552540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552540).length < 2 ^ (prefixWord ++ tailWord_552540).sum := by decide
  have hdescent : baseEnd_552540 < baseStart_552540 := by decide
  rcases family_descends (prefixWord ++ tailWord_552540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552573 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_552573 : Nat := 118140960795 + 552573 * 2 ^ 59
def prefixEnd_552573 : Nat := 4983230072969 + 3 ^ 40 * 552573 * 2
def baseEnd_552573 : Nat := 94578515232323929765423

theorem tailTrace_552573 : CollatzResearch.WordTrace tailWord_552573 prefixEnd_552573 94578515232323929765423 := by
  unfold tailWord_552573
  simp only [CollatzResearch.WordTrace]
  refine ⟨20153993027129867800174373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13435995351419911866782915 20153993027129867800174373)
  ·
    refine ⟨3778873692586850212532695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20153993027129867800174373 3778873692586850212532695)
    ·
      refine ⟨5668310538880275318799043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3778873692586850212532695 5668310538880275318799043)
      ·
        refine ⟨8502465808320412978198565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5668310538880275318799043 8502465808320412978198565)
        ·
          refine ⟨1594212339060077433412231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8502465808320412978198565 1594212339060077433412231)
          ·
            refine ⟨2391318508590116150118347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594212339060077433412231 2391318508590116150118347)
            ·
              refine ⟨3586977762885174225177521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2391318508590116150118347 3586977762885174225177521)
              ·
                refine ⟨2690233322163880668883141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3586977762885174225177521 2690233322163880668883141)
                ·
                  refine ⟨504418747905727625415589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2690233322163880668883141 504418747905727625415589)
                  ·
                    refine ⟨94578515232323929765423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 504418747905727625415589 94578515232323929765423)
                    ·
                      rfl

theorem cell23_552573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_552573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552573 prefixEnd_552573 := by exact prefixLift 552573
  have htrace : WordTrace (prefixWord ++ tailWord_552573) baseStart_552573 baseEnd_552573 := by
    simpa [prefixWord, tailWord_552573, baseEnd_552573] using wordTrace_append hprefix tailTrace_552573
  have hstable : (prefixWord ++ tailWord_552573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552573).length < 2 ^ (prefixWord ++ tailWord_552573).sum := by decide
  have hdescent : baseEnd_552573 < baseStart_552573 := by decide
  rcases family_descends (prefixWord ++ tailWord_552573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552576 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 4]
def baseStart_552576 : Nat := 118140960795 + 552576 * 2 ^ 59
def prefixEnd_552576 : Nat := 4983230072969 + 3 ^ 40 * 552576 * 2
def baseEnd_552576 : Nat := 283737086138935277558755

theorem tailTrace_552576 : CollatzResearch.WordTrace tailWord_552576 prefixEnd_552576 283737086138935277558755 := by
  unfold tailWord_552576
  simp only [CollatzResearch.WordTrace]
  refine ⟨10077051223059499656266791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13436068297412666208355721 10077051223059499656266791)
  ·
    refine ⟨15115576834589249484400187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10077051223059499656266791 15115576834589249484400187)
    ·
      refine ⟨22673365251883874226600281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15115576834589249484400187 22673365251883874226600281)
      ·
        refine ⟨17005023938912905669950211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22673365251883874226600281 17005023938912905669950211)
        ·
          refine ⟨25507535908369358504925317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17005023938912905669950211 25507535908369358504925317)
          ·
            refine ⟨4782662982819254719673497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25507535908369358504925317 4782662982819254719673497)
            ·
              refine ⟨3586997237114441039755123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4782662982819254719673497 3586997237114441039755123)
              ·
                refine ⟨5380495855671661559632685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3586997237114441039755123 5380495855671661559632685)
                ·
                  refine ⟨2017685945876873084862257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5380495855671661559632685 2017685945876873084862257)
                  ·
                    refine ⟨1513264459407654813646693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2017685945876873084862257 1513264459407654813646693)
                    ·
                      refine ⟨283737086138935277558755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1513264459407654813646693 283737086138935277558755)
                      ·
                        rfl

theorem cell23_552576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_552576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552576 prefixEnd_552576 := by exact prefixLift 552576
  have htrace : WordTrace (prefixWord ++ tailWord_552576) baseStart_552576 baseEnd_552576 := by
    simpa [prefixWord, tailWord_552576, baseEnd_552576] using wordTrace_append hprefix tailTrace_552576
  have hstable : (prefixWord ++ tailWord_552576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552576).length < 2 ^ (prefixWord ++ tailWord_552576).sum := by decide
  have hdescent : baseEnd_552576 < baseStart_552576 := by decide
  rcases family_descends (prefixWord ++ tailWord_552576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552583 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_552583 : Nat := 118140960795 + 552583 * 2 ^ 59
def prefixEnd_552583 : Nat := 4983230072969 + 3 ^ 40 * 552583 * 2
def baseEnd_552583 : Nat := 283740680503516750171223

theorem tailTrace_552583 : CollatzResearch.WordTrace tailWord_552583 prefixEnd_552583 283740680503516750171223 := by
  unfold tailWord_552583
  simp only [CollatzResearch.WordTrace]
  refine ⟨20154357757093639508038403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13436238504729093005358935 20154357757093639508038403)
  ·
    refine ⟨30231536635640459262057605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20154357757093639508038403 30231536635640459262057605)
    ·
      refine ⟨5668413119182586111635801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30231536635640459262057605 5668413119182586111635801)
      ·
        refine ⟨4251309839386939583726851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5668413119182586111635801 4251309839386939583726851)
        ·
          refine ⟨6376964759080409375590277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4251309839386939583726851 6376964759080409375590277)
          ·
            refine ⟨1195680892327576757923177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6376964759080409375590277 1195680892327576757923177)
            ·
              refine ⟨896760669245682568442383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1195680892327576757923177 896760669245682568442383)
              ·
                refine ⟨1345141003868523852663575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896760669245682568442383 1345141003868523852663575)
                ·
                  refine ⟨2017711505802785778995363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1345141003868523852663575 2017711505802785778995363)
                  ·
                    refine ⟨3026567258704178668493045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2017711505802785778995363 3026567258704178668493045)
                    ·
                      refine ⟨283740680503516750171223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3026567258704178668493045 283740680503516750171223)
                      ·
                        rfl

theorem cell23_552583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_552583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552583 prefixEnd_552583 := by exact prefixLift 552583
  have htrace : WordTrace (prefixWord ++ tailWord_552583) baseStart_552583 baseEnd_552583 := by
    simpa [prefixWord, tailWord_552583, baseEnd_552583] using wordTrace_append hprefix tailTrace_552583
  have hstable : (prefixWord ++ tailWord_552583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552583).length < 2 ^ (prefixWord ++ tailWord_552583).sum := by decide
  have hdescent : baseEnd_552583 < baseStart_552583 := by decide
  rcases family_descends (prefixWord ++ tailWord_552583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552586 : List Nat := [3, 1, 2, 3, 2, 1, 11]
def baseStart_552586 : Nat := 118140960795 + 552586 * 2 ^ 59
def prefixEnd_552586 : Nat := 4983230072969 + 3 ^ 40 * 552586 * 2
def baseEnd_552586 : Nat := 3502990382042965906589

theorem tailTrace_552586 : CollatzResearch.WordTrace tailWord_552586 prefixEnd_552586 3502990382042965906589 := by
  unfold tailWord_552586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5038616794020692755099403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13436311450721847346931741 5038616794020692755099403)
  ·
    refine ⟨7557925191031039132649105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5038616794020692755099403 7557925191031039132649105)
    ·
      refine ⟨5668443893273279349486829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7557925191031039132649105 5668443893273279349486829)
      ·
        refine ⟨2125666459977479756057561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5668443893273279349486829 2125666459977479756057561)
        ·
          refine ⟨1594249844983109817043171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2125666459977479756057561 1594249844983109817043171)
          ·
            refine ⟨2391374767474664725564757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594249844983109817043171 2391374767474664725564757)
            ·
              refine ⟨3502990382042965906589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2391374767474664725564757 3502990382042965906589)
              ·
                rfl

theorem cell23_552586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 11].length) (baseStart_552586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552586 prefixEnd_552586 := by exact prefixLift 552586
  have htrace : WordTrace (prefixWord ++ tailWord_552586) baseStart_552586 baseEnd_552586 := by
    simpa [prefixWord, tailWord_552586, baseEnd_552586] using wordTrace_append hprefix tailTrace_552586
  have hstable : (prefixWord ++ tailWord_552586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552586).length < 2 ^ (prefixWord ++ tailWord_552586).sum := by decide
  have hdescent : baseEnd_552586 < baseStart_552586 := by decide
  rcases family_descends (prefixWord ++ tailWord_552586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552597 : List Nat := [1, 3, 2, 1, 1, 1, 1, 8, 1, 2, 2]
def baseStart_552597 : Nat := 118140960795 + 552597 * 2 ^ 59
def prefixEnd_552597 : Nat := 4983230072969 + 3 ^ 40 * 552597 * 2
def baseEnd_552597 : Nat := 283747869232679695396159

theorem tailTrace_552597 : CollatzResearch.WordTrace tailWord_552597 prefixEnd_552597 283747869232679695396159 := by
  unfold tailWord_552597
  simp only [CollatzResearch.WordTrace]
  refine ⟨20154868379042919899048045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13436578919361946599365363 20154868379042919899048045)
  ·
    refine ⟨7558075642141094962143017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20154868379042919899048045 7558075642141094962143017)
    ·
      refine ⟨5668556731605821221607263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7558075642141094962143017 5668556731605821221607263)
      ·
        refine ⟨8502835097408731832410895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5668556731605821221607263 8502835097408731832410895)
        ·
          refine ⟨12754252646113097748616343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8502835097408731832410895 12754252646113097748616343)
          ·
            refine ⟨19131378969169646622924515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12754252646113097748616343 19131378969169646622924515)
            ·
              refine ⟨28697068453754469934386773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19131378969169646622924515 28697068453754469934386773)
              ·
                refine ⟨336293770942435194543595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 28697068453754469934386773 336293770942435194543595)
                ·
                  refine ⟨504440656413652791815393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336293770942435194543595 504440656413652791815393)
                  ·
                    refine ⟨378330492310239593861545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 504440656413652791815393 378330492310239593861545)
                    ·
                      refine ⟨283747869232679695396159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 378330492310239593861545 283747869232679695396159)
                      ·
                        rfl

theorem cell23_552597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_552597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552597 prefixEnd_552597 := by exact prefixLift 552597
  have htrace : WordTrace (prefixWord ++ tailWord_552597) baseStart_552597 baseEnd_552597 := by
    simpa [prefixWord, tailWord_552597, baseEnd_552597] using wordTrace_append hprefix tailTrace_552597
  have hstable : (prefixWord ++ tailWord_552597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552597).length < 2 ^ (prefixWord ++ tailWord_552597).sum := by decide
  have hdescent : baseEnd_552597 < baseStart_552597 := by decide
  rcases family_descends (prefixWord ++ tailWord_552597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552607 : List Nat := [1, 1, 2, 7, 1, 1, 1, 3, 2, 4]
def baseStart_552607 : Nat := 118140960795 + 552607 * 2 ^ 59
def prefixEnd_552607 : Nat := 4983230072969 + 3 ^ 40 * 552607 * 2
def baseEnd_552607 : Nat := 94584334679741552090371

theorem tailTrace_552607 : CollatzResearch.WordTrace tailWord_552607 prefixEnd_552607 94584334679741552090371 := by
  unfold tailWord_552607
  simp only [CollatzResearch.WordTrace]
  refine ⟨20155233109006691606912075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13436822072671127737941383 20155233109006691606912075)
  ·
    refine ⟨30232849663510037410368113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20155233109006691606912075 30232849663510037410368113)
    ·
      refine ⟨22674637247632528057776085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30232849663510037410368113 22674637247632528057776085)
      ·
        refine ⟨531436810491387376354127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 22674637247632528057776085 531436810491387376354127)
        ·
          refine ⟨797155215737081064531191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531436810491387376354127 797155215737081064531191)
          ·
            refine ⟨1195732823605621596796787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797155215737081064531191 1195732823605621596796787)
            ·
              refine ⟨1793599235408432395195181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195732823605621596796787 1793599235408432395195181)
              ·
                refine ⟨672599713278162148198193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1793599235408432395195181 672599713278162148198193)
                ·
                  refine ⟨504449784958621611148645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 672599713278162148198193 504449784958621611148645)
                  ·
                    refine ⟨94584334679741552090371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 504449784958621611148645 94584334679741552090371)
                    ·
                      rfl

theorem cell23_552607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 4].length) (baseStart_552607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552607 prefixEnd_552607 := by exact prefixLift 552607
  have htrace : WordTrace (prefixWord ++ tailWord_552607) baseStart_552607 baseEnd_552607 := by
    simpa [prefixWord, tailWord_552607, baseEnd_552607] using wordTrace_append hprefix tailTrace_552607
  have hstable : (prefixWord ++ tailWord_552607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552607).length < 2 ^ (prefixWord ++ tailWord_552607).sum := by decide
  have hdescent : baseEnd_552607 < baseStart_552607 := by decide
  rcases family_descends (prefixWord ++ tailWord_552607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552626 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_552626 : Nat := 118140960795 + 552626 * 2 ^ 59
def prefixEnd_552626 : Nat := 4983230072969 + 3 ^ 40 * 552626 * 2
def baseEnd_552626 : Nat := 283762760171660081933525

theorem tailTrace_552626 : CollatzResearch.WordTrace tailWord_552626 prefixEnd_552626 283762760171660081933525 := by
  unfold tailWord_552626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5038981523984464462963433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13437284063958571901235821 5038981523984464462963433)
  ·
    refine ⟨3779236142988348347222575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5038981523984464462963433 3779236142988348347222575)
    ·
      refine ⟨5668854214482522520833863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3779236142988348347222575 5668854214482522520833863)
      ·
        refine ⟨8503281321723783781250795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5668854214482522520833863 8503281321723783781250795)
        ·
          refine ⟨12754921982585675671876193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8503281321723783781250795 12754921982585675671876193)
          ·
            refine ⟨9566191486939256753907145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12754921982585675671876193 9566191486939256753907145)
            ·
              refine ⟨7174643615204442565430359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9566191486939256753907145 7174643615204442565430359)
              ·
                refine ⟨10761965422806663848145539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7174643615204442565430359 10761965422806663848145539)
                ·
                  refine ⟨16142948134209995772218309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10761965422806663848145539 16142948134209995772218309)
                  ·
                    refine ⟨3026802775164374207290933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16142948134209995772218309 3026802775164374207290933)
                    ·
                      refine ⟨283762760171660081933525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3026802775164374207290933 283762760171660081933525)
                      ·
                        rfl

theorem cell23_552626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_552626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552626 prefixEnd_552626 := by exact prefixLift 552626
  have htrace : WordTrace (prefixWord ++ tailWord_552626) baseStart_552626 baseEnd_552626 := by
    simpa [prefixWord, tailWord_552626, baseEnd_552626] using wordTrace_append hprefix tailTrace_552626
  have hstable : (prefixWord ++ tailWord_552626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552626).length < 2 ^ (prefixWord ++ tailWord_552626).sum := by decide
  have hdescent : baseEnd_552626 < baseStart_552626 := by decide
  rcases family_descends (prefixWord ++ tailWord_552626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552642 : List Nat := [3, 5, 1, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_552642 : Nat := 118140960795 + 552642 * 2 ^ 59
def prefixEnd_552642 : Nat := 4983230072969 + 3 ^ 40 * 552642 * 2
def baseEnd_552642 : Nat := 283770975862132019333453

theorem tailTrace_552642 : CollatzResearch.WordTrace tailWord_552642 prefixEnd_552642 283770975862132019333453 := by
  unfold tailWord_552642
  simp only [CollatzResearch.WordTrace]
  refine ⟨5039127415969973146109045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13437673109253261722957453 5039127415969973146109045)
  ·
    refine ⟨472418195247184982447723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5039127415969973146109045 472418195247184982447723)
    ·
      refine ⟨708627292870777473671585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 472418195247184982447723 708627292870777473671585)
      ·
        refine ⟨531470469653083105253689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 708627292870777473671585 531470469653083105253689)
        ·
          refine ⟨398602852239812328940267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 531470469653083105253689 398602852239812328940267)
          ·
            refine ⟨597904278359718493410401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398602852239812328940267 597904278359718493410401)
            ·
              refine ⟨448428208769788870057801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597904278359718493410401 448428208769788870057801)
              ·
                refine ⟨336321156577341652543351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448428208769788870057801 336321156577341652543351)
                ·
                  refine ⟨504481734866012478815027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336321156577341652543351 504481734866012478815027)
                  ·
                    refine ⟨756722602299018718222541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 504481734866012478815027 756722602299018718222541)
                    ·
                      refine ⟨283770975862132019333453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 756722602299018718222541 283770975862132019333453)
                      ·
                        rfl

theorem cell23_552642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_552642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552642 prefixEnd_552642 := by exact prefixLift 552642
  have htrace : WordTrace (prefixWord ++ tailWord_552642) baseStart_552642 baseEnd_552642 := by
    simpa [prefixWord, tailWord_552642, baseEnd_552642] using wordTrace_append hprefix tailTrace_552642
  have hstable : (prefixWord ++ tailWord_552642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552642).length < 2 ^ (prefixWord ++ tailWord_552642).sum := by decide
  have hdescent : baseEnd_552642 < baseStart_552642 := by decide
  rcases family_descends (prefixWord ++ tailWord_552642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552656 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 5]
def baseStart_552656 : Nat := 118140960795 + 552656 * 2 ^ 59
def prefixEnd_552656 : Nat := 4983230072969 + 3 ^ 40 * 552656 * 2
def baseEnd_552656 : Nat := 283778164591294964558387

theorem tailTrace_552656 : CollatzResearch.WordTrace tailWord_552656 prefixEnd_552656 283778164591294964558387 := by
  unfold tailWord_552656
  simp only [CollatzResearch.WordTrace]
  refine ⟨10078510142914586487722911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13438013523886115316963881 10078510142914586487722911)
  ·
    refine ⟨15117765214371879731584367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10078510142914586487722911 15117765214371879731584367)
    ·
      refine ⟨22676647821557819597376551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15117765214371879731584367 22676647821557819597376551)
      ·
        refine ⟨34014971732336729396064827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22676647821557819597376551 34014971732336729396064827)
        ·
          refine ⟨51022457598505094094097241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34014971732336729396064827 51022457598505094094097241)
          ·
            refine ⟨38266843198878820570572931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51022457598505094094097241 38266843198878820570572931)
            ·
              refine ⟨57400264798318230855859397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38266843198878820570572931 57400264798318230855859397)
              ·
                refine ⟨10762549649684668285473637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57400264798318230855859397 10762549649684668285473637)
                ·
                  refine ⟨2017978059315875303526307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10762549649684668285473637 2017978059315875303526307)
                  ·
                    refine ⟨3026967088973812955289461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2017978059315875303526307 3026967088973812955289461)
                    ·
                      refine ⟨283778164591294964558387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3026967088973812955289461 283778164591294964558387)
                      ·
                        rfl

theorem cell23_552656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_552656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552656 prefixEnd_552656 := by exact prefixLift 552656
  have htrace : WordTrace (prefixWord ++ tailWord_552656) baseStart_552656 baseEnd_552656 := by
    simpa [prefixWord, tailWord_552656, baseEnd_552656] using wordTrace_append hprefix tailTrace_552656
  have hstable : (prefixWord ++ tailWord_552656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552656).length < 2 ^ (prefixWord ++ tailWord_552656).sum := by decide
  have hdescent : baseEnd_552656 < baseStart_552656 := by decide
  rcases family_descends (prefixWord ++ tailWord_552656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552703 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 3]
def baseStart_552703 : Nat := 118140960795 + 552703 * 2 ^ 59
def prefixEnd_552703 : Nat := 4983230072969 + 3 ^ 40 * 552703 * 2
def baseEnd_552703 : Nat := 283802298182056280670671

theorem tailTrace_552703 : CollatzResearch.WordTrace tailWord_552703 prefixEnd_552703 283802298182056280670671 := by
  unfold tailWord_552703
  simp only [CollatzResearch.WordTrace]
  refine ⟨20158734516658900002406763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13439156344439266668271175 20158734516658900002406763)
  ·
    refine ⟨30238101774988350003610145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20158734516658900002406763 30238101774988350003610145)
    ·
      refine ⟨22678576331241262502707609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30238101774988350003610145 22678576331241262502707609)
      ·
        refine ⟨17008932248430946877030707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22678576331241262502707609 17008932248430946877030707)
        ·
          refine ⟨25513398372646420315546061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17008932248430946877030707 25513398372646420315546061)
          ·
            refine ⟨9567524389742407618329773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25513398372646420315546061 9567524389742407618329773)
            ·
              refine ⟨3587821646153402856873665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9567524389742407618329773 3587821646153402856873665)
              ·
                refine ⟨2690866234615052142655249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3587821646153402856873665 2690866234615052142655249)
                ·
                  refine ⟨2018149675961289106991437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2690866234615052142655249 2018149675961289106991437)
                  ·
                    refine ⟨756806128485483415121789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2018149675961289106991437 756806128485483415121789)
                    ·
                      refine ⟨283802298182056280670671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 756806128485483415121789 283802298182056280670671)
                      ·
                        rfl

theorem cell23_552703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_552703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552703 prefixEnd_552703 := by exact prefixLift 552703
  have htrace : WordTrace (prefixWord ++ tailWord_552703) baseStart_552703 baseEnd_552703 := by
    simpa [prefixWord, tailWord_552703, baseEnd_552703] using wordTrace_append hprefix tailTrace_552703
  have hstable : (prefixWord ++ tailWord_552703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552703).length < 2 ^ (prefixWord ++ tailWord_552703).sum := by decide
  have hdescent : baseEnd_552703 < baseStart_552703 := by decide
  rcases family_descends (prefixWord ++ tailWord_552703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552760 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_552760 : Nat := 118140960795 + 552760 * 2 ^ 59
def prefixEnd_552760 : Nat := 4983230072969 + 3 ^ 40 * 552760 * 2
def baseEnd_552760 : Nat := 283831566579362557657909

theorem tailTrace_552760 : CollatzResearch.WordTrace tailWord_552760 prefixEnd_552760 283831566579362557657909 := by
  unfold tailWord_552760
  simp only [CollatzResearch.WordTrace]
  refine ⟨10080406738726199368615867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13440542318301599158154489 10080406738726199368615867)
  ·
    refine ⟨15120610108089299052923801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10080406738726199368615867 15120610108089299052923801)
    ·
      refine ⟨11340457581066974289692851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15120610108089299052923801 11340457581066974289692851)
      ·
        refine ⟨17010686371600461434539277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11340457581066974289692851 17010686371600461434539277)
        ·
          refine ⟨6379007389350173037952229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17010686371600461434539277 6379007389350173037952229)
          ·
            refine ⟨1196063885503157444616043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6379007389350173037952229 1196063885503157444616043)
            ·
              refine ⟨1794095828254736166924065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196063885503157444616043 1794095828254736166924065)
              ·
                refine ⟨1345571871191052125193049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794095828254736166924065 1345571871191052125193049)
                ·
                  refine ⟨1009178903393289093894787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1345571871191052125193049 1009178903393289093894787)
                  ·
                    refine ⟨1513768355089933640842181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1009178903393289093894787 1513768355089933640842181)
                    ·
                      refine ⟨283831566579362557657909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1513768355089933640842181 283831566579362557657909)
                      ·
                        rfl

theorem cell23_552760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_552760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552760 prefixEnd_552760 := by exact prefixLift 552760
  have htrace : WordTrace (prefixWord ++ tailWord_552760) baseStart_552760 baseEnd_552760 := by
    simpa [prefixWord, tailWord_552760, baseEnd_552760] using wordTrace_append hprefix tailTrace_552760
  have hstable : (prefixWord ++ tailWord_552760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552760).length < 2 ^ (prefixWord ++ tailWord_552760).sum := by decide
  have hdescent : baseEnd_552760 < baseStart_552760 := by decide
  rcases family_descends (prefixWord ++ tailWord_552760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552861 : List Nat := [1, 4, 2, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_552861 : Nat := 118140960795 + 552861 * 2 ^ 59
def prefixEnd_552861 : Nat := 4983230072969 + 3 ^ 40 * 552861 * 2
def baseEnd_552861 : Nat := 283883428125466662494945

theorem tailTrace_552861 : CollatzResearch.WordTrace tailWord_552861 prefixEnd_552861 283883428125466662494945 := by
  unfold tailWord_552861
  simp only [CollatzResearch.WordTrace]
  refine ⟨20164497250086492986658437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13442998166724328657772291 20164497250086492986658437)
  ·
    refine ⟨3780843234391217434998457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20164497250086492986658437 3780843234391217434998457)
    ·
      refine ⟨2835632425793413076248843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3780843234391217434998457 2835632425793413076248843)
      ·
        refine ⟨4253448638690119614373265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2835632425793413076248843 4253448638690119614373265)
        ·
          refine ⟨3190086479017589710779949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4253448638690119614373265 3190086479017589710779949)
          ·
            refine ⟨1196282429631596141542481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3190086479017589710779949 1196282429631596141542481)
            ·
              refine ⟨897211822223697106156861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1196282429631596141542481 897211822223697106156861)
              ·
                refine ⟨336454433333886414808823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 897211822223697106156861 336454433333886414808823)
                ·
                  refine ⟨504681650000829622213235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336454433333886414808823 504681650000829622213235)
                  ·
                    refine ⟨757022475001244433319853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 504681650000829622213235 757022475001244433319853)
                    ·
                      refine ⟨283883428125466662494945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 757022475001244433319853 283883428125466662494945)
                      ·
                        rfl

theorem cell23_552861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_552861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552861 prefixEnd_552861 := by exact prefixLift 552861
  have htrace : WordTrace (prefixWord ++ tailWord_552861) baseStart_552861 baseEnd_552861 := by
    simpa [prefixWord, tailWord_552861, baseEnd_552861] using wordTrace_append hprefix tailTrace_552861
  have hstable : (prefixWord ++ tailWord_552861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552861).length < 2 ^ (prefixWord ++ tailWord_552861).sum := by decide
  have hdescent : baseEnd_552861 < baseStart_552861 := by decide
  rcases family_descends (prefixWord ++ tailWord_552861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552867 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 7, 2, 2]
def baseStart_552867 : Nat := 118140960795 + 552867 * 2 ^ 59
def prefixEnd_552867 : Nat := 4983230072969 + 3 ^ 40 * 552867 * 2
def baseEnd_552867 : Nat := 283886509009393639019917

theorem tailTrace_552867 : CollatzResearch.WordTrace tailWord_552867 prefixEnd_552867 283886509009393639019917 := by
  unfold tailWord_552867
  simp only [CollatzResearch.WordTrace]
  refine ⟨20164716088064756011376855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13443144058709837340917903 20164716088064756011376855)
  ·
    refine ⟨30247074132097134017065283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20164716088064756011376855 30247074132097134017065283)
    ·
      refine ⟨45370611198145701025597925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30247074132097134017065283 45370611198145701025597925)
      ·
        refine ⟨8506989599652318942299611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45370611198145701025597925 8506989599652318942299611)
        ·
          refine ⟨12760484399478478413449417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8506989599652318942299611 12760484399478478413449417)
          ·
            refine ⟨9570363299608858810087063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12760484399478478413449417 9570363299608858810087063)
            ·
              refine ⟨14355544949413288215130595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9570363299608858810087063 14355544949413288215130595)
              ·
                refine ⟨21533317424119932322695893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14355544949413288215130595 21533317424119932322695893)
                ·
                  refine ⟨504687127127810913813185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 21533317424119932322695893 504687127127810913813185)
                  ·
                    refine ⟨378515345345858185359889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 504687127127810913813185 378515345345858185359889)
                    ·
                      refine ⟨283886509009393639019917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 378515345345858185359889 283886509009393639019917)
                      ·
                        rfl

theorem cell23_552867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_552867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552867 prefixEnd_552867 := by exact prefixLift 552867
  have htrace : WordTrace (prefixWord ++ tailWord_552867) baseStart_552867 baseEnd_552867 := by
    simpa [prefixWord, tailWord_552867, baseEnd_552867] using wordTrace_append hprefix tailTrace_552867
  have hstable : (prefixWord ++ tailWord_552867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552867).length < 2 ^ (prefixWord ++ tailWord_552867).sum := by decide
  have hdescent : baseEnd_552867 < baseStart_552867 := by decide
  rcases family_descends (prefixWord ++ tailWord_552867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552904 : List Nat := [2, 1, 3, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_552904 : Nat := 118140960795 + 552904 * 2 ^ 59
def prefixEnd_552904 : Nat := 4983230072969 + 3 ^ 40 * 552904 * 2
def baseEnd_552904 : Nat := 283905507793609994257247

theorem tailTrace_552904 : CollatzResearch.WordTrace tailWord_552904 prefixEnd_552904 283905507793609994257247 := by
  unfold tailWord_552904
  simp only [CollatzResearch.WordTrace]
  refine ⟨10083032794465355665236883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13444043725953807553649177 10083032794465355665236883)
  ·
    refine ⟨15124549191698033497855325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10083032794465355665236883 15124549191698033497855325)
    ·
      refine ⟨5671705946886762561695747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15124549191698033497855325 5671705946886762561695747)
      ·
        refine ⟨8507558920330143842543621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5671705946886762561695747 8507558920330143842543621)
        ·
          refine ⟨1595167297561901970476929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8507558920330143842543621 1595167297561901970476929)
          ·
            refine ⟨1196375473171426477857697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1595167297561901970476929 1196375473171426477857697)
            ·
              refine ⟨897281604878569858393273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1196375473171426477857697 897281604878569858393273)
              ·
                refine ⟨672961203658927393794955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 897281604878569858393273 672961203658927393794955)
                ·
                  refine ⟨1009441805488391090692433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 672961203658927393794955 1009441805488391090692433)
                  ·
                    refine ⟨757081354116293318019325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1009441805488391090692433 757081354116293318019325)
                    ·
                      refine ⟨283905507793609994257247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 757081354116293318019325 283905507793609994257247)
                      ·
                        rfl

theorem cell23_552904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_552904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552904 prefixEnd_552904 := by exact prefixLift 552904
  have htrace : WordTrace (prefixWord ++ tailWord_552904) baseStart_552904 baseEnd_552904 := by
    simpa [prefixWord, tailWord_552904, baseEnd_552904] using wordTrace_append hprefix tailTrace_552904
  have hstable : (prefixWord ++ tailWord_552904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552904).length < 2 ^ (prefixWord ++ tailWord_552904).sum := by decide
  have hdescent : baseEnd_552904 < baseStart_552904 := by decide
  rcases family_descends (prefixWord ++ tailWord_552904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552935 : List Nat := [1, 1, 5, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_552935 : Nat := 118140960795 + 552935 * 2 ^ 59
def prefixEnd_552935 : Nat := 4983230072969 + 3 ^ 40 * 552935 * 2
def baseEnd_552935 : Nat := 283921425693899372969605

theorem tailTrace_552935 : CollatzResearch.WordTrace tailWord_552935 prefixEnd_552935 283921425693899372969605 := by
  unfold tailWord_552935
  simp only [CollatzResearch.WordTrace]
  refine ⟨20167196251818403624852259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13444797501212269083234839 20167196251818403624852259)
  ·
    refine ⟨30250794377727605437278389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20167196251818403624852259 30250794377727605437278389)
    ·
      refine ⟨2836011972911963009744849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30250794377727605437278389 2836011972911963009744849)
      ·
        refine ⟨2127008979683972257308637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2836011972911963009744849 2127008979683972257308637)
        ·
          refine ⟨797628367381489596490739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2127008979683972257308637 797628367381489596490739)
          ·
            refine ⟨1196442551072234394736109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797628367381489596490739 1196442551072234394736109)
            ·
              refine ⟨448665956652087898026041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1196442551072234394736109 448665956652087898026041)
              ·
                refine ⟨336499467489065923519531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448665956652087898026041 336499467489065923519531)
                ·
                  refine ⟨504749201233598885279297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336499467489065923519531 504749201233598885279297)
                  ·
                    refine ⟨378561900925199163959473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 504749201233598885279297 378561900925199163959473)
                    ·
                      refine ⟨283921425693899372969605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 378561900925199163959473 283921425693899372969605)
                      ·
                        rfl

theorem cell23_552935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_552935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552935 prefixEnd_552935 := by exact prefixLift 552935
  have htrace : WordTrace (prefixWord ++ tailWord_552935) baseStart_552935 baseEnd_552935 := by
    simpa [prefixWord, tailWord_552935, baseEnd_552935] using wordTrace_append hprefix tailTrace_552935
  have hstable : (prefixWord ++ tailWord_552935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552935).length < 2 ^ (prefixWord ++ tailWord_552935).sum := by decide
  have hdescent : baseEnd_552935 < baseStart_552935 := by decide
  rcases family_descends (prefixWord ++ tailWord_552935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552960 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 3]
def baseStart_552960 : Nat := 118140960795 + 552960 * 2 ^ 59
def prefixEnd_552960 : Nat := 4983230072969 + 3 ^ 40 * 552960 * 2
def baseEnd_552960 : Nat := 283934262710261775156989

theorem tailTrace_552960 : CollatzResearch.WordTrace tailWord_552960 prefixEnd_552960 283934262710261775156989 := by
  unfold tailWord_552960
  simp only [CollatzResearch.WordTrace]
  refine ⟨10084054038363916447256167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13445405384485221929674889 10084054038363916447256167)
  ·
    refine ⟨15126081057545874670884251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10084054038363916447256167 15126081057545874670884251)
    ·
      refine ⟨22689121586318812006326377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15126081057545874670884251 22689121586318812006326377)
      ·
        refine ⟨17016841189739109004744783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22689121586318812006326377 17016841189739109004744783)
        ·
          refine ⟨25525261784608663507117175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17016841189739109004744783 25525261784608663507117175)
          ·
            refine ⟨38287892676912995260675763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25525261784608663507117175 38287892676912995260675763)
            ·
              refine ⟨57431839015369492891013645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38287892676912995260675763 57431839015369492891013645)
              ·
                refine ⟨21536939630763559834130117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57431839015369492891013645 21536939630763559834130117)
                ·
                  refine ⟨4038176180768167468899397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21536939630763559834130117 4038176180768167468899397)
                  ·
                    refine ⟨757158033894031400418637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4038176180768167468899397 757158033894031400418637)
                    ·
                      refine ⟨283934262710261775156989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 757158033894031400418637 283934262710261775156989)
                      ·
                        rfl

theorem cell23_552960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_552960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552960 prefixEnd_552960 := by exact prefixLift 552960
  have htrace : WordTrace (prefixWord ++ tailWord_552960) baseStart_552960 baseEnd_552960 := by
    simpa [prefixWord, tailWord_552960, baseEnd_552960] using wordTrace_append hprefix tailTrace_552960
  have hstable : (prefixWord ++ tailWord_552960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552960).length < 2 ^ (prefixWord ++ tailWord_552960).sum := by decide
  have hdescent : baseEnd_552960 < baseStart_552960 := by decide
  rcases family_descends (prefixWord ++ tailWord_552960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552974 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2]
def baseStart_552974 : Nat := 118140960795 + 552974 * 2 ^ 59
def prefixEnd_552974 : Nat := 4983230072969 + 3 ^ 40 * 552974 * 2
def baseEnd_552974 : Nat := 283941451439424720381925

theorem tailTrace_552974 : CollatzResearch.WordTrace tailWord_552974 prefixEnd_552974 283941451439424720381925 := by
  unfold tailWord_552974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2521077337334639160690247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13445745799118075523681317 2521077337334639160690247)
  ·
    refine ⟨3781616006001958741035371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2521077337334639160690247 3781616006001958741035371)
    ·
      refine ⟨5672424009002938111553057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3781616006001958741035371 5672424009002938111553057)
      ·
        refine ⟨4254318006752203583664793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5672424009002938111553057 4254318006752203583664793)
        ·
          refine ⟨3190738505064152687748595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4254318006752203583664793 3190738505064152687748595)
          ·
            refine ⟨4786107757596229031622893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3190738505064152687748595 4786107757596229031622893)
            ·
              refine ⟨1794790409098585886858585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4786107757596229031622893 1794790409098585886858585)
              ·
                refine ⟨1346092806823939415143939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794790409098585886858585 1346092806823939415143939)
                ·
                  refine ⟨2019139210235909122715909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346092806823939415143939 2019139210235909122715909)
                  ·
                    refine ⟨378588601919232960509233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2019139210235909122715909 378588601919232960509233)
                    ·
                      refine ⟨283941451439424720381925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 378588601919232960509233 283941451439424720381925)
                      ·
                        rfl

theorem cell23_552974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_552974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552974 prefixEnd_552974 := by exact prefixLift 552974
  have htrace : WordTrace (prefixWord ++ tailWord_552974) baseStart_552974 baseEnd_552974 := by
    simpa [prefixWord, tailWord_552974, baseEnd_552974] using wordTrace_append hprefix tailTrace_552974
  have hstable : (prefixWord ++ tailWord_552974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552974).length < 2 ^ (prefixWord ++ tailWord_552974).sum := by decide
  have hdescent : baseEnd_552974 < baseStart_552974 := by decide
  rcases family_descends (prefixWord ++ tailWord_552974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552991 : List Nat := [1, 1, 2, 4, 1, 2, 4, 2, 2, 2, 2]
def baseStart_552991 : Nat := 118140960795 + 552991 * 2 ^ 59
def prefixEnd_552991 : Nat := 4983230072969 + 3 ^ 40 * 552991 * 2
def baseEnd_552991 : Nat := 283950180610551153869347

theorem tailTrace_552991 : CollatzResearch.WordTrace tailWord_552991 prefixEnd_552991 283950180610551153869347 := by
  unfold tailWord_552991
  simp only [CollatzResearch.WordTrace]
  refine ⟨20169238739615525188890827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13446159159743683459260551 20169238739615525188890827)
  ·
    refine ⟨30253858109423287783336241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20169238739615525188890827 30253858109423287783336241)
    ·
      refine ⟨22690393582067465837502181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30253858109423287783336241 22690393582067465837502181)
      ·
        refine ⟨4254448796637649844531659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22690393582067465837502181 4254448796637649844531659)
        ·
          refine ⟨6381673194956474766797489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4254448796637649844531659 6381673194956474766797489)
          ·
            refine ⟨4786254896217356075098117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6381673194956474766797489 4786254896217356075098117)
            ·
              refine ⟨897422793040754264080897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4786254896217356075098117 897422793040754264080897)
              ·
                refine ⟨673067094780565698060673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 897422793040754264080897 673067094780565698060673)
                ·
                  refine ⟨504800321085424273545505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 673067094780565698060673 504800321085424273545505)
                  ·
                    refine ⟨378600240814068205159129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 504800321085424273545505 378600240814068205159129)
                    ·
                      refine ⟨283950180610551153869347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 378600240814068205159129 283950180610551153869347)
                      ·
                        rfl

theorem cell23_552991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_552991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_552991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_552991 prefixEnd_552991 := by exact prefixLift 552991
  have htrace : WordTrace (prefixWord ++ tailWord_552991) baseStart_552991 baseEnd_552991 := by
    simpa [prefixWord, tailWord_552991, baseEnd_552991] using wordTrace_append hprefix tailTrace_552991
  have hstable : (prefixWord ++ tailWord_552991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552991).length < 2 ^ (prefixWord ++ tailWord_552991).sum := by decide
  have hdescent : baseEnd_552991 < baseStart_552991 := by decide
  rcases family_descends (prefixWord ++ tailWord_552991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553047 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_553047 : Nat := 118140960795 + 553047 * 2 ^ 59
def prefixEnd_553047 : Nat := 4983230072969 + 3 ^ 40 * 553047 * 2
def baseEnd_553047 : Nat := 283978935527202934769089

theorem tailTrace_553047 : CollatzResearch.WordTrace tailWord_553047 prefixEnd_553047 283978935527202934769089 := by
  unfold tailWord_553047
  simp only [CollatzResearch.WordTrace]
  refine ⟨20171281227412646752929395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13447520818275097835286263 20171281227412646752929395)
  ·
    refine ⟨30256921841118970129394093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20171281227412646752929395 30256921841118970129394093)
    ·
      refine ⟨11346345690419613798522785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30256921841118970129394093 11346345690419613798522785)
      ·
        refine ⟨8509759267814710348892089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11346345690419613798522785 8509759267814710348892089)
        ·
          refine ⟨6382319450861032761669067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8509759267814710348892089 6382319450861032761669067)
          ·
            refine ⟨9573479176291549142503601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6382319450861032761669067 9573479176291549142503601)
            ·
              refine ⟨7180109382218661856877701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9573479176291549142503601 7180109382218661856877701)
              ·
                refine ⟨1346270509165999098164569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7180109382218661856877701 1346270509165999098164569)
                ·
                  refine ⟨1009702881874499323623427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1346270509165999098164569 1009702881874499323623427)
                  ·
                    refine ⟨1514554322811748985435141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1009702881874499323623427 1514554322811748985435141)
                    ·
                      refine ⟨283978935527202934769089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1514554322811748985435141 283978935527202934769089)
                      ·
                        rfl

theorem cell23_553047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_553047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553047 prefixEnd_553047 := by exact prefixLift 553047
  have htrace : WordTrace (prefixWord ++ tailWord_553047) baseStart_553047 baseEnd_553047 := by
    simpa [prefixWord, tailWord_553047, baseEnd_553047] using wordTrace_append hprefix tailTrace_553047
  have hstable : (prefixWord ++ tailWord_553047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553047).length < 2 ^ (prefixWord ++ tailWord_553047).sum := by decide
  have hdescent : baseEnd_553047 < baseStart_553047 := by decide
  rcases family_descends (prefixWord ++ tailWord_553047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553074 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_553074 : Nat := 118140960795 + 553074 * 2 ^ 59
def prefixEnd_553074 : Nat := 4983230072969 + 3 ^ 40 * 553074 * 2
def baseEnd_553074 : Nat := 94664266501624776377155

theorem tailTrace_553074 : CollatzResearch.WordTrace tailWord_553074 prefixEnd_553074 94664266501624776377155 := by
  unfold tailWord_553074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5043066499578707591040569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13448177332209886909441517 5043066499578707591040569)
  ·
    refine ⟨3782299874684030693280427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5043066499578707591040569 3782299874684030693280427)
    ·
      refine ⟨5673449812026046039920641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3782299874684030693280427 5673449812026046039920641)
      ·
        refine ⟨4255087359019534529940481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5673449812026046039920641 4255087359019534529940481)
        ·
          refine ⟨3191315519264650897455361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4255087359019534529940481 3191315519264650897455361)
          ·
            refine ⟨2393486639448488173091521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3191315519264650897455361 2393486639448488173091521)
            ·
              refine ⟨1795114979586366129818641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2393486639448488173091521 1795114979586366129818641)
              ·
                refine ⟨1346336234689774597363981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1795114979586366129818641 1346336234689774597363981)
                ·
                  refine ⟨504876088008665474011493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1346336234689774597363981 504876088008665474011493)
                  ·
                    refine ⟨94664266501624776377155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 504876088008665474011493 94664266501624776377155)
                    ·
                      rfl

theorem cell23_553074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_553074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553074 prefixEnd_553074 := by exact prefixLift 553074
  have htrace : WordTrace (prefixWord ++ tailWord_553074) baseStart_553074 baseEnd_553074 := by
    simpa [prefixWord, tailWord_553074, baseEnd_553074] using wordTrace_append hprefix tailTrace_553074
  have hstable : (prefixWord ++ tailWord_553074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553074).length < 2 ^ (prefixWord ++ tailWord_553074).sum := by decide
  have hdescent : baseEnd_553074 < baseStart_553074 := by decide
  rcases family_descends (prefixWord ++ tailWord_553074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553091 : List Nat := [1, 1, 1, 3, 3, 3, 3, 3, 1, 4]
def baseStart_553091 : Nat := 118140960795 + 553091 * 2 ^ 59
def prefixEnd_553091 : Nat := 4983230072969 + 3 ^ 40 * 553091 * 2
def baseEnd_553091 : Nat := 94667176225333587539629

theorem tailTrace_553091 : CollatzResearch.WordTrace tailWord_553091 prefixEnd_553091 94667176225333587539629 := by
  unfold tailWord_553091
  simp only [CollatzResearch.WordTrace]
  refine ⟨20172886039253242267531127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13448590692835494845020751 20172886039253242267531127)
  ·
    refine ⟨30259329058879863401296691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20172886039253242267531127 30259329058879863401296691)
    ·
      refine ⟨45388993588319795101945037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30259329058879863401296691 45388993588319795101945037)
      ·
        refine ⟨17020872595619923163229389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45388993588319795101945037 17020872595619923163229389)
        ·
          refine ⟨6382827223357471186211021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17020872595619923163229389 6382827223357471186211021)
          ·
            refine ⟨2393560208759051694829133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6382827223357471186211021 2393560208759051694829133)
            ·
              refine ⟨897585078284644385560925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2393560208759051694829133 897585078284644385560925)
              ·
                refine ⟨336594404356741644585347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 897585078284644385560925 336594404356741644585347)
                ·
                  refine ⟨504891606535112466878021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336594404356741644585347 504891606535112466878021)
                  ·
                    refine ⟨94667176225333587539629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 504891606535112466878021 94667176225333587539629)
                    ·
                      rfl

theorem cell23_553091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 1, 4].length) (baseStart_553091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553091 prefixEnd_553091 := by exact prefixLift 553091
  have htrace : WordTrace (prefixWord ++ tailWord_553091) baseStart_553091 baseEnd_553091 := by
    simpa [prefixWord, tailWord_553091, baseEnd_553091] using wordTrace_append hprefix tailTrace_553091
  have hstable : (prefixWord ++ tailWord_553091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553091).length < 2 ^ (prefixWord ++ tailWord_553091).sum := by decide
  have hdescent : baseEnd_553091 < baseStart_553091 := by decide
  rcases family_descends (prefixWord ++ tailWord_553091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553121 : List Nat := [1, 2, 3, 3, 1, 4, 2, 1, 6]
def baseStart_553121 : Nat := 118140960795 + 553121 * 2 ^ 59
def prefixEnd_553121 : Nat := 4983230072969 + 3 ^ 40 * 553121 * 2
def baseEnd_553121 : Nat := 31557437010626182804861

theorem tailTrace_553121 : CollatzResearch.WordTrace tailWord_553121 prefixEnd_553121 31557437010626182804861 := by
  unfold tailWord_553121
  simp only [CollatzResearch.WordTrace]
  refine ⟨20173980229144557391123217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13449320152763038260748811 20173980229144557391123217)
  ·
    refine ⟨15130485171858418043342413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20173980229144557391123217 15130485171858418043342413)
    ·
      refine ⟨5673931939446906766253405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15130485171858418043342413 5673931939446906766253405)
      ·
        refine ⟨2127724477292590037345027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5673931939446906766253405 2127724477292590037345027)
        ·
          refine ⟨3191586715938885056017541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2127724477292590037345027 3191586715938885056017541)
          ·
            refine ⟨598422509238540948003289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3191586715938885056017541 598422509238540948003289)
            ·
              refine ⟨448816881928905711002467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598422509238540948003289 448816881928905711002467)
              ·
                refine ⟨673225322893358566503701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448816881928905711002467 673225322893358566503701)
                ·
                  refine ⟨31557437010626182804861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 673225322893358566503701 31557437010626182804861)
                  ·
                    rfl

theorem cell23_553121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 6].length) (baseStart_553121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553121 prefixEnd_553121 := by exact prefixLift 553121
  have htrace : WordTrace (prefixWord ++ tailWord_553121) baseStart_553121 baseEnd_553121 := by
    simpa [prefixWord, tailWord_553121, baseEnd_553121] using wordTrace_append hprefix tailTrace_553121
  have hstable : (prefixWord ++ tailWord_553121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553121).length < 2 ^ (prefixWord ++ tailWord_553121).sum := by decide
  have hdescent : baseEnd_553121 < baseStart_553121 := by decide
  rcases family_descends (prefixWord ++ tailWord_553121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553147 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 1, 6]
def baseStart_553147 : Nat := 118140960795 + 553147 * 2 ^ 59
def prefixEnd_553147 : Nat := 4983230072969 + 3 ^ 40 * 553147 * 2
def baseEnd_553147 : Nat := 94676761197550847839543

theorem tailTrace_553147 : CollatzResearch.WordTrace tailWord_553147 prefixEnd_553147 94676761197550847839543 := by
  unfold tailWord_553147
  simp only [CollatzResearch.WordTrace]
  refine ⟨20174928527050363831569695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13449952351366909221046463 20174928527050363831569695)
  ·
    refine ⟨30262392790575545747354543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20174928527050363831569695 30262392790575545747354543)
    ·
      refine ⟨45393589185863318621031815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30262392790575545747354543 45393589185863318621031815)
      ·
        refine ⟨68090383778794977931547723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45393589185863318621031815 68090383778794977931547723)
        ·
          refine ⟨102135575668192466897321585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68090383778794977931547723 102135575668192466897321585)
          ·
            refine ⟨76601681751144350172991189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102135575668192466897321585 76601681751144350172991189)
            ·
              refine ⟨1795351916042445707179481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 76601681751144350172991189 1795351916042445707179481)
              ·
                refine ⟨1346513937031834280384611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1795351916042445707179481 1346513937031834280384611)
                ·
                  refine ⟨2019770905547751420576917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346513937031834280384611 2019770905547751420576917)
                  ·
                    refine ⟨94676761197550847839543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2019770905547751420576917 94676761197550847839543)
                    ·
                      rfl

theorem cell23_553147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 6].length) (baseStart_553147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553147 prefixEnd_553147 := by exact prefixLift 553147
  have htrace : WordTrace (prefixWord ++ tailWord_553147) baseStart_553147 baseEnd_553147 := by
    simpa [prefixWord, tailWord_553147, baseEnd_553147] using wordTrace_append hprefix tailTrace_553147
  have hstable : (prefixWord ++ tailWord_553147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553147).length < 2 ^ (prefixWord ++ tailWord_553147).sum := by decide
  have hdescent : baseEnd_553147 < baseStart_553147 := by decide
  rcases family_descends (prefixWord ++ tailWord_553147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553167 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 4]
def baseStart_553167 : Nat := 118140960795 + 553167 * 2 ^ 59
def prefixEnd_553167 : Nat := 4983230072969 + 3 ^ 40 * 553167 * 2
def baseEnd_553167 : Nat := 284040553205742465268537

theorem tailTrace_553167 : CollatzResearch.WordTrace tailWord_553167 prefixEnd_553167 284040553205742465268537 := by
  unfold tailWord_553167
  simp only [CollatzResearch.WordTrace]
  refine ⟨20175657986977907247297755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13450438657985271498198503 20175657986977907247297755)
  ·
    refine ⟨30263486980466860870946633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20175657986977907247297755 30263486980466860870946633)
    ·
      refine ⟨22697615235350145653209975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30263486980466860870946633 22697615235350145653209975)
      ·
        refine ⟨34046422853025218479814963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22697615235350145653209975 34046422853025218479814963)
        ·
          refine ⟨51069634279537827719722445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34046422853025218479814963 51069634279537827719722445)
          ·
            refine ⟨19151112854826685394895917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51069634279537827719722445 19151112854826685394895917)
            ·
              refine ⟨7181667320560007023085969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19151112854826685394895917 7181667320560007023085969)
              ·
                refine ⟨5386250490420005267314477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7181667320560007023085969 5386250490420005267314477)
                ·
                  refine ⟨2019843933907501975242929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5386250490420005267314477 2019843933907501975242929)
                  ·
                    refine ⟨1514882950430626481432197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2019843933907501975242929 1514882950430626481432197)
                    ·
                      refine ⟨284040553205742465268537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1514882950430626481432197 284040553205742465268537)
                      ·
                        rfl

theorem cell23_553167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_553167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553167 prefixEnd_553167 := by exact prefixLift 553167
  have htrace : WordTrace (prefixWord ++ tailWord_553167) baseStart_553167 baseEnd_553167 := by
    simpa [prefixWord, tailWord_553167, baseEnd_553167] using wordTrace_append hprefix tailTrace_553167
  have hstable : (prefixWord ++ tailWord_553167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553167).length < 2 ^ (prefixWord ++ tailWord_553167).sum := by decide
  have hdescent : baseEnd_553167 < baseStart_553167 := by decide
  rcases family_descends (prefixWord ++ tailWord_553167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553177 : List Nat := [1, 2, 1, 2, 3, 1, 5, 8]
def baseStart_553177 : Nat := 118140960795 + 553177 * 2 ^ 59
def prefixEnd_553177 : Nat := 4983230072969 + 3 ^ 40 * 553177 * 2
def baseEnd_553177 : Nat := 10520210667121756523833

theorem tailTrace_553177 : CollatzResearch.WordTrace tailWord_553177 prefixEnd_553177 10520210667121756523833 := by
  unfold tailWord_553177
  simp only [CollatzResearch.WordTrace]
  refine ⟨20176022716941678955161785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13450681811294452636774523 20176022716941678955161785)
  ·
    refine ⟨15132017037706259216371339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20176022716941678955161785 15132017037706259216371339)
    ·
      refine ⟨22698025556559388824557009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15132017037706259216371339 22698025556559388824557009)
      ·
        refine ⟨17023519167419541618417757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22698025556559388824557009 17023519167419541618417757)
        ·
          refine ⟨6383819687782328106906659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17023519167419541618417757 6383819687782328106906659)
          ·
            refine ⟨9575729531673492160359989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6383819687782328106906659 9575729531673492160359989)
            ·
              refine ⟨897724643594389890033749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9575729531673492160359989 897724643594389890033749)
              ·
                refine ⟨10520210667121756523833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 897724643594389890033749 10520210667121756523833)
                ·
                  rfl

theorem cell23_553177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 8].length) (baseStart_553177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553177 prefixEnd_553177 := by exact prefixLift 553177
  have htrace : WordTrace (prefixWord ++ tailWord_553177) baseStart_553177 baseEnd_553177 := by
    simpa [prefixWord, tailWord_553177, baseEnd_553177] using wordTrace_append hprefix tailTrace_553177
  have hstable : (prefixWord ++ tailWord_553177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553177).length < 2 ^ (prefixWord ++ tailWord_553177).sum := by decide
  have hdescent : baseEnd_553177 < baseStart_553177 := by decide
  rcases family_descends (prefixWord ++ tailWord_553177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553181 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_553181 : Nat := 118140960795 + 553181 * 2 ^ 59
def prefixEnd_553181 : Nat := 4983230072969 + 3 ^ 40 * 553181 * 2
def baseEnd_553181 : Nat := 94682580644968470164491

theorem tailTrace_553181 : CollatzResearch.WordTrace tailWord_553181 prefixEnd_553181 94682580644968470164491 := by
  unfold tailWord_553181
  simp only [CollatzResearch.WordTrace]
  refine ⟨20176168608927187638307397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13450779072618125092204931 20176168608927187638307397)
  ·
    refine ⟨3783031614173847682182637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20176168608927187638307397 3783031614173847682182637)
    ·
      refine ⟨1418636855315192880818489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3783031614173847682182637 1418636855315192880818489)
      ·
        refine ⟨1063977641486394660613867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1418636855315192880818489 1063977641486394660613867)
        ·
          refine ⟨1595966462229591990920801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063977641486394660613867 1595966462229591990920801)
          ·
            refine ⟨1196974846672193993190601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1595966462229591990920801 1196974846672193993190601)
            ·
              refine ⟨897731135004145494892951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1196974846672193993190601 897731135004145494892951)
              ·
                refine ⟨1346596702506218242339427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 897731135004145494892951 1346596702506218242339427)
                ·
                  refine ⟨2019895053759327363509141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346596702506218242339427 2019895053759327363509141)
                  ·
                    refine ⟨94682580644968470164491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2019895053759327363509141 94682580644968470164491)
                    ·
                      rfl

theorem cell23_553181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_553181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553181 prefixEnd_553181 := by exact prefixLift 553181
  have htrace : WordTrace (prefixWord ++ tailWord_553181) baseStart_553181 baseEnd_553181 := by
    simpa [prefixWord, tailWord_553181, baseEnd_553181] using wordTrace_append hprefix tailTrace_553181
  have hstable : (prefixWord ++ tailWord_553181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553181).length < 2 ^ (prefixWord ++ tailWord_553181).sum := by decide
  have hdescent : baseEnd_553181 < baseStart_553181 := by decide
  rcases family_descends (prefixWord ++ tailWord_553181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553184 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 4]
def baseStart_553184 : Nat := 118140960795 + 553184 * 2 ^ 59
def prefixEnd_553184 : Nat := 4983230072969 + 3 ^ 40 * 553184 * 2
def baseEnd_553184 : Nat := 284049282376868898755959

theorem tailTrace_553184 : CollatzResearch.WordTrace tailWord_553184 prefixEnd_553184 284049282376868898755959 := by
  unfold tailWord_553184
  simp only [CollatzResearch.WordTrace]
  refine ⟨10088139013958159575333303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13450852018610879433777737 10088139013958159575333303)
  ·
    refine ⟨15132208520937239362999955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10088139013958159575333303 15132208520937239362999955)
    ·
      refine ⟨22698312781405859044499933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15132208520937239362999955 22698312781405859044499933)
      ·
        refine ⟨8511867293027197141687475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22698312781405859044499933 8511867293027197141687475)
        ·
          refine ⟨12767800939540795712531213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8511867293027197141687475 12767800939540795712531213)
          ·
            refine ⟨4787925352327798392199205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12767800939540795712531213 4787925352327798392199205)
            ·
              refine ⟨897736003561462198537351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4787925352327798392199205 897736003561462198537351)
              ·
                refine ⟨1346604005342193297806027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 897736003561462198537351 1346604005342193297806027)
                ·
                  refine ⟨2019906008013289946709041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346604005342193297806027 2019906008013289946709041)
                  ·
                    refine ⟨1514929506009967460031781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2019906008013289946709041 1514929506009967460031781)
                    ·
                      refine ⟨284049282376868898755959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1514929506009967460031781 284049282376868898755959)
                      ·
                        rfl

theorem cell23_553184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_553184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553184 prefixEnd_553184 := by exact prefixLift 553184
  have htrace : WordTrace (prefixWord ++ tailWord_553184) baseStart_553184 baseEnd_553184 := by
    simpa [prefixWord, tailWord_553184, baseEnd_553184] using wordTrace_append hprefix tailTrace_553184
  have hstable : (prefixWord ++ tailWord_553184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553184).length < 2 ^ (prefixWord ++ tailWord_553184).sum := by decide
  have hdescent : baseEnd_553184 < baseStart_553184 := by decide
  rcases family_descends (prefixWord ++ tailWord_553184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553191 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_553191 : Nat := 118140960795 + 553191 * 2 ^ 59
def prefixEnd_553191 : Nat := 4983230072969 + 3 ^ 40 * 553191 * 2
def baseEnd_553191 : Nat := 284052876741450371368427

theorem tailTrace_553191 : CollatzResearch.WordTrace tailWord_553191 prefixEnd_553191 284052876741450371368427 := by
  unfold tailWord_553191
  simp only [CollatzResearch.WordTrace]
  refine ⟨20176533338890959346171427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13451022225927306230780951 20176533338890959346171427)
  ·
    refine ⟨30264800008336439019257141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20176533338890959346171427 30264800008336439019257141)
    ·
      refine ⟨2837325000781541158055357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30264800008336439019257141 2837325000781541158055357)
      ·
        refine ⟨1063996875293077934270759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2837325000781541158055357 1063996875293077934270759)
        ·
          refine ⟨1595995312939616901406139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063996875293077934270759 1595995312939616901406139)
          ·
            refine ⟨2393992969409425352109209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595995312939616901406139 2393992969409425352109209)
            ·
              refine ⟨1795494727057069014081907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2393992969409425352109209 1795494727057069014081907)
              ·
                refine ⟨2693242090585603521122861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795494727057069014081907 2693242090585603521122861)
                ·
                  refine ⟨1009965783969601320421073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2693242090585603521122861 1009965783969601320421073)
                  ·
                    refine ⟨757474337977200990315805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1009965783969601320421073 757474337977200990315805)
                    ·
                      refine ⟨284052876741450371368427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 757474337977200990315805 284052876741450371368427)
                      ·
                        rfl

theorem cell23_553191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_553191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553191 prefixEnd_553191 := by exact prefixLift 553191
  have htrace : WordTrace (prefixWord ++ tailWord_553191) baseStart_553191 baseEnd_553191 := by
    simpa [prefixWord, tailWord_553191, baseEnd_553191] using wordTrace_append hprefix tailTrace_553191
  have hstable : (prefixWord ++ tailWord_553191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553191).length < 2 ^ (prefixWord ++ tailWord_553191).sum := by decide
  have hdescent : baseEnd_553191 < baseStart_553191 := by decide
  rcases family_descends (prefixWord ++ tailWord_553191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553194 : List Nat := [3, 1, 3, 1, 1, 2, 5, 7]
def baseStart_553194 : Nat := 118140960795 + 553194 * 2 ^ 59
def prefixEnd_553194 : Nat := 4983230072969 + 3 ^ 40 * 553194 * 2
def baseEnd_553194 : Nat := 10520533969756068875219

theorem tailTrace_553194 : CollatzResearch.WordTrace tailWord_553194 prefixEnd_553194 10520533969756068875219 := by
  unfold tailWord_553194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5044160689470022714632659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13451095171920060572353757 5044160689470022714632659)
  ·
    refine ⟨7566241034205034071948989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5044160689470022714632659 7566241034205034071948989)
    ·
      refine ⟨2837340387826887776980871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7566241034205034071948989 2837340387826887776980871)
      ·
        refine ⟨4256010581740331665471307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2837340387826887776980871 4256010581740331665471307)
        ·
          refine ⟨6384015872610497498206961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4256010581740331665471307 6384015872610497498206961)
          ·
            refine ⟨4788011904457873123655221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6384015872610497498206961 4788011904457873123655221)
            ·
              refine ⟨448876116042925605342677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4788011904457873123655221 448876116042925605342677)
              ·
                refine ⟨10520533969756068875219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 448876116042925605342677 10520533969756068875219)
                ·
                  rfl

theorem cell23_553194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 7].length) (baseStart_553194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553194 prefixEnd_553194 := by exact prefixLift 553194
  have htrace : WordTrace (prefixWord ++ tailWord_553194) baseStart_553194 baseEnd_553194 := by
    simpa [prefixWord, tailWord_553194, baseEnd_553194] using wordTrace_append hprefix tailTrace_553194
  have hstable : (prefixWord ++ tailWord_553194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553194).length < 2 ^ (prefixWord ++ tailWord_553194).sum := by decide
  have hdescent : baseEnd_553194 < baseStart_553194 := by decide
  rcases family_descends (prefixWord ++ tailWord_553194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553221 : List Nat := [1, 3, 1, 1, 2, 1, 2, 6, 2, 1, 3]
def baseStart_553221 : Nat := 118140960795 + 553221 * 2 ^ 59
def prefixEnd_553221 : Nat := 4983230072969 + 3 ^ 40 * 553221 * 2
def baseEnd_553221 : Nat := 284068281161085253993289

theorem tailTrace_553221 : CollatzResearch.WordTrace tailWord_553221 prefixEnd_553221 284068281161085253993289 := by
  unfold tailWord_553221
  simp only [CollatzResearch.WordTrace]
  refine ⟨20177627528782274469763517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13451751685854849646509011 20177627528782274469763517)
  ·
    refine ⟨7566610323293352926161319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20177627528782274469763517 7566610323293352926161319)
    ·
      refine ⟨11349915484940029389241979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7566610323293352926161319 11349915484940029389241979)
      ·
        refine ⟨17024873227410044083862969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11349915484940029389241979 17024873227410044083862969)
        ·
          refine ⟨12768654920557533062897227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17024873227410044083862969 12768654920557533062897227)
          ·
            refine ⟨19152982380836299594345841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12768654920557533062897227 19152982380836299594345841)
            ·
              refine ⟨14364736785627224695759381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19152982380836299594345841 14364736785627224695759381)
              ·
                refine ⟨673347036826276157613721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14364736785627224695759381 673347036826276157613721)
                ·
                  refine ⟨505010277619707118210291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 673347036826276157613721 505010277619707118210291)
                  ·
                    refine ⟨757515416429560677315437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 505010277619707118210291 757515416429560677315437)
                    ·
                      refine ⟨284068281161085253993289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 757515416429560677315437 284068281161085253993289)
                      ·
                        rfl

theorem cell23_553221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_553221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553221 prefixEnd_553221 := by exact prefixLift 553221
  have htrace : WordTrace (prefixWord ++ tailWord_553221) baseStart_553221 baseEnd_553221 := by
    simpa [prefixWord, tailWord_553221, baseEnd_553221] using wordTrace_append hprefix tailTrace_553221
  have hstable : (prefixWord ++ tailWord_553221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553221).length < 2 ^ (prefixWord ++ tailWord_553221).sum := by decide
  have hdescent : baseEnd_553221 < baseStart_553221 := by decide
  rcases family_descends (prefixWord ++ tailWord_553221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553248 : List Nat := [2, 1, 1, 5, 2, 1, 1, 4, 1, 3, 2]
def baseStart_553248 : Nat := 118140960795 + 553248 * 2 ^ 59
def prefixEnd_553248 : Nat := 4983230072969 + 3 ^ 40 * 553248 * 2
def baseEnd_553248 : Nat := 284082145138756648355665

theorem tailTrace_553248 : CollatzResearch.WordTrace tailWord_553248 prefixEnd_553248 284082145138756648355665 := by
  unfold tailWord_553248
  simp only [CollatzResearch.WordTrace]
  refine ⟨10089306149842229040498199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13452408199789638720664265 10089306149842229040498199)
  ·
    refine ⟨15133959224763343560747299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10089306149842229040498199 15133959224763343560747299)
    ·
      refine ⟨22700938837145015341120949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15133959224763343560747299 22700938837145015341120949)
      ·
        refine ⟨2128213015982345188230089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22700938837145015341120949 2128213015982345188230089)
        ·
          refine ⟨1596159761986758891172567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2128213015982345188230089 1596159761986758891172567)
          ·
            refine ⟨2394239642980138336758851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596159761986758891172567 2394239642980138336758851)
            ·
              refine ⟨3591359464470207505138277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2394239642980138336758851 3591359464470207505138277)
              ·
                refine ⟨673379899588163907213427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3591359464470207505138277 673379899588163907213427)
                ·
                  refine ⟨1010069849382245860820141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 673379899588163907213427 1010069849382245860820141)
                  ·
                    refine ⟨378776193518342197807553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1010069849382245860820141 378776193518342197807553)
                    ·
                      refine ⟨284082145138756648355665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 378776193518342197807553 284082145138756648355665)
                      ·
                        rfl

theorem cell23_553248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_553248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553248 prefixEnd_553248 := by exact prefixLift 553248
  have htrace : WordTrace (prefixWord ++ tailWord_553248) baseStart_553248 baseEnd_553248 := by
    simpa [prefixWord, tailWord_553248, baseEnd_553248] using wordTrace_append hprefix tailTrace_553248
  have hstable : (prefixWord ++ tailWord_553248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553248).length < 2 ^ (prefixWord ++ tailWord_553248).sum := by decide
  have hdescent : baseEnd_553248 < baseStart_553248 := by decide
  rcases family_descends (prefixWord ++ tailWord_553248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553368 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 2, 1, 4]
def baseStart_553368 : Nat := 118140960795 + 553368 * 2 ^ 59
def prefixEnd_553368 : Nat := 4983230072969 + 3 ^ 40 * 553368 * 2
def baseEnd_553368 : Nat := 284143762817296178855113

theorem tailTrace_553368 : CollatzResearch.WordTrace tailWord_553368 prefixEnd_553368 284143762817296178855113 := by
  unfold tailWord_553368
  simp only [CollatzResearch.WordTrace]
  refine ⟨10091494529624859287682379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13455326039499812383576505 10091494529624859287682379)
  ·
    refine ⟨15137241794437288931523569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10091494529624859287682379 15137241794437288931523569)
    ·
      refine ⟨11352931345827966698642677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15137241794437288931523569 11352931345827966698642677)
      ·
        refine ⟨1064337313671371877997751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11352931345827966698642677 1064337313671371877997751)
        ·
          refine ⟨1596505970507057816996627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064337313671371877997751 1596505970507057816996627)
          ·
            refine ⟨2394758955760586725494941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596505970507057816996627 2394758955760586725494941)
            ·
              refine ⟨898034608410220022060603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2394758955760586725494941 898034608410220022060603)
              ·
                refine ⟨1347051912615330033090905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898034608410220022060603 1347051912615330033090905)
                ·
                  refine ⟨1010288934461497524818179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1347051912615330033090905 1010288934461497524818179)
                  ·
                    refine ⟨1515433401692246287227269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1010288934461497524818179 1515433401692246287227269)
                    ·
                      refine ⟨284143762817296178855113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1515433401692246287227269 284143762817296178855113)
                      ·
                        rfl

theorem cell23_553368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_553368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553368 prefixEnd_553368 := by exact prefixLift 553368
  have htrace : WordTrace (prefixWord ++ tailWord_553368) baseStart_553368 baseEnd_553368 := by
    simpa [prefixWord, tailWord_553368, baseEnd_553368] using wordTrace_append hprefix tailTrace_553368
  have hstable : (prefixWord ++ tailWord_553368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553368).length < 2 ^ (prefixWord ++ tailWord_553368).sum := by decide
  have hdescent : baseEnd_553368 < baseStart_553368 := by decide
  rcases family_descends (prefixWord ++ tailWord_553368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553394 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_553394 : Nat := 118140960795 + 553394 * 2 ^ 59
def prefixEnd_553394 : Nat := 4983230072969 + 3 ^ 40 * 553394 * 2
def baseEnd_553394 : Nat := 284157113314313077129993

theorem tailTrace_553394 : CollatzResearch.WordTrace tailWord_553394 prefixEnd_553394 284157113314313077129993 := by
  unfold tailWord_553394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5045984339288881253952809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13455958238103683343874157 5045984339288881253952809)
  ·
    refine ⟨3784488254466660940464607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5045984339288881253952809 3784488254466660940464607)
    ·
      refine ⟨5676732381699991410696911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3784488254466660940464607 5676732381699991410696911)
      ·
        refine ⟨8515098572549987116045367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5676732381699991410696911 8515098572549987116045367)
        ·
          refine ⟨12772647858824980674068051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8515098572549987116045367 12772647858824980674068051)
          ·
            refine ⟨19158971788237471011102077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12772647858824980674068051 19158971788237471011102077)
            ·
              refine ⟨7184614420589051629163279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19158971788237471011102077 7184614420589051629163279)
              ·
                refine ⟨10776921630883577443744919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7184614420589051629163279 10776921630883577443744919)
                ·
                  refine ⟨16165382446325366165617379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10776921630883577443744919 16165382446325366165617379)
                  ·
                    refine ⟨24248073669488049248426069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16165382446325366165617379 24248073669488049248426069)
                    ·
                      refine ⟨284157113314313077129993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 24248073669488049248426069 284157113314313077129993)
                      ·
                        rfl

theorem cell23_553394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_553394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553394 prefixEnd_553394 := by exact prefixLift 553394
  have htrace : WordTrace (prefixWord ++ tailWord_553394) baseStart_553394 baseEnd_553394 := by
    simpa [prefixWord, tailWord_553394, baseEnd_553394] using wordTrace_append hprefix tailTrace_553394
  have hstable : (prefixWord ++ tailWord_553394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553394).length < 2 ^ (prefixWord ++ tailWord_553394).sum := by decide
  have hdescent : baseEnd_553394 < baseStart_553394 := by decide
  rcases family_descends (prefixWord ++ tailWord_553394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553418 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_553418 : Nat := 118140960795 + 553418 * 2 ^ 59
def prefixEnd_553418 : Nat := 4983230072969 + 3 ^ 40 * 553418 * 2
def baseEnd_553418 : Nat := 284169436850020983229883

theorem tailTrace_553418 : CollatzResearch.WordTrace tailWord_553418 prefixEnd_553418 284169436850020983229883 := by
  unfold tailWord_553418
  simp only [CollatzResearch.WordTrace]
  refine ⟨5046203177267144278671227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13456541806045718076456605 5046203177267144278671227)
  ·
    refine ⟨7569304765900716418006841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5046203177267144278671227 7569304765900716418006841)
    ·
      refine ⟨5676978574425537313505131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7569304765900716418006841 5676978574425537313505131)
      ·
        refine ⟨8515467861638305970257697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5676978574425537313505131 8515467861638305970257697)
        ·
          refine ⟨6386600896228729477693273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8515467861638305970257697 6386600896228729477693273)
          ·
            refine ⟨4789950672171547108269955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6386600896228729477693273 4789950672171547108269955)
            ·
              refine ⟨7184926008257320662404933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4789950672171547108269955 7184926008257320662404933)
              ·
                refine ⟨1347173626548247624200925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7184926008257320662404933 1347173626548247624200925)
                ·
                  refine ⟨505190109955592859075347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1347173626548247624200925 505190109955592859075347)
                  ·
                    refine ⟨757785164933389288613021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 505190109955592859075347 757785164933389288613021)
                    ·
                      refine ⟨284169436850020983229883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 757785164933389288613021 284169436850020983229883)
                      ·
                        rfl

theorem cell23_553418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_553418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553418 prefixEnd_553418 := by exact prefixLift 553418
  have htrace : WordTrace (prefixWord ++ tailWord_553418) baseStart_553418 baseEnd_553418 := by
    simpa [prefixWord, tailWord_553418, baseEnd_553418] using wordTrace_append hprefix tailTrace_553418
  have hstable : (prefixWord ++ tailWord_553418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553418).length < 2 ^ (prefixWord ++ tailWord_553418).sum := by decide
  have hdescent : baseEnd_553418 < baseStart_553418 := by decide
  rcases family_descends (prefixWord ++ tailWord_553418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553451 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 4, 4]
def baseStart_553451 : Nat := 118140960795 + 553451 * 2 ^ 59
def prefixEnd_553451 : Nat := 4983230072969 + 3 ^ 40 * 553451 * 2
def baseEnd_553451 : Nat := 94728793903873118039077

theorem tailTrace_553451 : CollatzResearch.WordTrace tailWord_553451 prefixEnd_553451 94728793903873118039077 := by
  unfold tailWord_553451
  simp only [CollatzResearch.WordTrace]
  refine ⟨20186016317949023750636207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13457344211966015833757471 20186016317949023750636207)
  ·
    refine ⟨30279024476923535625954311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20186016317949023750636207 30279024476923535625954311)
    ·
      refine ⟨45418536715385303438931467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30279024476923535625954311 45418536715385303438931467)
      ·
        refine ⟨68127805073077955158397201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45418536715385303438931467 68127805073077955158397201)
        ·
          refine ⟨51095853804808466368797901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68127805073077955158397201 51095853804808466368797901)
          ·
            refine ⟨19160945176803174888299213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51095853804808466368797901 19160945176803174888299213)
            ·
              refine ⟨7185354441301190583112205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19160945176803174888299213 7185354441301190583112205)
              ·
                refine ⟨2694507915487946468667077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7185354441301190583112205 2694507915487946468667077)
                ·
                  refine ⟨505220234153989962875077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2694507915487946468667077 505220234153989962875077)
                  ·
                    refine ⟨94728793903873118039077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 505220234153989962875077 94728793903873118039077)
                    ·
                      rfl

theorem cell23_553451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 4].length) (baseStart_553451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553451 prefixEnd_553451 := by exact prefixLift 553451
  have htrace : WordTrace (prefixWord ++ tailWord_553451) baseStart_553451 baseEnd_553451 := by
    simpa [prefixWord, tailWord_553451, baseEnd_553451] using wordTrace_append hprefix tailTrace_553451
  have hstable : (prefixWord ++ tailWord_553451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553451).length < 2 ^ (prefixWord ++ tailWord_553451).sum := by decide
  have hdescent : baseEnd_553451 < baseStart_553451 := by decide
  rcases family_descends (prefixWord ++ tailWord_553451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553452 : List Nat := [2, 2, 1, 1, 2, 1, 7, 2, 1, 1, 3]
def baseStart_553452 : Nat := 118140960795 + 553452 * 2 ^ 59
def prefixEnd_553452 : Nat := 4983230072969 + 3 ^ 40 * 553452 * 2
def baseEnd_553452 : Nat := 284186895192273850204727

theorem tailTrace_553452 : CollatzResearch.WordTrace tailWord_553452 prefixEnd_553452 284186895192273850204727 := by
  unfold tailWord_553452
  simp only [CollatzResearch.WordTrace]
  refine ⟨10093026395472700460711305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13457368527296933947615073 10093026395472700460711305)
  ·
    refine ⟨7569769796604525345533479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10093026395472700460711305 7569769796604525345533479)
    ·
      refine ⟨11354654694906788018300219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7569769796604525345533479 11354654694906788018300219)
      ·
        refine ⟨17031982042360182027450329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11354654694906788018300219 17031982042360182027450329)
        ·
          refine ⟨12773986531770136520587747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17031982042360182027450329 12773986531770136520587747)
          ·
            refine ⟨19160979797655204780881621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12773986531770136520587747 19160979797655204780881621)
            ·
              refine ⟨449085464007543862051913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19160979797655204780881621 449085464007543862051913)
              ·
                refine ⟨336814098005657896538935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449085464007543862051913 336814098005657896538935)
                ·
                  refine ⟨505221147008486844808403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336814098005657896538935 505221147008486844808403)
                  ·
                    refine ⟨757831720512730267212605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 505221147008486844808403 757831720512730267212605)
                    ·
                      refine ⟨284186895192273850204727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 757831720512730267212605 284186895192273850204727)
                      ·
                        rfl

theorem cell23_553452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 1, 1, 3].length) (baseStart_553452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553452 prefixEnd_553452 := by exact prefixLift 553452
  have htrace : WordTrace (prefixWord ++ tailWord_553452) baseStart_553452 baseEnd_553452 := by
    simpa [prefixWord, tailWord_553452, baseEnd_553452] using wordTrace_append hprefix tailTrace_553452
  have hstable : (prefixWord ++ tailWord_553452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553452).length < 2 ^ (prefixWord ++ tailWord_553452).sum := by decide
  have hdescent : baseEnd_553452 < baseStart_553452 := by decide
  rcases family_descends (prefixWord ++ tailWord_553452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553471 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 4]
def baseStart_553471 : Nat := 118140960795 + 553471 * 2 ^ 59
def prefixEnd_553471 : Nat := 4983230072969 + 3 ^ 40 * 553471 * 2
def baseEnd_553471 : Nat := 284196651324709275867139

theorem tailTrace_553471 : CollatzResearch.WordTrace tailWord_553471 prefixEnd_553471 284196651324709275867139 := by
  unfold tailWord_553471
  simp only [CollatzResearch.WordTrace]
  refine ⟨20186745777876567166364267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13457830518584378110909511 20186745777876567166364267)
  ·
    refine ⟨30280118666814850749546401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20186745777876567166364267 30280118666814850749546401)
    ·
      refine ⟨22710089000111138062159801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30280118666814850749546401 22710089000111138062159801)
      ·
        refine ⟨17032566750083353546619851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22710089000111138062159801 17032566750083353546619851)
        ·
          refine ⟨25548850125125030319929777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17032566750083353546619851 25548850125125030319929777)
          ·
            refine ⟨19161637593843772739947333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25548850125125030319929777 19161637593843772739947333)
            ·
              refine ⟨3592807048845707388740125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19161637593843772739947333 3592807048845707388740125)
              ·
                refine ⟨1347302643317140270777547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3592807048845707388740125 1347302643317140270777547)
                ·
                  refine ⟨2020953964975710406166321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347302643317140270777547 2020953964975710406166321)
                  ·
                    refine ⟨1515715473731782804624741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2020953964975710406166321 1515715473731782804624741)
                    ·
                      refine ⟨284196651324709275867139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1515715473731782804624741 284196651324709275867139)
                      ·
                        rfl

theorem cell23_553471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_553471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553471 prefixEnd_553471 := by exact prefixLift 553471
  have htrace : WordTrace (prefixWord ++ tailWord_553471) baseStart_553471 baseEnd_553471 := by
    simpa [prefixWord, tailWord_553471, baseEnd_553471] using wordTrace_append hprefix tailTrace_553471
  have hstable : (prefixWord ++ tailWord_553471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553471).length < 2 ^ (prefixWord ++ tailWord_553471).sum := by decide
  have hdescent : baseEnd_553471 < baseStart_553471 := by decide
  rcases family_descends (prefixWord ++ tailWord_553471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553485 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_553485 : Nat := 118140960795 + 553485 * 2 ^ 59
def prefixEnd_553485 : Nat := 4983230072969 + 3 ^ 40 * 553485 * 2
def baseEnd_553485 : Nat := 94734613351290740364025

theorem tailTrace_553485 : CollatzResearch.WordTrace tailWord_553485 prefixEnd_553485 94734613351290740364025 := by
  unfold tailWord_553485
  simp only [CollatzResearch.WordTrace]
  refine ⟨20187256399825847557373909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13458170933217231704915939 20187256399825847557373909)
  ·
    refine ⟨473138821870918302125951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 20187256399825847557373909 473138821870918302125951)
    ·
      refine ⟨709708232806377453188927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 473138821870918302125951 709708232806377453188927)
      ·
        refine ⟨1064562349209566179783391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709708232806377453188927 1064562349209566179783391)
        ·
          refine ⟨1596843523814349269675087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064562349209566179783391 1596843523814349269675087)
          ·
            refine ⟨2395265285721523904512631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596843523814349269675087 2395265285721523904512631)
            ·
              refine ⟨3592897928582285856768947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2395265285721523904512631 3592897928582285856768947)
              ·
                refine ⟨5389346892873428785153421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3592897928582285856768947 5389346892873428785153421)
                ·
                  refine ⟨2021005084827535794432533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5389346892873428785153421 2021005084827535794432533)
                  ·
                    refine ⟨94734613351290740364025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2021005084827535794432533 94734613351290740364025)
                    ·
                      rfl

theorem cell23_553485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_553485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553485 prefixEnd_553485 := by exact prefixLift 553485
  have htrace : WordTrace (prefixWord ++ tailWord_553485) baseStart_553485 baseEnd_553485 := by
    simpa [prefixWord, tailWord_553485, baseEnd_553485] using wordTrace_append hprefix tailTrace_553485
  have hstable : (prefixWord ++ tailWord_553485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553485).length < 2 ^ (prefixWord ++ tailWord_553485).sum := by decide
  have hdescent : baseEnd_553485 < baseStart_553485 := by decide
  rcases family_descends (prefixWord ++ tailWord_553485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553509 : List Nat := [1, 3, 1, 2, 2, 1, 6, 2, 1, 2, 2]
def baseStart_553509 : Nat := 118140960795 + 553509 * 2 ^ 59
def prefixEnd_553509 : Nat := 4983230072969 + 3 ^ 40 * 553509 * 2
def baseEnd_553509 : Nat := 284216163589580127191965

theorem tailTrace_553509 : CollatzResearch.WordTrace tailWord_553509 prefixEnd_553509 284216163589580127191965 := by
  unfold tailWord_553509
  simp only [CollatzResearch.WordTrace]
  refine ⟨20188131751738899656247581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13458754501159266437498387 20188131751738899656247581)
  ·
    refine ⟨7570549406902087371092843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20188131751738899656247581 7570549406902087371092843)
    ·
      refine ⟨11355824110353131056639265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7570549406902087371092843 11355824110353131056639265)
      ·
        refine ⟨8516868082764848292479449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11355824110353131056639265 8516868082764848292479449)
        ·
          refine ⟨6387651062073636219359587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8516868082764848292479449 6387651062073636219359587)
          ·
            refine ⟨9581476593110454329039381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6387651062073636219359587 9581476593110454329039381)
            ·
              refine ⟨449131715302052546673721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9581476593110454329039381 449131715302052546673721)
              ·
                refine ⟨336848786476539410005291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449131715302052546673721 336848786476539410005291)
                ·
                  refine ⟨505273179714809115007937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336848786476539410005291 505273179714809115007937)
                  ·
                    refine ⟨378954884786106836255953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 505273179714809115007937 378954884786106836255953)
                    ·
                      refine ⟨284216163589580127191965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 378954884786106836255953 284216163589580127191965)
                      ·
                        rfl

theorem cell23_553509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_553509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553509 prefixEnd_553509 := by exact prefixLift 553509
  have htrace : WordTrace (prefixWord ++ tailWord_553509) baseStart_553509 baseEnd_553509 := by
    simpa [prefixWord, tailWord_553509, baseEnd_553509] using wordTrace_append hprefix tailTrace_553509
  have hstable : (prefixWord ++ tailWord_553509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553509).length < 2 ^ (prefixWord ++ tailWord_553509).sum := by decide
  have hdescent : baseEnd_553509 < baseStart_553509 := by decide
  rcases family_descends (prefixWord ++ tailWord_553509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553525 : List Nat := [1, 3, 3, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_553525 : Nat := 118140960795 + 553525 * 2 ^ 59
def prefixEnd_553525 : Nat := 4983230072969 + 3 ^ 40 * 553525 * 2
def baseEnd_553525 : Nat := 284224379280052064591891

theorem tailTrace_553525 : CollatzResearch.WordTrace tailWord_553525 prefixEnd_553525 284224379280052064591891 := by
  unfold tailWord_553525
  simp only [CollatzResearch.WordTrace]
  refine ⟨20188715319680934388830029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13459143546453956259220019 20188715319680934388830029)
  ·
    refine ⟨7570768244880350395811261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20188715319680934388830029 7570768244880350395811261)
    ·
      refine ⟨2839038091830131398429223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7570768244880350395811261 2839038091830131398429223)
      ·
        refine ⟨4258557137745197097643835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2839038091830131398429223 4258557137745197097643835)
        ·
          refine ⟨6387835706617795646465753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4258557137745197097643835 6387835706617795646465753)
          ·
            refine ⟨4790876779963346734849315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6387835706617795646465753 4790876779963346734849315)
            ·
              refine ⟨7186315169945020102273973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4790876779963346734849315 7186315169945020102273973)
              ·
                refine ⟨673717047182345634588185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7186315169945020102273973 673717047182345634588185)
                ·
                  refine ⟨505287785386759225941139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 673717047182345634588185 505287785386759225941139)
                  ·
                    refine ⟨757931678080138838911709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 505287785386759225941139 757931678080138838911709)
                    ·
                      refine ⟨284224379280052064591891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 757931678080138838911709 284224379280052064591891)
                      ·
                        rfl

theorem cell23_553525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_553525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553525 prefixEnd_553525 := by exact prefixLift 553525
  have htrace : WordTrace (prefixWord ++ tailWord_553525) baseStart_553525 baseEnd_553525 := by
    simpa [prefixWord, tailWord_553525, baseEnd_553525] using wordTrace_append hprefix tailTrace_553525
  have hstable : (prefixWord ++ tailWord_553525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553525).length < 2 ^ (prefixWord ++ tailWord_553525).sum := by decide
  have hdescent : baseEnd_553525 < baseStart_553525 := by decide
  rcases family_descends (prefixWord ++ tailWord_553525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553535 : List Nat := [1, 1, 2, 2, 3, 2, 2, 4, 1, 3, 2]
def baseStart_553535 : Nat := 118140960795 + 553535 * 2 ^ 59
def prefixEnd_553535 : Nat := 4983230072969 + 3 ^ 40 * 553535 * 2
def baseEnd_553535 : Nat := 284229514086597025466845

theorem tailTrace_553535 : CollatzResearch.WordTrace tailWord_553535 prefixEnd_553535 284229514086597025466845 := by
  unfold tailWord_553535
  simp only [CollatzResearch.WordTrace]
  refine ⟨20189080049644706096694059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13459386699763137397796039 20189080049644706096694059)
  ·
    refine ⟨30283620074467059145041089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20189080049644706096694059 30283620074467059145041089)
    ·
      refine ⟨22712715055850294358780817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30283620074467059145041089 22712715055850294358780817)
      ·
        refine ⟨17034536291887720769085613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22712715055850294358780817 17034536291887720769085613)
        ·
          refine ⟨6387951109457895288407105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17034536291887720769085613 6387951109457895288407105)
          ·
            refine ⟨4790963332093421466305329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6387951109457895288407105 4790963332093421466305329)
            ·
              refine ⟨3593222499070066099728997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4790963332093421466305329 3593222499070066099728997)
              ·
                refine ⟨673729218575637393699187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3593222499070066099728997 673729218575637393699187)
                ·
                  refine ⟨1010593827863456090548781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 673729218575637393699187 1010593827863456090548781)
                  ·
                    refine ⟨378972685448796033955793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1010593827863456090548781 378972685448796033955793)
                    ·
                      refine ⟨284229514086597025466845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 378972685448796033955793 284229514086597025466845)
                      ·
                        rfl

theorem cell23_553535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 3, 2].length) (baseStart_553535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553535 prefixEnd_553535 := by exact prefixLift 553535
  have htrace : WordTrace (prefixWord ++ tailWord_553535) baseStart_553535 baseEnd_553535 := by
    simpa [prefixWord, tailWord_553535, baseEnd_553535] using wordTrace_append hprefix tailTrace_553535
  have hstable : (prefixWord ++ tailWord_553535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553535).length < 2 ^ (prefixWord ++ tailWord_553535).sum := by decide
  have hdescent : baseEnd_553535 < baseStart_553535 := by decide
  rcases family_descends (prefixWord ++ tailWord_553535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553542 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_553542 : Nat := 118140960795 + 553542 * 2 ^ 59
def prefixEnd_553542 : Nat := 4983230072969 + 3 ^ 40 * 553542 * 2
def baseEnd_553542 : Nat := 284233108451178498079313

theorem tailTrace_553542 : CollatzResearch.WordTrace tailWord_553542 prefixEnd_553542 284233108451178498079313 := by
  unfold tailWord_553542
  simp only [CollatzResearch.WordTrace]
  refine ⟨630916730019354571631215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13459556907079564194799253 630916730019354571631215)
  ·
    refine ⟨946375095029031857446823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 630916730019354571631215 946375095029031857446823)
    ·
      refine ⟨1419562642543547786170235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 946375095029031857446823 1419562642543547786170235)
      ·
        refine ⟨2129343963815321679255353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1419562642543547786170235 2129343963815321679255353)
        ·
          refine ⟨1597007972861491259441515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2129343963815321679255353 1597007972861491259441515)
          ·
            refine ⟨2395511959292236889162273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597007972861491259441515 2395511959292236889162273)
            ·
              refine ⟨1796633969469177666871705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2395511959292236889162273 1796633969469177666871705)
              ·
                refine ⟨1347475477101883250153779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1796633969469177666871705 1347475477101883250153779)
                ·
                  refine ⟨2021213215652824875230669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347475477101883250153779 2021213215652824875230669)
                  ·
                    refine ⟨757954955869809328211501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2021213215652824875230669 757954955869809328211501)
                    ·
                      refine ⟨284233108451178498079313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 757954955869809328211501 284233108451178498079313)
                      ·
                        rfl

theorem cell23_553542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_553542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553542 prefixEnd_553542 := by exact prefixLift 553542
  have htrace : WordTrace (prefixWord ++ tailWord_553542) baseStart_553542 baseEnd_553542 := by
    simpa [prefixWord, tailWord_553542, baseEnd_553542] using wordTrace_append hprefix tailTrace_553542
  have hstable : (prefixWord ++ tailWord_553542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553542).length < 2 ^ (prefixWord ++ tailWord_553542).sum := by decide
  have hdescent : baseEnd_553542 < baseStart_553542 := by decide
  rcases family_descends (prefixWord ++ tailWord_553542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553551 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 5]
def baseStart_553551 : Nat := 118140960795 + 553551 * 2 ^ 59
def prefixEnd_553551 : Nat := 4983230072969 + 3 ^ 40 * 553551 * 2
def baseEnd_553551 : Nat := 284237729777068962866771

theorem tailTrace_553551 : CollatzResearch.WordTrace tailWord_553551 prefixEnd_553551 284237729777068962866771 := by
  unfold tailWord_553551
  simp only [CollatzResearch.WordTrace]
  refine ⟨20189663617586740829276507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13459775745057827219517671 20189663617586740829276507)
  ·
    refine ⟨30284495426380111243914761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20189663617586740829276507 30284495426380111243914761)
    ·
      refine ⟨22713371569785083432936071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30284495426380111243914761 22713371569785083432936071)
      ·
        refine ⟨34070057354677625149404107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22713371569785083432936071 34070057354677625149404107)
        ·
          refine ⟨51105086032016437724106161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34070057354677625149404107 51105086032016437724106161)
          ·
            refine ⟨38328814524012328293079621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51105086032016437724106161 38328814524012328293079621)
            ·
              refine ⟨7186652723252311554952429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38328814524012328293079621 7186652723252311554952429)
              ·
                refine ⟨2694994771219616833107161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7186652723252311554952429 2694994771219616833107161)
                ·
                  refine ⟨2021246078414712624830371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2694994771219616833107161 2021246078414712624830371)
                  ·
                    refine ⟨3031869117622068937245557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2021246078414712624830371 3031869117622068937245557)
                    ·
                      refine ⟨284237729777068962866771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3031869117622068937245557 284237729777068962866771)
                      ·
                        rfl

theorem cell23_553551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_553551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553551 prefixEnd_553551 := by exact prefixLift 553551
  have htrace : WordTrace (prefixWord ++ tailWord_553551) baseStart_553551 baseEnd_553551 := by
    simpa [prefixWord, tailWord_553551, baseEnd_553551] using wordTrace_append hprefix tailTrace_553551
  have hstable : (prefixWord ++ tailWord_553551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553551).length < 2 ^ (prefixWord ++ tailWord_553551).sum := by decide
  have hdescent : baseEnd_553551 < baseStart_553551 := by decide
  rcases family_descends (prefixWord ++ tailWord_553551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553578 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_553578 : Nat := 118140960795 + 553578 * 2 ^ 59
def prefixEnd_553578 : Nat := 4983230072969 + 3 ^ 40 * 553578 * 2
def baseEnd_553578 : Nat := 284251593754740357229147

theorem tailTrace_553578 : CollatzResearch.WordTrace tailWord_553578 prefixEnd_553578 284251593754740357229147 := by
  unfold tailWord_553578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5047662097122231110127347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13460432258992616293672925 5047662097122231110127347)
  ·
    refine ⟨7571493145683346665191021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5047662097122231110127347 7571493145683346665191021)
    ·
      refine ⟨2839309929631254999446633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7571493145683346665191021 2839309929631254999446633)
      ·
        refine ⟨2129482447223441249584975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2839309929631254999446633 2129482447223441249584975)
        ·
          refine ⟨3194223670835161874377463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2129482447223441249584975 3194223670835161874377463)
          ·
            refine ⟨4791335506252742811566195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3194223670835161874377463 4791335506252742811566195)
            ·
              refine ⟨7187003259379114217349293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4791335506252742811566195 7187003259379114217349293)
              ·
                refine ⟨2695126222267167831505985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7187003259379114217349293 2695126222267167831505985)
                ·
                  refine ⟨2021344666700375873629489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2695126222267167831505985 2021344666700375873629489)
                  ·
                    refine ⟨1516008500025281905222117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2021344666700375873629489 1516008500025281905222117)
                    ·
                      refine ⟨284251593754740357229147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1516008500025281905222117 284251593754740357229147)
                      ·
                        rfl

theorem cell23_553578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_553578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553578 prefixEnd_553578 := by exact prefixLift 553578
  have htrace : WordTrace (prefixWord ++ tailWord_553578) baseStart_553578 baseEnd_553578 := by
    simpa [prefixWord, tailWord_553578, baseEnd_553578] using wordTrace_append hprefix tailTrace_553578
  have hstable : (prefixWord ++ tailWord_553578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553578).length < 2 ^ (prefixWord ++ tailWord_553578).sum := by decide
  have hdescent : baseEnd_553578 < baseStart_553578 := by decide
  rcases family_descends (prefixWord ++ tailWord_553578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553582 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_553582 : Nat := 118140960795 + 553582 * 2 ^ 59
def prefixEnd_553582 : Nat := 4983230072969 + 3 ^ 40 * 553582 * 2
def baseEnd_553582 : Nat := 284253647677358341579129

theorem tailTrace_553582 : CollatzResearch.WordTrace tailWord_553582 prefixEnd_553582 284253647677358341579129 := by
  unfold tailWord_553582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2523849285059304140456875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13460529520316288749103333 2523849285059304140456875)
  ·
    refine ⟨3785773927588956210685313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2523849285059304140456875 3785773927588956210685313)
    ·
      refine ⟨2839330445691717158013985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3785773927588956210685313 2839330445691717158013985)
      ·
        refine ⟨2129497834268787868510489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2839330445691717158013985 2129497834268787868510489)
        ·
          refine ⟨1597123375701590901382867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2129497834268787868510489 1597123375701590901382867)
          ·
            refine ⟨2395685063552386352074301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597123375701590901382867 2395685063552386352074301)
            ·
              refine ⟨898381898832144882027863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2395685063552386352074301 898381898832144882027863)
              ·
                refine ⟨1347572848248217323041795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898381898832144882027863 1347572848248217323041795)
                ·
                  refine ⟨2021359272372325984562693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347572848248217323041795 2021359272372325984562693)
                  ·
                    refine ⟨379004863569811122105505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2021359272372325984562693 379004863569811122105505)
                    ·
                      refine ⟨284253647677358341579129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 379004863569811122105505 284253647677358341579129)
                      ·
                        rfl

theorem cell23_553582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_553582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553582 prefixEnd_553582 := by exact prefixLift 553582
  have htrace : WordTrace (prefixWord ++ tailWord_553582) baseStart_553582 baseEnd_553582 := by
    simpa [prefixWord, tailWord_553582, baseEnd_553582] using wordTrace_append hprefix tailTrace_553582
  have hstable : (prefixWord ++ tailWord_553582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553582).length < 2 ^ (prefixWord ++ tailWord_553582).sum := by decide
  have hdescent : baseEnd_553582 < baseStart_553582 := by decide
  rcases family_descends (prefixWord ++ tailWord_553582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553605 : List Nat := [1, 3, 1, 1, 4, 2, 3, 3, 5]
def baseStart_553605 : Nat := 118140960795 + 553605 * 2 ^ 59
def prefixEnd_553605 : Nat := 4983230072969 + 3 ^ 40 * 553605 * 2
def baseEnd_553605 : Nat := 31585050859156861287947

theorem tailTrace_553605 : CollatzResearch.WordTrace tailWord_553605 prefixEnd_553605 31585050859156861287947 := by
  unfold tailWord_553605
  simp only [CollatzResearch.WordTrace]
  refine ⟨20191633159391108051742269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13461088772927405367828179 20191633159391108051742269)
  ·
    refine ⟨7571862434771665519403351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20191633159391108051742269 7571862434771665519403351)
    ·
      refine ⟨11357793652157498279105027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7571862434771665519403351 11357793652157498279105027)
      ·
        refine ⟨17036690478236247418657541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11357793652157498279105027 17036690478236247418657541)
        ·
          refine ⟨3194379464669296390998289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17036690478236247418657541 3194379464669296390998289)
          ·
            refine ⟨2395784598501972293248717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3194379464669296390998289 2395784598501972293248717)
            ·
              refine ⟨898419224438239609968269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2395784598501972293248717 898419224438239609968269)
              ·
                refine ⟨336907209164339853738101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 898419224438239609968269 336907209164339853738101)
                ·
                  refine ⟨31585050859156861287947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 336907209164339853738101 31585050859156861287947)
                  ·
                    rfl

theorem cell23_553605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 5].length) (baseStart_553605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553605 prefixEnd_553605 := by exact prefixLift 553605
  have htrace : WordTrace (prefixWord ++ tailWord_553605) baseStart_553605 baseEnd_553605 := by
    simpa [prefixWord, tailWord_553605, baseEnd_553605] using wordTrace_append hprefix tailTrace_553605
  have hstable : (prefixWord ++ tailWord_553605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553605).length < 2 ^ (prefixWord ++ tailWord_553605).sum := by decide
  have hdescent : baseEnd_553605 < baseStart_553605 := by decide
  rcases family_descends (prefixWord ++ tailWord_553605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553621 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_553621 : Nat := 118140960795 + 553621 * 2 ^ 59
def prefixEnd_553621 : Nat := 4983230072969 + 3 ^ 40 * 553621 * 2
def baseEnd_553621 : Nat := 284273673422883688991449

theorem tailTrace_553621 : CollatzResearch.WordTrace tailWord_553621 prefixEnd_553621 284273673422883688991449 := by
  unfold tailWord_553621
  simp only [CollatzResearch.WordTrace]
  refine ⟨20192216727333142784324717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13461477818222095189549811 20192216727333142784324717)
  ·
    refine ⟨7572081272749928544121769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20192216727333142784324717 7572081272749928544121769)
    ·
      refine ⟨5679060954562446408091327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7572081272749928544121769 5679060954562446408091327)
      ·
        refine ⟨8518591431843669612136991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5679060954562446408091327 8518591431843669612136991)
        ·
          refine ⟨12777887147765504418205487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8518591431843669612136991 12777887147765504418205487)
          ·
            refine ⟨19166830721648256627308231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12777887147765504418205487 19166830721648256627308231)
            ·
              refine ⟨28750246082472384940962347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19166830721648256627308231 28750246082472384940962347)
              ·
                refine ⟨43125369123708577411443521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28750246082472384940962347 43125369123708577411443521)
                ·
                  refine ⟨32344026842781433058582641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43125369123708577411443521 32344026842781433058582641)
                  ·
                    refine ⟨24258020132086074793936981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32344026842781433058582641 24258020132086074793936981)
                    ·
                      refine ⟨284273673422883688991449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 24258020132086074793936981 284273673422883688991449)
                      ·
                        rfl

theorem cell23_553621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_553621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553621 prefixEnd_553621 := by exact prefixLift 553621
  have htrace : WordTrace (prefixWord ++ tailWord_553621) baseStart_553621 baseEnd_553621 := by
    simpa [prefixWord, tailWord_553621, baseEnd_553621] using wordTrace_append hprefix tailTrace_553621
  have hstable : (prefixWord ++ tailWord_553621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553621).length < 2 ^ (prefixWord ++ tailWord_553621).sum := by decide
  have hdescent : baseEnd_553621 < baseStart_553621 := by decide
  rcases family_descends (prefixWord ++ tailWord_553621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553628 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_553628 : Nat := 118140960795 + 553628 * 2 ^ 59
def prefixEnd_553628 : Nat := 4983230072969 + 3 ^ 40 * 553628 * 2
def baseEnd_553628 : Nat := 284277267787465161603917

theorem tailTrace_553628 : CollatzResearch.WordTrace tailWord_553628 prefixEnd_553628 284277267787465161603917 := by
  unfold tailWord_553628
  simp only [CollatzResearch.WordTrace]
  refine ⟨10096236019153891489914769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13461648025538521986553025 10096236019153891489914769)
  ·
    refine ⟨7572177014365418617436077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10096236019153891489914769 7572177014365418617436077)
    ·
      refine ⟨2839566380387031981538529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7572177014365418617436077 2839566380387031981538529)
      ·
        refine ⟨2129674785290273986153897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2839566380387031981538529 2129674785290273986153897)
        ·
          refine ⟨1597256088967705489615423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2129674785290273986153897 1597256088967705489615423)
          ·
            refine ⟨2395884133451558234423135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597256088967705489615423 2395884133451558234423135)
            ·
              refine ⟨3593826200177337351634703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2395884133451558234423135 3593826200177337351634703)
              ·
                refine ⟨5390739300266006027452055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3593826200177337351634703 5390739300266006027452055)
                ·
                  refine ⟨8086108950399009041178083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5390739300266006027452055 8086108950399009041178083)
                  ·
                    refine ⟨12129163425598513561767125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8086108950399009041178083 12129163425598513561767125)
                    ·
                      refine ⟨284277267787465161603917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12129163425598513561767125 284277267787465161603917)
                      ·
                        rfl

theorem cell23_553628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_553628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553628 prefixEnd_553628 := by exact prefixLift 553628
  have htrace : WordTrace (prefixWord ++ tailWord_553628) baseStart_553628 baseEnd_553628 := by
    simpa [prefixWord, tailWord_553628, baseEnd_553628] using wordTrace_append hprefix tailTrace_553628
  have hstable : (prefixWord ++ tailWord_553628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553628).length < 2 ^ (prefixWord ++ tailWord_553628).sum := by decide
  have hdescent : baseEnd_553628 < baseStart_553628 := by decide
  rcases family_descends (prefixWord ++ tailWord_553628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553633 : List Nat := [1, 2, 3, 3, 4, 1, 2, 1, 2, 2, 2]
def baseStart_553633 : Nat := 118140960795 + 553633 * 2 ^ 59
def prefixEnd_553633 : Nat := 4983230072969 + 3 ^ 40 * 553633 * 2
def baseEnd_553633 : Nat := 284279835190737642041395

theorem tailTrace_553633 : CollatzResearch.WordTrace tailWord_553633 prefixEnd_553633 284279835190737642041395 := by
  unfold tailWord_553633
  simp only [CollatzResearch.WordTrace]
  refine ⟨20192654403289668833761553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13461769602193112555841035 20192654403289668833761553)
  ·
    refine ⟨15144490802467251625321165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20192654403289668833761553 15144490802467251625321165)
    ·
      refine ⟨5679184050925219359495437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15144490802467251625321165 5679184050925219359495437)
      ·
        refine ⟨2129694019096957259810789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5679184050925219359495437 2129694019096957259810789)
        ·
          refine ⟨399317628580679486214523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2129694019096957259810789 399317628580679486214523)
          ·
            refine ⟨598976442871019229321785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399317628580679486214523 598976442871019229321785)
            ·
              refine ⟨449232332153264421991339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598976442871019229321785 449232332153264421991339)
              ·
                refine ⟨673848498229896632987009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449232332153264421991339 673848498229896632987009)
                ·
                  refine ⟨505386373672422474740257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 673848498229896632987009 505386373672422474740257)
                  ·
                    refine ⟨379039780254316856055193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 505386373672422474740257 379039780254316856055193)
                    ·
                      refine ⟨284279835190737642041395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 379039780254316856055193 284279835190737642041395)
                      ·
                        rfl

theorem cell23_553633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_553633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553633 prefixEnd_553633 := by exact prefixLift 553633
  have htrace : WordTrace (prefixWord ++ tailWord_553633) baseStart_553633 baseEnd_553633 := by
    simpa [prefixWord, tailWord_553633, baseEnd_553633] using wordTrace_append hprefix tailTrace_553633
  have hstable : (prefixWord ++ tailWord_553633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553633).length < 2 ^ (prefixWord ++ tailWord_553633).sum := by decide
  have hdescent : baseEnd_553633 < baseStart_553633 := by decide
  rcases family_descends (prefixWord ++ tailWord_553633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553648 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 5, 4]
def baseStart_553648 : Nat := 118140960795 + 553648 * 2 ^ 59
def prefixEnd_553648 : Nat := 4983230072969 + 3 ^ 40 * 553648 * 2
def baseEnd_553648 : Nat := 94762512466851694451275

theorem tailTrace_553648 : CollatzResearch.WordTrace tailWord_553648 prefixEnd_553648 94762512466851694451275 := by
  unfold tailWord_553648
  simp only [CollatzResearch.WordTrace]
  refine ⟨10096600749117663197778799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13462134332156884263705065 10096600749117663197778799)
  ·
    refine ⟨15144901123676494796668199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10096600749117663197778799 15144901123676494796668199)
    ·
      refine ⟨22717351685514742195002299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15144901123676494796668199 22717351685514742195002299)
      ·
        refine ⟨34076027528272113292503449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22717351685514742195002299 34076027528272113292503449)
        ·
          refine ⟨25557020646204084969377587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34076027528272113292503449 25557020646204084969377587)
          ·
            refine ⟨38335530969306127454066381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25557020646204084969377587 38335530969306127454066381)
            ·
              refine ⟨14375824113489797795274893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38335530969306127454066381 14375824113489797795274893)
              ·
                refine ⟨5390934042558674173228085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14375824113489797795274893 5390934042558674173228085)
                ·
                  refine ⟨505400066489875703740133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5390934042558674173228085 505400066489875703740133)
                  ·
                    refine ⟨94762512466851694451275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 505400066489875703740133 94762512466851694451275)
                    ·
                      rfl

theorem cell23_553648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 5, 4].length) (baseStart_553648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553648 prefixEnd_553648 := by exact prefixLift 553648
  have htrace : WordTrace (prefixWord ++ tailWord_553648) baseStart_553648 baseEnd_553648 := by
    simpa [prefixWord, tailWord_553648, baseEnd_553648] using wordTrace_append hprefix tailTrace_553648
  have hstable : (prefixWord ++ tailWord_553648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553648).length < 2 ^ (prefixWord ++ tailWord_553648).sum := by decide
  have hdescent : baseEnd_553648 < baseStart_553648 := by decide
  rcases family_descends (prefixWord ++ tailWord_553648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553705 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 5, 1, 3]
def baseStart_553705 : Nat := 118140960795 + 553705 * 2 ^ 59
def prefixEnd_553705 : Nat := 4983230072969 + 3 ^ 40 * 553705 * 2
def baseEnd_553705 : Nat := 284316805797861360341063

theorem tailTrace_553705 : CollatzResearch.WordTrace tailWord_553705 prefixEnd_553705 284316805797861360341063 := by
  unfold tailWord_553705
  simp only [CollatzResearch.WordTrace]
  refine ⟨20195280459028825130382569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13463520306019216753588379 20195280459028825130382569)
  ·
    refine ⟨15146460344271618847786927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20195280459028825130382569 15146460344271618847786927)
    ·
      refine ⟨22719690516407428271680391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15146460344271618847786927 22719690516407428271680391)
      ·
        refine ⟨34079535774611142407520587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22719690516407428271680391 34079535774611142407520587)
        ·
          refine ⟨51119303661916713611280881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34079535774611142407520587 51119303661916713611280881)
          ·
            refine ⟨38339477746437535208460661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51119303661916713611280881 38339477746437535208460661)
            ·
              refine ⟨3594326038728518925793187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38339477746437535208460661 3594326038728518925793187)
              ·
                refine ⟨5391489058092778388689781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3594326038728518925793187 5391489058092778388689781)
                ·
                  refine ⟨505452099196197973939667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5391489058092778388689781 505452099196197973939667)
                  ·
                    refine ⟨758178148794296960909501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 505452099196197973939667 758178148794296960909501)
                    ·
                      refine ⟨284316805797861360341063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 758178148794296960909501 284316805797861360341063)
                      ·
                        rfl

theorem cell23_553705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 1, 3].length) (baseStart_553705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553705 prefixEnd_553705 := by exact prefixLift 553705
  have htrace : WordTrace (prefixWord ++ tailWord_553705) baseStart_553705 baseEnd_553705 := by
    simpa [prefixWord, tailWord_553705, baseEnd_553705] using wordTrace_append hprefix tailTrace_553705
  have hstable : (prefixWord ++ tailWord_553705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553705).length < 2 ^ (prefixWord ++ tailWord_553705).sum := by decide
  have hdescent : baseEnd_553705 < baseStart_553705 := by decide
  rcases family_descends (prefixWord ++ tailWord_553705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553725 : List Nat := [1, 4, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_553725 : Nat := 118140960795 + 553725 * 2 ^ 59
def prefixEnd_553725 : Nat := 4983230072969 + 3 ^ 40 * 553725 * 2
def baseEnd_553725 : Nat := 94775691803650427363657

theorem tailTrace_553725 : CollatzResearch.WordTrace tailWord_553725 prefixEnd_553725 94775691803650427363657 := by
  unfold tailWord_553725
  simp only [CollatzResearch.WordTrace]
  refine ⟨20196009918956368546110629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13464006612637579030740419 20196009918956368546110629)
  ·
    refine ⟨3786751859804319102395743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20196009918956368546110629 3786751859804319102395743)
    ·
      refine ⟨5680127789706478653593615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3786751859804319102395743 5680127789706478653593615)
      ·
        refine ⟨8520191684559717980390423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5680127789706478653593615 8520191684559717980390423)
        ·
          refine ⟨12780287526839576970585635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8520191684559717980390423 12780287526839576970585635)
          ·
            refine ⟨19170431290259365455878453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12780287526839576970585635 19170431290259365455878453)
            ·
              refine ⟨1797227933461815511488605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19170431290259365455878453 1797227933461815511488605)
              ·
                refine ⟨673960475048180816808227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1797227933461815511488605 673960475048180816808227)
                ·
                  refine ⟨1010940712572271225212341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 673960475048180816808227 1010940712572271225212341)
                  ·
                    refine ⟨94775691803650427363657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1010940712572271225212341 94775691803650427363657)
                    ·
                      rfl

theorem cell23_553725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_553725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553725 prefixEnd_553725 := by exact prefixLift 553725
  have htrace : WordTrace (prefixWord ++ tailWord_553725) baseStart_553725 baseEnd_553725 := by
    simpa [prefixWord, tailWord_553725, baseEnd_553725] using wordTrace_append hprefix tailTrace_553725
  have hstable : (prefixWord ++ tailWord_553725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553725).length < 2 ^ (prefixWord ++ tailWord_553725).sum := by decide
  have hdescent : baseEnd_553725 < baseStart_553725 := by decide
  rcases family_descends (prefixWord ++ tailWord_553725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553732 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_553732 : Nat := 118140960795 + 553732 * 2 ^ 59
def prefixEnd_553732 : Nat := 4983230072969 + 3 ^ 40 * 553732 * 2
def baseEnd_553732 : Nat := 284330669775532754703439

theorem tailTrace_553732 : CollatzResearch.WordTrace tailWord_553732 prefixEnd_553732 284330669775532754703439 := by
  unfold tailWord_553732
  simp only [CollatzResearch.WordTrace]
  refine ⟨10098132614965504370807725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13464176819954005827743633 10098132614965504370807725)
  ·
    refine ⟨3786799730612064139052897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10098132614965504370807725 3786799730612064139052897)
    ·
      refine ⟨2840099797959048104289673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3786799730612064139052897 2840099797959048104289673)
      ·
        refine ⟨2130074848469286078217255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2840099797959048104289673 2130074848469286078217255)
        ·
          refine ⟨3195112272703929117325883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2130074848469286078217255 3195112272703929117325883)
          ·
            refine ⟨4792668409055893675988825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3195112272703929117325883 4792668409055893675988825)
            ·
              refine ⟨3594501306791920256991619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4792668409055893675988825 3594501306791920256991619)
              ·
                refine ⟨5391751960187880385487429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3594501306791920256991619 5391751960187880385487429)
                ·
                  refine ⟨1010953492535227572278893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5391751960187880385487429 1010953492535227572278893)
                  ·
                    refine ⟨379107559700710339604585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1010953492535227572278893 379107559700710339604585)
                    ·
                      refine ⟨284330669775532754703439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 379107559700710339604585 284330669775532754703439)
                      ·
                        rfl

theorem cell23_553732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_553732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553732 prefixEnd_553732 := by exact prefixLift 553732
  have htrace : WordTrace (prefixWord ++ tailWord_553732) baseStart_553732 baseEnd_553732 := by
    simpa [prefixWord, tailWord_553732, baseEnd_553732] using wordTrace_append hprefix tailTrace_553732
  have hstable : (prefixWord ++ tailWord_553732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553732).length < 2 ^ (prefixWord ++ tailWord_553732).sum := by decide
  have hdescent : baseEnd_553732 < baseStart_553732 := by decide
  rcases family_descends (prefixWord ++ tailWord_553732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553762 : List Nat := [3, 3, 1, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_553762 : Nat := 118140960795 + 553762 * 2 ^ 59
def prefixEnd_553762 : Nat := 4983230072969 + 3 ^ 40 * 553762 * 2
def baseEnd_553762 : Nat := 284346074195167637328301

theorem tailTrace_553762 : CollatzResearch.WordTrace tailWord_553762 prefixEnd_553762 284346074195167637328301 := by
  unfold tailWord_553762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5049339854955580966301885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13464906279881549243471693 5049339854955580966301885)
  ·
    refine ⟨1893502445608342862363207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5049339854955580966301885 1893502445608342862363207)
    ·
      refine ⟨2840253668412514293544811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1893502445608342862363207 2840253668412514293544811)
      ·
        refine ⟨4260380502618771440317217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2840253668412514293544811 4260380502618771440317217)
        ·
          refine ⟨3195285376964078580237913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4260380502618771440317217 3195285376964078580237913)
          ·
            refine ⟨2396464032723058935178435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3195285376964078580237913 2396464032723058935178435)
            ·
              refine ⟨3594696049084588402767653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396464032723058935178435 3594696049084588402767653)
              ·
                refine ⟨674005509203360325518935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3594696049084588402767653 674005509203360325518935)
                ·
                  refine ⟨1011008263805040488278403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674005509203360325518935 1011008263805040488278403)
                  ·
                    refine ⟨1516512395707560732417605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1011008263805040488278403 1516512395707560732417605)
                    ·
                      refine ⟨284346074195167637328301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1516512395707560732417605 284346074195167637328301)
                      ·
                        rfl

theorem cell23_553762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_553762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553762 prefixEnd_553762 := by exact prefixLift 553762
  have htrace : WordTrace (prefixWord ++ tailWord_553762) baseStart_553762 baseEnd_553762 := by
    simpa [prefixWord, tailWord_553762, baseEnd_553762] using wordTrace_append hprefix tailTrace_553762
  have hstable : (prefixWord ++ tailWord_553762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553762).length < 2 ^ (prefixWord ++ tailWord_553762).sum := by decide
  have hdescent : baseEnd_553762 < baseStart_553762 := by decide
  rcases family_descends (prefixWord ++ tailWord_553762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553846 : List Nat := [5, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_553846 : Nat := 118140960795 + 553846 * 2 ^ 59
def prefixEnd_553846 : Nat := 4983230072969 + 3 ^ 40 * 553846 * 2
def baseEnd_553846 : Nat := 284389206570145308677915

theorem tailTrace_553846 : CollatzResearch.WordTrace tailWord_553846 prefixEnd_553846 284389206570145308677915 := by
  unfold tailWord_553846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1262526446969875388204087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13466948767678670807510261 1262526446969875388204087)
  ·
    refine ⟨1893789670454813082306131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1262526446969875388204087 1893789670454813082306131)
    ·
      refine ⟨2840684505682219623459197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1893789670454813082306131 2840684505682219623459197)
      ·
        refine ⟨1065256689630832358797199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2840684505682219623459197 1065256689630832358797199)
        ·
          refine ⟨1597885034446248538195799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065256689630832358797199 1597885034446248538195799)
          ·
            refine ⟨2396827551669372807293699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597885034446248538195799 2396827551669372807293699)
            ·
              refine ⟨3595241327504059210940549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396827551669372807293699 3595241327504059210940549)
              ·
                refine ⟨674107748907011102051353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3595241327504059210940549 674107748907011102051353)
                ·
                  refine ⟨505580811680258326538515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 674107748907011102051353 505580811680258326538515)
                  ·
                    refine ⟨758371217520387489807773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 505580811680258326538515 758371217520387489807773)
                    ·
                      refine ⟨284389206570145308677915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 758371217520387489807773 284389206570145308677915)
                      ·
                        rfl

theorem cell23_553846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_553846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553846 prefixEnd_553846 := by exact prefixLift 553846
  have htrace : WordTrace (prefixWord ++ tailWord_553846) baseStart_553846 baseEnd_553846 := by
    simpa [prefixWord, tailWord_553846, baseEnd_553846] using wordTrace_append hprefix tailTrace_553846
  have hstable : (prefixWord ++ tailWord_553846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553846).length < 2 ^ (prefixWord ++ tailWord_553846).sum := by decide
  have hdescent : baseEnd_553846 < baseStart_553846 := by decide
  rcases family_descends (prefixWord ++ tailWord_553846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553855 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 3]
def baseStart_553855 : Nat := 118140960795 + 553855 * 2 ^ 59
def prefixEnd_553855 : Nat := 4983230072969 + 3 ^ 40 * 553855 * 2
def baseEnd_553855 : Nat := 284393827896035773465373

theorem tailTrace_553855 : CollatzResearch.WordTrace tailWord_553855 prefixEnd_553855 284393827896035773465373 := by
  unfold tailWord_553855
  simp only [CollatzResearch.WordTrace]
  refine ⟨20200751408485400748343019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13467167605656933832228679 20200751408485400748343019)
  ·
    refine ⟨30301127112728101122514529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20200751408485400748343019 30301127112728101122514529)
    ·
      refine ⟨22725845334546075841885897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30301127112728101122514529 22725845334546075841885897)
      ·
        refine ⟨17044384000909556881414423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22725845334546075841885897 17044384000909556881414423)
        ·
          refine ⟨25566576001364335322121635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17044384000909556881414423 25566576001364335322121635)
          ·
            refine ⟨38349864002046502983182453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25566576001364335322121635 38349864002046502983182453)
            ·
              refine ⟨3595299750191859654673355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38349864002046502983182453 3595299750191859654673355)
              ·
                refine ⟨5392949625287789482010033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595299750191859654673355 5392949625287789482010033)
                ·
                  refine ⟨4044712218965842111507525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5392949625287789482010033 4044712218965842111507525)
                  ·
                    refine ⟨758383541056095395907661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4044712218965842111507525 758383541056095395907661)
                    ·
                      refine ⟨284393827896035773465373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 758383541056095395907661 284393827896035773465373)
                      ·
                        rfl

theorem cell23_553855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_553855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553855 prefixEnd_553855 := by exact prefixLift 553855
  have htrace : WordTrace (prefixWord ++ tailWord_553855) baseStart_553855 baseEnd_553855 := by
    simpa [prefixWord, tailWord_553855, baseEnd_553855] using wordTrace_append hprefix tailTrace_553855
  have hstable : (prefixWord ++ tailWord_553855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553855).length < 2 ^ (prefixWord ++ tailWord_553855).sum := by decide
  have hdescent : baseEnd_553855 < baseStart_553855 := by decide
  rcases family_descends (prefixWord ++ tailWord_553855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553865 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 1, 4, 4]
def baseStart_553865 : Nat := 118140960795 + 553865 * 2 ^ 59
def prefixEnd_553865 : Nat := 4983230072969 + 3 ^ 40 * 553865 * 2
def baseEnd_553865 : Nat := 284398962702580734340327

theorem tailTrace_553865 : CollatzResearch.WordTrace tailWord_553865 prefixEnd_553865 284398962702580734340327 := by
  unfold tailWord_553865
  simp only [CollatzResearch.WordTrace]
  refine ⟨20201116138449172456207049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13467410758966114970804699 20201116138449172456207049)
  ·
    refine ⟨15150837103836879342155287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20201116138449172456207049 15150837103836879342155287)
    ·
      refine ⟨22726255655755319013232931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15150837103836879342155287 22726255655755319013232931)
      ·
        refine ⟨34089383483632978519849397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22726255655755319013232931 34089383483632978519849397)
        ·
          refine ⟨3195879701590591736235881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34089383483632978519849397 3195879701590591736235881)
          ·
            refine ⟨2396909776192943802176911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3195879701590591736235881 2396909776192943802176911)
            ·
              refine ⟨3595364664289415703265367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396909776192943802176911 3595364664289415703265367)
              ·
                refine ⟨5393046996434123554898051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595364664289415703265367 5393046996434123554898051)
                ·
                  refine ⟨8089570494651185332347077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5393046996434123554898051 8089570494651185332347077)
                  ·
                    refine ⟨1516794467747097249815077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8089570494651185332347077 1516794467747097249815077)
                    ·
                      refine ⟨284398962702580734340327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1516794467747097249815077 284398962702580734340327)
                      ·
                        rfl

theorem cell23_553865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_553865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553865 prefixEnd_553865 := by exact prefixLift 553865
  have htrace : WordTrace (prefixWord ++ tailWord_553865) baseStart_553865 baseEnd_553865 := by
    simpa [prefixWord, tailWord_553865, baseEnd_553865] using wordTrace_append hprefix tailTrace_553865
  have hstable : (prefixWord ++ tailWord_553865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553865).length < 2 ^ (prefixWord ++ tailWord_553865).sum := by decide
  have hdescent : baseEnd_553865 < baseStart_553865 := by decide
  rcases family_descends (prefixWord ++ tailWord_553865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553959 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_553959 : Nat := 118140960795 + 553959 * 2 ^ 59
def prefixEnd_553959 : Nat := 4983230072969 + 3 ^ 40 * 553959 * 2
def baseEnd_553959 : Nat := 284447229884103366564895

theorem tailTrace_553959 : CollatzResearch.WordTrace tailWord_553959 prefixEnd_553959 284447229884103366564895 := by
  unfold tailWord_553959
  simp only [CollatzResearch.WordTrace]
  refine ⟨20204544600108626510128931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13469696400072417673419287 20204544600108626510128931)
  ·
    refine ⟨30306816900162939765193397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20204544600108626510128931 30306816900162939765193397)
    ·
      refine ⟨2841264084390275602986881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30306816900162939765193397 2841264084390275602986881)
      ·
        refine ⟨2130948063292706702240161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2841264084390275602986881 2130948063292706702240161)
        ·
          refine ⟨1598211047469530026680121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2130948063292706702240161 1598211047469530026680121)
          ·
            refine ⟨1198658285602147520010091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1598211047469530026680121 1198658285602147520010091)
            ·
              refine ⟨1797987428403221280015137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198658285602147520010091 1797987428403221280015137)
              ·
                refine ⟨1348490571302415960011353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1797987428403221280015137 1348490571302415960011353)
                ·
                  refine ⟨1011367928476811970008515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1348490571302415960011353 1011367928476811970008515)
                  ·
                    refine ⟨1517051892715217955012773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1011367928476811970008515 1517051892715217955012773)
                    ·
                      refine ⟨284447229884103366564895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1517051892715217955012773 284447229884103366564895)
                      ·
                        rfl

theorem cell23_553959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_553959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553959 prefixEnd_553959 := by exact prefixLift 553959
  have htrace : WordTrace (prefixWord ++ tailWord_553959) baseStart_553959 baseEnd_553959 := by
    simpa [prefixWord, tailWord_553959, baseEnd_553959] using wordTrace_append hprefix tailTrace_553959
  have hstable : (prefixWord ++ tailWord_553959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553959).length < 2 ^ (prefixWord ++ tailWord_553959).sum := by decide
  have hdescent : baseEnd_553959 < baseStart_553959 := by decide
  rcases family_descends (prefixWord ++ tailWord_553959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553969 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 3, 4]
def baseStart_553969 : Nat := 118140960795 + 553969 * 2 ^ 59
def prefixEnd_553969 : Nat := 4983230072969 + 3 ^ 40 * 553969 * 2
def baseEnd_553969 : Nat := 94817454896882775813283

theorem tailTrace_553969 : CollatzResearch.WordTrace tailWord_553969 prefixEnd_553969 94817454896882775813283 := by
  unfold tailWord_553969
  simp only [CollatzResearch.WordTrace]
  refine ⟨20204909330072398217992961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13469939553381598811995307 20204909330072398217992961)
  ·
    refine ⟨15153681997554298663494721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20204909330072398217992961 15153681997554298663494721)
    ·
      refine ⟨11365261498165723997621041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15153681997554298663494721 11365261498165723997621041)
      ·
        refine ⟨8523946123624292998215781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11365261498165723997621041 8523946123624292998215781)
        ·
          refine ⟨1598239898179554937165459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8523946123624292998215781 1598239898179554937165459)
          ·
            refine ⟨2397359847269332405748189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598239898179554937165459 2397359847269332405748189)
            ·
              refine ⟨899009942725999652155571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2397359847269332405748189 899009942725999652155571)
              ·
                refine ⟨1348514914088999478233357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899009942725999652155571 1348514914088999478233357)
                ·
                  refine ⟨505693092783374804337509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1348514914088999478233357 505693092783374804337509)
                  ·
                    refine ⟨94817454896882775813283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 505693092783374804337509 94817454896882775813283)
                    ·
                      rfl

theorem cell23_553969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_553969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_553969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_553969 prefixEnd_553969 := by exact prefixLift 553969
  have htrace : WordTrace (prefixWord ++ tailWord_553969) baseStart_553969 baseEnd_553969 := by
    simpa [prefixWord, tailWord_553969, baseEnd_553969] using wordTrace_append hprefix tailTrace_553969
  have hstable : (prefixWord ++ tailWord_553969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553969).length < 2 ^ (prefixWord ++ tailWord_553969).sum := by decide
  have hdescent : baseEnd_553969 < baseStart_553969 := by decide
  rcases family_descends (prefixWord ++ tailWord_553969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554016 : List Nat := [2, 1, 1, 7, 1, 1, 2, 2, 6]
def baseStart_554016 : Nat := 118140960795 + 554016 * 2 ^ 59
def prefixEnd_554016 : Nat := 4983230072969 + 3 ^ 40 * 554016 * 2
def baseEnd_554016 : Nat := 31608499809045515950237

theorem tailTrace_554016 : CollatzResearch.WordTrace tailWord_554016 prefixEnd_554016 31608499809045515950237 := by
  unfold tailWord_554016
  simp only [CollatzResearch.WordTrace]
  refine ⟨10103311780451062622476951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13471082373934750163302601 10103311780451062622476951)
  ·
    refine ⟨15154967670676593933715427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10103311780451062622476951 15154967670676593933715427)
    ·
      refine ⟨22732451506014890900573141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15154967670676593933715427 22732451506014890900573141)
      ·
        refine ⟨532791832172224005482183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 22732451506014890900573141 532791832172224005482183)
        ·
          refine ⟨799187748258336008223275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532791832172224005482183 799187748258336008223275)
          ·
            refine ⟨1198781622387504012334913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799187748258336008223275 1198781622387504012334913)
            ·
              refine ⟨899086216790628009251185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1198781622387504012334913 899086216790628009251185)
              ·
                refine ⟨674314662592971006938389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 899086216790628009251185 674314662592971006938389)
                ·
                  refine ⟨31608499809045515950237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 674314662592971006938389 31608499809045515950237)
                  ·
                    rfl

theorem cell23_554016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 6].length) (baseStart_554016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554016 prefixEnd_554016 := by exact prefixLift 554016
  have htrace : WordTrace (prefixWord ++ tailWord_554016) baseStart_554016 baseEnd_554016 := by
    simpa [prefixWord, tailWord_554016, baseEnd_554016] using wordTrace_append hprefix tailTrace_554016
  have hstable : (prefixWord ++ tailWord_554016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554016).length < 2 ^ (prefixWord ++ tailWord_554016).sum := by decide
  have hdescent : baseEnd_554016 < baseStart_554016 := by decide
  rcases family_descends (prefixWord ++ tailWord_554016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554020 : List Nat := [2, 3, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_554020 : Nat := 118140960795 + 554020 * 2 ^ 59
def prefixEnd_554020 : Nat := 4983230072969 + 3 ^ 40 * 554020 * 2
def baseEnd_554020 : Nat := 94826184068009209300705

theorem tailTrace_554020 : CollatzResearch.WordTrace tailWord_554020 prefixEnd_554020 94826184068009209300705 := by
  unfold tailWord_554020
  simp only [CollatzResearch.WordTrace]
  refine ⟨10103384726443816964049757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13471179635258422618733009 10103384726443816964049757)
  ·
    refine ⟨3788769272416431361518659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10103384726443816964049757 3788769272416431361518659)
    ·
      refine ⟨5683153908624647042277989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3788769272416431361518659 5683153908624647042277989)
      ·
        refine ⟨1065591357867121320427123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5683153908624647042277989 1065591357867121320427123)
        ·
          refine ⟨1598387036800681980640685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065591357867121320427123 1598387036800681980640685)
          ·
            refine ⟨599395138800255742740257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1598387036800681980640685 599395138800255742740257)
            ·
              refine ⟨449546354100191807055193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 599395138800255742740257 449546354100191807055193)
              ·
                refine ⟨337159765575143855291395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449546354100191807055193 337159765575143855291395)
                ·
                  refine ⟨505739648362715782937093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337159765575143855291395 505739648362715782937093)
                  ·
                    refine ⟨94826184068009209300705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 505739648362715782937093 94826184068009209300705)
                    ·
                      rfl

theorem cell23_554020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_554020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554020 prefixEnd_554020 := by exact prefixLift 554020
  have htrace : WordTrace (prefixWord ++ tailWord_554020) baseStart_554020 baseEnd_554020 := by
    simpa [prefixWord, tailWord_554020, baseEnd_554020] using wordTrace_append hprefix tailTrace_554020
  have hstable : (prefixWord ++ tailWord_554020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554020).length < 2 ^ (prefixWord ++ tailWord_554020).sum := by decide
  have hdescent : baseEnd_554020 < baseStart_554020 := by decide
  rcases family_descends (prefixWord ++ tailWord_554020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554032 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 4]
def baseStart_554032 : Nat := 118140960795 + 554032 * 2 ^ 59
def prefixEnd_554032 : Nat := 4983230072969 + 3 ^ 40 * 554032 * 2
def baseEnd_554032 : Nat := 284484713971881580952059

theorem tailTrace_554032 : CollatzResearch.WordTrace tailWord_554032 prefixEnd_554032 284484713971881580952059 := by
  unfold tailWord_554032
  simp only [CollatzResearch.WordTrace]
  refine ⟨10103603564422079988768175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13471471419229439985024233 10103603564422079988768175)
  ·
    refine ⟨15155405346633119983152263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10103603564422079988768175 15155405346633119983152263)
    ·
      refine ⟨22733108019949679974728395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15155405346633119983152263 22733108019949679974728395)
      ·
        refine ⟨34099662029924519962092593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22733108019949679974728395 34099662029924519962092593)
        ·
          refine ⟨25574746522443389971569445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34099662029924519962092593 25574746522443389971569445)
          ·
            refine ⟨4795264972958135619669271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25574746522443389971569445 4795264972958135619669271)
            ·
              refine ⟨7192897459437203429503907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4795264972958135619669271 7192897459437203429503907)
              ·
                refine ⟨10789346189155805144255861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7192897459437203429503907 10789346189155805144255861)
                ·
                  refine ⟨1011501205233356732273987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10789346189155805144255861 1011501205233356732273987)
                  ·
                    refine ⟨1517251807850035098410981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1011501205233356732273987 1517251807850035098410981)
                    ·
                      refine ⟨284484713971881580952059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1517251807850035098410981 284484713971881580952059)
                      ·
                        rfl

theorem cell23_554032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_554032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554032 prefixEnd_554032 := by exact prefixLift 554032
  have htrace : WordTrace (prefixWord ++ tailWord_554032) baseStart_554032 baseEnd_554032 := by
    simpa [prefixWord, tailWord_554032, baseEnd_554032] using wordTrace_append hprefix tailTrace_554032
  have hstable : (prefixWord ++ tailWord_554032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554032).length < 2 ^ (prefixWord ++ tailWord_554032).sum := by decide
  have hdescent : baseEnd_554032 < baseStart_554032 := by decide
  rcases family_descends (prefixWord ++ tailWord_554032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554042 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 1, 6]
def baseStart_554042 : Nat := 118140960795 + 554042 * 2 ^ 59
def prefixEnd_554042 : Nat := 4983230072969 + 3 ^ 40 * 554042 * 2
def baseEnd_554042 : Nat := 94829949592808847275671

theorem tailTrace_554042 : CollatzResearch.WordTrace tailWord_554042 prefixEnd_554042 94829949592808847275671 := by
  unfold tailWord_554042
  simp only [CollatzResearch.WordTrace]
  refine ⟨5051892964701982921350095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13471714572538621123600253 5051892964701982921350095)
  ·
    refine ⟨7577839447052974382025143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5051892964701982921350095 7577839447052974382025143)
    ·
      refine ⟨11366759170579461573037715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7577839447052974382025143 11366759170579461573037715)
      ·
        refine ⟨17050138755869192359556573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11366759170579461573037715 17050138755869192359556573)
        ·
          refine ⟨6393802033450947134833715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17050138755869192359556573 6393802033450947134833715)
          ·
            refine ⟨9590703050176420702250573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6393802033450947134833715 9590703050176420702250573)
            ·
              refine ⟨3596513643816157763343965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9590703050176420702250573 3596513643816157763343965)
              ·
                refine ⟨1348692616431059161253987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3596513643816157763343965 1348692616431059161253987)
                ·
                  refine ⟨2023038924646588741880981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348692616431059161253987 2023038924646588741880981)
                  ·
                    refine ⟨94829949592808847275671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2023038924646588741880981 94829949592808847275671)
                    ·
                      rfl

theorem cell23_554042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_554042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554042 prefixEnd_554042 := by exact prefixLift 554042
  have htrace : WordTrace (prefixWord ++ tailWord_554042) baseStart_554042 baseEnd_554042 := by
    simpa [prefixWord, tailWord_554042, baseEnd_554042] using wordTrace_append hprefix tailTrace_554042
  have hstable : (prefixWord ++ tailWord_554042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554042).length < 2 ^ (prefixWord ++ tailWord_554042).sum := by decide
  have hdescent : baseEnd_554042 < baseStart_554042 := by decide
  rcases family_descends (prefixWord ++ tailWord_554042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554066 : List Nat := [3, 2, 2, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_554066 : Nat := 118140960795 + 554066 * 2 ^ 59
def prefixEnd_554066 : Nat := 4983230072969 + 3 ^ 40 * 554066 * 2
def baseEnd_554066 : Nat := 284502172314134447926903

theorem tailTrace_554066 : CollatzResearch.WordTrace tailWord_554066 prefixEnd_554066 284502172314134447926903 := by
  unfold tailWord_554066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5052111802680245946068513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13472298140480655856182701 5052111802680245946068513)
  ·
    refine ⟨3789083852010184459551385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5052111802680245946068513 3789083852010184459551385)
    ·
      refine ⟨2841812889007638344663539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3789083852010184459551385 2841812889007638344663539)
      ·
        refine ⟨4262719333511457516995309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2841812889007638344663539 4262719333511457516995309)
        ·
          refine ⟨1598519750066796568873241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4262719333511457516995309 1598519750066796568873241)
          ·
            refine ⟨1198889812550097426654931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1598519750066796568873241 1198889812550097426654931)
            ·
              refine ⟨1798334718825146139982397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198889812550097426654931 1798334718825146139982397)
              ·
                refine ⟨674375519559429802493399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1798334718825146139982397 674375519559429802493399)
                ·
                  refine ⟨1011563279339144703740099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674375519559429802493399 1011563279339144703740099)
                  ·
                    refine ⟨1517344919008717055610149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1011563279339144703740099 1517344919008717055610149)
                    ·
                      refine ⟨284502172314134447926903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1517344919008717055610149 284502172314134447926903)
                      ·
                        rfl

theorem cell23_554066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_554066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554066 prefixEnd_554066 := by exact prefixLift 554066
  have htrace : WordTrace (prefixWord ++ tailWord_554066) baseStart_554066 baseEnd_554066 := by
    simpa [prefixWord, tailWord_554066, baseEnd_554066] using wordTrace_append hprefix tailTrace_554066
  have hstable : (prefixWord ++ tailWord_554066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554066).length < 2 ^ (prefixWord ++ tailWord_554066).sum := by decide
  have hdescent : baseEnd_554066 < baseStart_554066 := by decide
  rcases family_descends (prefixWord ++ tailWord_554066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554093 : List Nat := [1, 5, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_554093 : Nat := 118140960795 + 554093 * 2 ^ 59
def prefixEnd_554093 : Nat := 4983230072969 + 3 ^ 40 * 554093 * 2
def baseEnd_554093 : Nat := 94838678763935280763093

theorem tailTrace_554093 : CollatzResearch.WordTrace tailWord_554093 prefixEnd_554093 94838678763935280763093 := by
  unfold tailWord_554093
  simp only [CollatzResearch.WordTrace]
  refine ⟨20209431981623167395506933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13472954654415444930337955 20209431981623167395506933)
  ·
    refine ⟨1894634248277171943328775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20209431981623167395506933 1894634248277171943328775)
    ·
      refine ⟨2841951372415757914993163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1894634248277171943328775 2841951372415757914993163)
      ·
        refine ⟨4262927058623636872489745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2841951372415757914993163 4262927058623636872489745)
        ·
          refine ⟨3197195293967727654367309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4262927058623636872489745 3197195293967727654367309)
          ·
            refine ⟨1198948235237897870387741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3197195293967727654367309 1198948235237897870387741)
            ·
              refine ⟨449605588214211701395403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1198948235237897870387741 449605588214211701395403)
              ·
                refine ⟨674408382321317552093105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449605588214211701395403 674408382321317552093105)
                ·
                  refine ⟨505806286740988164069829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 674408382321317552093105 505806286740988164069829)
                  ·
                    refine ⟨94838678763935280763093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 505806286740988164069829 94838678763935280763093)
                    ·
                      rfl

theorem cell23_554093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_554093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554093 prefixEnd_554093 := by exact prefixLift 554093
  have htrace : WordTrace (prefixWord ++ tailWord_554093) baseStart_554093 baseEnd_554093 := by
    simpa [prefixWord, tailWord_554093, baseEnd_554093] using wordTrace_append hprefix tailTrace_554093
  have hstable : (prefixWord ++ tailWord_554093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554093).length < 2 ^ (prefixWord ++ tailWord_554093).sum := by decide
  have hdescent : baseEnd_554093 < baseStart_554093 := by decide
  rcases family_descends (prefixWord ++ tailWord_554093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554112 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 5]
def baseStart_554112 : Nat := 118140960795 + 554112 * 2 ^ 59
def prefixEnd_554112 : Nat := 4983230072969 + 3 ^ 40 * 554112 * 2
def baseEnd_554112 : Nat := 284525792424241267951691

theorem tailTrace_554112 : CollatzResearch.WordTrace tailWord_554112 prefixEnd_554112 284525792424241267951691 := by
  unfold tailWord_554112
  simp only [CollatzResearch.WordTrace]
  refine ⟨10105062484277166820224295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13473416645702889093632393 10105062484277166820224295)
  ·
    refine ⟨15157593726415750230336443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10105062484277166820224295 15157593726415750230336443)
    ·
      refine ⟨22736390589623625345504665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15157593726415750230336443 22736390589623625345504665)
      ·
        refine ⟨17052292942217719009128499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22736390589623625345504665 17052292942217719009128499)
        ·
          refine ⟨25578439413326578513692749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17052292942217719009128499 25578439413326578513692749)
          ·
            refine ⟨9591914779997466942634781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25578439413326578513692749 9591914779997466942634781)
            ·
              refine ⟨3596968042499050103488043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9591914779997466942634781 3596968042499050103488043)
              ·
                refine ⟨5395452063748575155232065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596968042499050103488043 5395452063748575155232065)
                ·
                  refine ⟨4046589047811431366424049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5395452063748575155232065 4046589047811431366424049)
                  ·
                    refine ⟨3034941785858573524818037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4046589047811431366424049 3034941785858573524818037)
                    ·
                      refine ⟨284525792424241267951691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3034941785858573524818037 284525792424241267951691)
                      ·
                        rfl

theorem cell23_554112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_554112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554112 prefixEnd_554112 := by exact prefixLift 554112
  have htrace : WordTrace (prefixWord ++ tailWord_554112) baseStart_554112 baseEnd_554112 := by
    simpa [prefixWord, tailWord_554112, baseEnd_554112] using wordTrace_append hprefix tailTrace_554112
  have hstable : (prefixWord ++ tailWord_554112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554112).length < 2 ^ (prefixWord ++ tailWord_554112).sum := by decide
  have hdescent : baseEnd_554112 < baseStart_554112 := by decide
  rcases family_descends (prefixWord ++ tailWord_554112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554116 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_554116 : Nat := 118140960795 + 554116 * 2 ^ 59
def prefixEnd_554116 : Nat := 4983230072969 + 3 ^ 40 * 554116 * 2
def baseEnd_554116 : Nat := 284527846346859252301673

theorem tailTrace_554116 : CollatzResearch.WordTrace tailWord_554116 prefixEnd_554116 284527846346859252301673 := by
  unfold tailWord_554116
  simp only [CollatzResearch.WordTrace]
  refine ⟨10105135430269921161797101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13473513907026561549062801 10105135430269921161797101)
  ·
    refine ⟨3789425786351220435673913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10105135430269921161797101 3789425786351220435673913)
    ·
      refine ⟨2842069339763415326755435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3789425786351220435673913 2842069339763415326755435)
      ·
        refine ⟨4263104009645122990133153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2842069339763415326755435 4263104009645122990133153)
        ·
          refine ⟨3197328007233842242599865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4263104009645122990133153 3197328007233842242599865)
          ·
            refine ⟨2397996005425381681949899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3197328007233842242599865 2397996005425381681949899)
            ·
              refine ⟨3596994008138072522924849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397996005425381681949899 3596994008138072522924849)
              ·
                refine ⟨2697745506103554392193637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3596994008138072522924849 2697745506103554392193637)
                ·
                  refine ⟨505827282394416448536307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2697745506103554392193637 505827282394416448536307)
                  ·
                    refine ⟨758740923591624672804461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 505827282394416448536307 758740923591624672804461)
                    ·
                      refine ⟨284527846346859252301673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 758740923591624672804461 284527846346859252301673)
                      ·
                        rfl

theorem cell23_554116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_554116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554116 prefixEnd_554116 := by exact prefixLift 554116
  have htrace : WordTrace (prefixWord ++ tailWord_554116) baseStart_554116 baseEnd_554116 := by
    simpa [prefixWord, tailWord_554116, baseEnd_554116] using wordTrace_append hprefix tailTrace_554116
  have hstable : (prefixWord ++ tailWord_554116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554116).length < 2 ^ (prefixWord ++ tailWord_554116).sum := by decide
  have hdescent : baseEnd_554116 < baseStart_554116 := by decide
  rcases family_descends (prefixWord ++ tailWord_554116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554117 : List Nat := [1, 3, 1, 1, 6, 2, 1, 3, 1, 2, 2]
def baseStart_554117 : Nat := 118140960795 + 554117 * 2 ^ 59
def prefixEnd_554117 : Nat := 4983230072969 + 3 ^ 40 * 554117 * 2
def baseEnd_554117 : Nat := 284528359827513748389169

theorem tailTrace_554117 : CollatzResearch.WordTrace tailWord_554117 prefixEnd_554117 284528359827513748389169 := by
  unfold tailWord_554117
  simp only [CollatzResearch.WordTrace]
  refine ⟨20210307333536219494380605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13473538222357479662920403 20210307333536219494380605)
  ·
    refine ⟨7578865250076082310392727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20210307333536219494380605 7578865250076082310392727)
    ·
      refine ⟨11368297875114123465589091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7578865250076082310392727 11368297875114123465589091)
      ·
        refine ⟨17052446812671185198383637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11368297875114123465589091 17052446812671185198383637)
        ·
          refine ⟨799333444343961806174233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17052446812671185198383637 799333444343961806174233)
          ·
            refine ⟨599500083257971354630675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 799333444343961806174233 599500083257971354630675)
            ·
              refine ⟨899250124886957031946013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599500083257971354630675 899250124886957031946013)
              ·
                refine ⟨337218796832608886979755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 899250124886957031946013 337218796832608886979755)
                ·
                  refine ⟨505828195248913330469633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337218796832608886979755 505828195248913330469633)
                  ·
                    refine ⟨379371146436684997852225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 505828195248913330469633 379371146436684997852225)
                    ·
                      refine ⟨284528359827513748389169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 379371146436684997852225 284528359827513748389169)
                      ·
                        rfl

theorem cell23_554117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 1, 2, 2].length) (baseStart_554117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554117 prefixEnd_554117 := by exact prefixLift 554117
  have htrace : WordTrace (prefixWord ++ tailWord_554117) baseStart_554117 baseEnd_554117 := by
    simpa [prefixWord, tailWord_554117, baseEnd_554117] using wordTrace_append hprefix tailTrace_554117
  have hstable : (prefixWord ++ tailWord_554117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554117).length < 2 ^ (prefixWord ++ tailWord_554117).sum := by decide
  have hdescent : baseEnd_554117 < baseStart_554117 := by decide
  rcases family_descends (prefixWord ++ tailWord_554117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554156 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 6, 2, 2]
def baseStart_554156 : Nat := 118140960795 + 554156 * 2 ^ 59
def prefixEnd_554156 : Nat := 4983230072969 + 3 ^ 40 * 554156 * 2
def baseEnd_554156 : Nat := 284548385573039095801489

theorem tailTrace_554156 : CollatzResearch.WordTrace tailWord_554156 prefixEnd_554156 284548385573039095801489 := by
  unfold tailWord_554156
  simp only [CollatzResearch.WordTrace]
  refine ⟨10105864890197464577525161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13474486520263286103366881 10105864890197464577525161)
  ·
    refine ⟨7579398667648098433143871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10105864890197464577525161 7579398667648098433143871)
    ·
      refine ⟨11369098001472147649715807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7579398667648098433143871 11369098001472147649715807)
      ·
        refine ⟨17053647002208221474573711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11369098001472147649715807 17053647002208221474573711)
        ·
          refine ⟨25580470503312332211860567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17053647002208221474573711 25580470503312332211860567)
          ·
            refine ⟨38370705754968498317790851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25580470503312332211860567 38370705754968498317790851)
            ·
              refine ⟨57556058632452747476686277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38370705754968498317790851 57556058632452747476686277)
              ·
                refine ⟨10791760993584890151878677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57556058632452747476686277 10791760993584890151878677)
                ·
                  refine ⟨505863796574291725869313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10791760993584890151878677 505863796574291725869313)
                  ·
                    refine ⟨379397847430718794401985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 505863796574291725869313 379397847430718794401985)
                    ·
                      refine ⟨284548385573039095801489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 379397847430718794401985 284548385573039095801489)
                      ·
                        rfl

theorem cell23_554156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 2, 2].length) (baseStart_554156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554156 prefixEnd_554156 := by exact prefixLift 554156
  have htrace : WordTrace (prefixWord ++ tailWord_554156) baseStart_554156 baseEnd_554156 := by
    simpa [prefixWord, tailWord_554156, baseEnd_554156] using wordTrace_append hprefix tailTrace_554156
  have hstable : (prefixWord ++ tailWord_554156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554156).length < 2 ^ (prefixWord ++ tailWord_554156).sum := by decide
  have hdescent : baseEnd_554156 < baseStart_554156 := by decide
  rcases family_descends (prefixWord ++ tailWord_554156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554177 : List Nat := [1, 2, 6, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_554177 : Nat := 118140960795 + 554177 * 2 ^ 59
def prefixEnd_554177 : Nat := 4983230072969 + 3 ^ 40 * 554177 * 2
def baseEnd_554177 : Nat := 284559168666783513638893

theorem tailTrace_554177 : CollatzResearch.WordTrace tailWord_554177 prefixEnd_554177 284559168666783513638893 := by
  unfold tailWord_554177
  simp only [CollatzResearch.WordTrace]
  refine ⟨20212495713318849741564785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13474997142212566494376523 20212495713318849741564785)
  ·
    refine ⟨15159371784989137306173589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20212495713318849741564785 15159371784989137306173589)
    ·
      refine ⟨710595552421365811226887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15159371784989137306173589 710595552421365811226887)
      ·
        refine ⟨1065893328632048716840331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710595552421365811226887 1065893328632048716840331)
        ·
          refine ⟨1598839992948073075260497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065893328632048716840331 1598839992948073075260497)
          ·
            refine ⟨1199129994711054806445373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1598839992948073075260497 1199129994711054806445373)
            ·
              refine ⟨449673748016645552417015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1199129994711054806445373 449673748016645552417015)
              ·
                refine ⟨674510622024968328625523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449673748016645552417015 674510622024968328625523)
                ·
                  refine ⟨1011765933037452492938285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674510622024968328625523 1011765933037452492938285)
                  ·
                    refine ⟨379412224889044684851857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1011765933037452492938285 379412224889044684851857)
                    ·
                      refine ⟨284559168666783513638893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 379412224889044684851857 284559168666783513638893)
                      ·
                        rfl

theorem cell23_554177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_554177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554177 prefixEnd_554177 := by exact prefixLift 554177
  have htrace : WordTrace (prefixWord ++ tailWord_554177) baseStart_554177 baseEnd_554177 := by
    simpa [prefixWord, tailWord_554177, baseEnd_554177] using wordTrace_append hprefix tailTrace_554177
  have hstable : (prefixWord ++ tailWord_554177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554177).length < 2 ^ (prefixWord ++ tailWord_554177).sum := by decide
  have hdescent : baseEnd_554177 < baseStart_554177 := by decide
  rcases family_descends (prefixWord ++ tailWord_554177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554216 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_554216 : Nat := 118140960795 + 554216 * 2 ^ 59
def prefixEnd_554216 : Nat := 4983230072969 + 3 ^ 40 * 554216 * 2
def baseEnd_554216 : Nat := 284579194412308861051213

theorem tailTrace_554216 : CollatzResearch.WordTrace tailWord_554216 prefixEnd_554216 284579194412308861051213 := by
  unfold tailWord_554216
  simp only [CollatzResearch.WordTrace]
  refine ⟨10106959080088779701117251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13475945440118372934823001 10106959080088779701117251)
  ·
    refine ⟨15160438620133169551675877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10106959080088779701117251 15160438620133169551675877)
    ·
      refine ⟨2842582241274969290939227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15160438620133169551675877 2842582241274969290939227)
      ·
        refine ⟨4263873361912453936408841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2842582241274969290939227 4263873361912453936408841)
        ·
          refine ⟨3197905021434340452306631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4263873361912453936408841 3197905021434340452306631)
          ·
            refine ⟨4796857532151510678459947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3197905021434340452306631 4796857532151510678459947)
            ·
              refine ⟨7195286298227266017689921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4796857532151510678459947 7195286298227266017689921)
              ·
                refine ⟨5396464723670449513267441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7195286298227266017689921 5396464723670449513267441)
                ·
                  refine ⟨4047348542752837134950581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5396464723670449513267441 4047348542752837134950581)
                  ·
                    refine ⟨379438925883078481401617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4047348542752837134950581 379438925883078481401617)
                    ·
                      refine ⟨284579194412308861051213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 379438925883078481401617 284579194412308861051213)
                      ·
                        rfl

theorem cell23_554216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_554216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554216 prefixEnd_554216 := by exact prefixLift 554216
  have htrace : WordTrace (prefixWord ++ tailWord_554216) baseStart_554216 baseEnd_554216 := by
    simpa [prefixWord, tailWord_554216, baseEnd_554216] using wordTrace_append hprefix tailTrace_554216
  have hstable : (prefixWord ++ tailWord_554216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554216).length < 2 ^ (prefixWord ++ tailWord_554216).sum := by decide
  have hdescent : baseEnd_554216 < baseStart_554216 := by decide
  rcases family_descends (prefixWord ++ tailWord_554216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554226 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_554226 : Nat := 118140960795 + 554226 * 2 ^ 59
def prefixEnd_554226 : Nat := 4983230072969 + 3 ^ 40 * 554226 * 2
def baseEnd_554226 : Nat := 94861443072951273975389

theorem tailTrace_554226 : CollatzResearch.WordTrace tailWord_554226 prefixEnd_554226 94861443072951273975389 := by
  unfold tailWord_554226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053570722535332777524633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13476188593427554073399021 5053570722535332777524633)
  ·
    refine ⟨3790178041901499583143475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5053570722535332777524633 3790178041901499583143475)
    ·
      refine ⟨5685267062852249374715213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3790178041901499583143475 5685267062852249374715213)
      ·
        refine ⟨2131975148569593515518205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5685267062852249374715213 2131975148569593515518205)
        ·
          refine ⟨799490680713597568319327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2131975148569593515518205 799490680713597568319327)
          ·
            refine ⟨1199236021070396352478991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799490680713597568319327 1199236021070396352478991)
            ·
              refine ⟨1798854031605594528718487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199236021070396352478991 1798854031605594528718487)
              ·
                refine ⟨2698281047408391793077731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1798854031605594528718487 2698281047408391793077731)
                ·
                  refine ⟨4047421571112587689616597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2698281047408391793077731 4047421571112587689616597)
                  ·
                    refine ⟨94861443072951273975389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4047421571112587689616597 94861443072951273975389)
                    ·
                      rfl

theorem cell23_554226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_554226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554226 prefixEnd_554226 := by exact prefixLift 554226
  have htrace : WordTrace (prefixWord ++ tailWord_554226) baseStart_554226 baseEnd_554226 := by
    simpa [prefixWord, tailWord_554226, baseEnd_554226] using wordTrace_append hprefix tailTrace_554226
  have hstable : (prefixWord ++ tailWord_554226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554226).length < 2 ^ (prefixWord ++ tailWord_554226).sum := by decide
  have hdescent : baseEnd_554226 < baseStart_554226 := by decide
  rcases family_descends (prefixWord ++ tailWord_554226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554228 : List Nat := [2, 6, 1, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_554228 : Nat := 118140960795 + 554228 * 2 ^ 59
def prefixEnd_554228 : Nat := 4983230072969 + 3 ^ 40 * 554228 * 2
def baseEnd_554228 : Nat := 284585356180162814101159

theorem tailTrace_554228 : CollatzResearch.WordTrace tailWord_554228 prefixEnd_554228 284585356180162814101159 := by
  unfold tailWord_554228
  simp only [CollatzResearch.WordTrace]
  refine ⟨10107177918067042725835669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13476237224089390301114225 10107177918067042725835669)
  ·
    refine ⟨473773964909392627773547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10107177918067042725835669 473773964909392627773547)
    ·
      refine ⟨710660947364088941660321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 473773964909392627773547 710660947364088941660321)
      ·
        refine ⟨532995710523066706245241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 710660947364088941660321 532995710523066706245241)
        ·
          refine ⟨399746782892300029683931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 532995710523066706245241 399746782892300029683931)
          ·
            refine ⟨599620174338450044525897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399746782892300029683931 599620174338450044525897)
            ·
              refine ⟨449715130753837533394423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 599620174338450044525897 449715130753837533394423)
              ·
                refine ⟨674572696130756300091635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449715130753837533394423 674572696130756300091635)
                ·
                  refine ⟨1011859044196134450137453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674572696130756300091635 1011859044196134450137453)
                  ·
                    refine ⟨379447141573550418801545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1011859044196134450137453 379447141573550418801545)
                    ·
                      refine ⟨284585356180162814101159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 379447141573550418801545 284585356180162814101159)
                      ·
                        rfl

theorem cell23_554228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_554228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554228 prefixEnd_554228 := by exact prefixLift 554228
  have htrace : WordTrace (prefixWord ++ tailWord_554228) baseStart_554228 baseEnd_554228 := by
    simpa [prefixWord, tailWord_554228, baseEnd_554228] using wordTrace_append hprefix tailTrace_554228
  have hstable : (prefixWord ++ tailWord_554228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554228).length < 2 ^ (prefixWord ++ tailWord_554228).sum := by decide
  have hdescent : baseEnd_554228 < baseStart_554228 := by decide
  rcases family_descends (prefixWord ++ tailWord_554228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554266 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3]
def baseStart_554266 : Nat := 118140960795 + 554266 * 2 ^ 59
def prefixEnd_554266 : Nat := 4983230072969 + 3 ^ 40 * 554266 * 2
def baseEnd_554266 : Nat := 284604868445033665425983

theorem tailTrace_554266 : CollatzResearch.WordTrace tailWord_554266 prefixEnd_554266 284604868445033665425983 := by
  unfold tailWord_554266
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053935452499104485388663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13477161206664278627703101 5053935452499104485388663)
  ·
    refine ⟨7580903178748656728082995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5053935452499104485388663 7580903178748656728082995)
    ·
      refine ⟨11371354768122985092124493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7580903178748656728082995 11371354768122985092124493)
      ·
        refine ⟨4264258038046119409546685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11371354768122985092124493 4264258038046119409546685)
        ·
          refine ⟨1599096764267294778580007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4264258038046119409546685 1599096764267294778580007)
          ·
            refine ⟨2398645146400942167870011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599096764267294778580007 2398645146400942167870011)
            ·
              refine ⟨3597967719601413251805017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2398645146400942167870011 3597967719601413251805017)
              ·
                refine ⟨2698475789701059938853763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3597967719601413251805017 2698475789701059938853763)
                ·
                  refine ⟨4047713684551589908280645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2698475789701059938853763 4047713684551589908280645)
                  ·
                    refine ⟨758946315853423107802621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4047713684551589908280645 758946315853423107802621)
                    ·
                      refine ⟨284604868445033665425983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 758946315853423107802621 284604868445033665425983)
                      ·
                        rfl

theorem cell23_554266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_554266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554266 prefixEnd_554266 := by exact prefixLift 554266
  have htrace : WordTrace (prefixWord ++ tailWord_554266) baseStart_554266 baseEnd_554266 := by
    simpa [prefixWord, tailWord_554266, baseEnd_554266] using wordTrace_append hprefix tailTrace_554266
  have hstable : (prefixWord ++ tailWord_554266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554266).length < 2 ^ (prefixWord ++ tailWord_554266).sum := by decide
  have hdescent : baseEnd_554266 < baseStart_554266 := by decide
  rcases family_descends (prefixWord ++ tailWord_554266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554290 : List Nat := [3, 2, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_554290 : Nat := 118140960795 + 554290 * 2 ^ 59
def prefixEnd_554290 : Nat := 4983230072969 + 3 ^ 40 * 554290 * 2
def baseEnd_554290 : Nat := 94872397326913857175291

theorem tailTrace_554290 : CollatzResearch.WordTrace tailWord_554290 prefixEnd_554290 94872397326913857175291 := by
  unfold tailWord_554290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5054154290477367510107081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13477744774606313360285549 5054154290477367510107081)
  ·
    refine ⟨3790615717858025632580311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5054154290477367510107081 3790615717858025632580311)
    ·
      refine ⟨5685923576787038448870467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3790615717858025632580311 5685923576787038448870467)
      ·
        refine ⟨8528885365180557673305701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5685923576787038448870467 8528885365180557673305701)
        ·
          refine ⟨1599166005971354563744819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8528885365180557673305701 1599166005971354563744819)
          ·
            refine ⟨2398749008957031845617229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599166005971354563744819 2398749008957031845617229)
            ·
              refine ⟨899530878358886942106461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2398749008957031845617229 899530878358886942106461)
              ·
                refine ⟨337324079384582603289923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 899530878358886942106461 337324079384582603289923)
                ·
                  refine ⟨505986119076873904934885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337324079384582603289923 505986119076873904934885)
                  ·
                    refine ⟨94872397326913857175291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 505986119076873904934885 94872397326913857175291)
                    ·
                      rfl

theorem cell23_554290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_554290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554290 prefixEnd_554290 := by exact prefixLift 554290
  have htrace : WordTrace (prefixWord ++ tailWord_554290) baseStart_554290 baseEnd_554290 := by
    simpa [prefixWord, tailWord_554290, baseEnd_554290] using wordTrace_append hprefix tailTrace_554290
  have hstable : (prefixWord ++ tailWord_554290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554290).length < 2 ^ (prefixWord ++ tailWord_554290).sum := by decide
  have hdescent : baseEnd_554290 < baseStart_554290 := by decide
  rcases family_descends (prefixWord ++ tailWord_554290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554313 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 3, 1, 3]
def baseStart_554313 : Nat := 118140960795 + 554313 * 2 ^ 59
def prefixEnd_554313 : Nat := 4983230072969 + 3 ^ 40 * 554313 * 2
def baseEnd_554313 : Nat := 284629002035794981538267

theorem tailTrace_554313 : CollatzResearch.WordTrace tailWord_554313 prefixEnd_554313 284629002035794981538267 := by
  unfold tailWord_554313
  simp only [CollatzResearch.WordTrace]
  refine ⟨20217456040826144968515593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13478304027217429979010395 20217456040826144968515593)
  ·
    refine ⟨15163092030619608726386695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20217456040826144968515593 15163092030619608726386695)
    ·
      refine ⟨22744638045929413089580043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15163092030619608726386695 22744638045929413089580043)
      ·
        refine ⟨34116957068894119634370065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22744638045929413089580043 34116957068894119634370065)
        ·
          refine ⟨25587717801670589725777549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34116957068894119634370065 25587717801670589725777549)
          ·
            refine ⟨9595394175626471147166581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25587717801670589725777549 9595394175626471147166581)
            ·
              refine ⟨899568203964981670046867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9595394175626471147166581 899568203964981670046867)
              ·
                refine ⟨1349352305947472505070301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899568203964981670046867 1349352305947472505070301)
                ·
                  refine ⟨506007114730302189401363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1349352305947472505070301 506007114730302189401363)
                  ·
                    refine ⟨759010672095453284102045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 506007114730302189401363 759010672095453284102045)
                    ·
                      refine ⟨284629002035794981538267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 759010672095453284102045 284629002035794981538267)
                      ·
                        rfl

theorem cell23_554313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 1, 3].length) (baseStart_554313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554313 prefixEnd_554313 := by exact prefixLift 554313
  have htrace : WordTrace (prefixWord ++ tailWord_554313) baseStart_554313 baseEnd_554313 := by
    simpa [prefixWord, tailWord_554313, baseEnd_554313] using wordTrace_append hprefix tailTrace_554313
  have hstable : (prefixWord ++ tailWord_554313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554313).length < 2 ^ (prefixWord ++ tailWord_554313).sum := by decide
  have hdescent : baseEnd_554313 < baseStart_554313 := by decide
  rcases family_descends (prefixWord ++ tailWord_554313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554340 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 2, 3, 2]
def baseStart_554340 : Nat := 118140960795 + 554340 * 2 ^ 59
def prefixEnd_554340 : Nat := 4983230072969 + 3 ^ 40 * 554340 * 2
def baseEnd_554340 : Nat := 284642866013466375900643

theorem tailTrace_554340 : CollatzResearch.WordTrace tailWord_554340 prefixEnd_554340 284642866013466375900643 := by
  unfold tailWord_554340
  simp only [CollatzResearch.WordTrace]
  refine ⟨10109220405864164289874237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13478960541152219053165649 10109220405864164289874237)
  ·
    refine ⟨3790957652199061608702839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10109220405864164289874237 3790957652199061608702839)
    ·
      refine ⟨5686436478298592413054259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3790957652199061608702839 5686436478298592413054259)
      ·
        refine ⟨8529654717447888619581389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5686436478298592413054259 8529654717447888619581389)
        ·
          refine ⟨3198620519042958232343021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8529654717447888619581389 3198620519042958232343021)
          ·
            refine ⟨1199482694641109337128633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3198620519042958232343021 1199482694641109337128633)
            ·
              refine ⟨899612020980832002846475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1199482694641109337128633 899612020980832002846475)
              ·
                refine ⟨1349418031471248004269713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899612020980832002846475 1349418031471248004269713)
                ·
                  refine ⟨1012063523603436003202285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1349418031471248004269713 1012063523603436003202285)
                  ·
                    refine ⟨379523821351288501200857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012063523603436003202285 379523821351288501200857)
                    ·
                      refine ⟨284642866013466375900643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 379523821351288501200857 284642866013466375900643)
                      ·
                        rfl

theorem cell23_554340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_554340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554340 prefixEnd_554340 := by exact prefixLift 554340
  have htrace : WordTrace (prefixWord ++ tailWord_554340) baseStart_554340 baseEnd_554340 := by
    simpa [prefixWord, tailWord_554340, baseEnd_554340] using wordTrace_append hprefix tailTrace_554340
  have hstable : (prefixWord ++ tailWord_554340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554340).length < 2 ^ (prefixWord ++ tailWord_554340).sum := by decide
  have hdescent : baseEnd_554340 < baseStart_554340 := by decide
  rcases family_descends (prefixWord ++ tailWord_554340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554363 : List Nat := [1, 1, 1, 1, 1, 6, 4, 2, 2, 4]
def baseStart_554363 : Nat := 118140960795 + 554363 * 2 ^ 59
def prefixEnd_554363 : Nat := 4983230072969 + 3 ^ 40 * 554363 * 2
def baseEnd_554363 : Nat := 94884892022839928637679

theorem tailTrace_554363 : CollatzResearch.WordTrace tailWord_554363 prefixEnd_554363 94884892022839928637679 := by
  unfold tailWord_554363
  simp only [CollatzResearch.WordTrace]
  refine ⟨20219279690645003507835743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13479519793763335671890495 20219279690645003507835743)
  ·
    refine ⟨30328919535967505261753615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20219279690645003507835743 30328919535967505261753615)
    ·
      refine ⟨45493379303951257892630423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30328919535967505261753615 45493379303951257892630423)
      ·
        refine ⟨68240068955926886838945635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45493379303951257892630423 68240068955926886838945635)
        ·
          refine ⟨102360103433890330258418453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68240068955926886838945635 102360103433890330258418453)
          ·
            refine ⟨4798129848463609230863365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 102360103433890330258418453 4798129848463609230863365)
            ·
              refine ⟨899649346586926730786881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4798129848463609230863365 899649346586926730786881)
              ·
                refine ⟨674737009940195048090161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 899649346586926730786881 674737009940195048090161)
                ·
                  refine ⟨506052757455146286067621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 674737009940195048090161 506052757455146286067621)
                  ·
                    refine ⟨94884892022839928637679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 506052757455146286067621 94884892022839928637679)
                    ·
                      rfl

theorem cell23_554363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 4].length) (baseStart_554363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554363 prefixEnd_554363 := by exact prefixLift 554363
  have htrace : WordTrace (prefixWord ++ tailWord_554363) baseStart_554363 baseEnd_554363 := by
    simpa [prefixWord, tailWord_554363, baseEnd_554363] using wordTrace_append hprefix tailTrace_554363
  have hstable : (prefixWord ++ tailWord_554363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554363).length < 2 ^ (prefixWord ++ tailWord_554363).sum := by decide
  have hdescent : baseEnd_554363 < baseStart_554363 := by decide
  rcases family_descends (prefixWord ++ tailWord_554363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554370 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_554370 : Nat := 118140960795 + 554370 * 2 ^ 59
def prefixEnd_554370 : Nat := 4983230072969 + 3 ^ 40 * 554370 * 2
def baseEnd_554370 : Nat := 284658270433101258525505

theorem tailTrace_554370 : CollatzResearch.WordTrace tailWord_554370 prefixEnd_554370 284658270433101258525505 := by
  unfold tailWord_554370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5054883750404910925835141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13479690001079762468893709 5054883750404910925835141)
  ·
    refine ⟨947790703200920798594089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5054883750404910925835141 947790703200920798594089)
    ·
      refine ⟨710843027400690598945567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 947790703200920798594089 710843027400690598945567)
      ·
        refine ⟨1066264541101035898418351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710843027400690598945567 1066264541101035898418351)
        ·
          refine ⟨1599396811651553847627527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066264541101035898418351 1599396811651553847627527)
          ·
            refine ⟨2399095217477330771441291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599396811651553847627527 2399095217477330771441291)
            ·
              refine ⟨3598642826215996157161937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399095217477330771441291 3598642826215996157161937)
              ·
                refine ⟨2698982119661997117871453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3598642826215996157161937 2698982119661997117871453)
                ·
                  refine ⟨1012118294873248919201795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2698982119661997117871453 1012118294873248919201795)
                  ·
                    refine ⟨1518177442309873378802693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1012118294873248919201795 1518177442309873378802693)
                    ·
                      refine ⟨284658270433101258525505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1518177442309873378802693 284658270433101258525505)
                      ·
                        rfl

theorem cell23_554370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_554370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554370 prefixEnd_554370 := by exact prefixLift 554370
  have htrace : WordTrace (prefixWord ++ tailWord_554370) baseStart_554370 baseEnd_554370 := by
    simpa [prefixWord, tailWord_554370, baseEnd_554370] using wordTrace_append hprefix tailTrace_554370
  have hstable : (prefixWord ++ tailWord_554370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554370).length < 2 ^ (prefixWord ++ tailWord_554370).sum := by decide
  have hdescent : baseEnd_554370 < baseStart_554370 := by decide
  rcases family_descends (prefixWord ++ tailWord_554370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554376 : List Nat := [2, 1, 3, 3, 1, 2, 3, 8]
def baseStart_554376 : Nat := 118140960795 + 554376 * 2 ^ 59
def prefixEnd_554376 : Nat := 4983230072969 + 3 ^ 40 * 554376 * 2
def baseEnd_554376 : Nat := 10543013011741786483351

theorem tailTrace_554376 : CollatzResearch.WordTrace tailWord_554376 prefixEnd_554376 10543013011741786483351 := by
  unfold tailWord_554376
  simp only [CollatzResearch.WordTrace]
  refine ⟨10109876919798953364029491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13479835893065271152039321 10109876919798953364029491)
  ·
    refine ⟨15164815379698430046044237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10109876919798953364029491 15164815379698430046044237)
    ·
      refine ⟨5686805767386911267266589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15164815379698430046044237 5686805767386911267266589)
      ·
        refine ⟨2132552162770091725224971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5686805767386911267266589 2132552162770091725224971)
        ·
          refine ⟨3198828244155137587837457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2132552162770091725224971 3198828244155137587837457)
          ·
            refine ⟨2399121183116353190878093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3198828244155137587837457 2399121183116353190878093)
            ·
              refine ⟨899670443668632446579285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2399121183116353190878093 899670443668632446579285)
              ·
                refine ⟨10543013011741786483351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 899670443668632446579285 10543013011741786483351)
                ·
                  rfl

theorem cell23_554376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 8].length) (baseStart_554376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554376 prefixEnd_554376 := by exact prefixLift 554376
  have htrace : WordTrace (prefixWord ++ tailWord_554376) baseStart_554376 baseEnd_554376 := by
    simpa [prefixWord, tailWord_554376, baseEnd_554376] using wordTrace_append hprefix tailTrace_554376
  have hstable : (prefixWord ++ tailWord_554376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554376).length < 2 ^ (prefixWord ++ tailWord_554376).sum := by decide
  have hdescent : baseEnd_554376 < baseStart_554376 := by decide
  rcases family_descends (prefixWord ++ tailWord_554376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554403 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 4, 1, 3]
def baseStart_554403 : Nat := 118140960795 + 554403 * 2 ^ 59
def prefixEnd_554403 : Nat := 4983230072969 + 3 ^ 40 * 554403 * 2
def baseEnd_554403 : Nat := 284675215294699629412853

theorem tailTrace_554403 : CollatzResearch.WordTrace tailWord_554403 prefixEnd_554403 284675215294699629412853 := by
  unfold tailWord_554403
  simp only [CollatzResearch.WordTrace]
  refine ⟨20220738610500090339291863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13480492407000060226194575 20220738610500090339291863)
  ·
    refine ⟨30331107915750135508937795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20220738610500090339291863 30331107915750135508937795)
    ·
      refine ⟨45496661873625203263406693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30331107915750135508937795 45496661873625203263406693)
      ·
        refine ⟨8530624101304725611888755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45496661873625203263406693 8530624101304725611888755)
        ·
          refine ⟨12795936151957088417833133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8530624101304725611888755 12795936151957088417833133)
          ·
            refine ⟨4798476056983908156687425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12795936151957088417833133 4798476056983908156687425)
            ·
              refine ⟨3598857042737931117515569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4798476056983908156687425 3598857042737931117515569)
              ·
                refine ⟨2699142782053448338136677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3598857042737931117515569 2699142782053448338136677)
                ·
                  refine ⟨506089271635021563400627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2699142782053448338136677 506089271635021563400627)
                  ·
                    refine ⟨759133907452532345100941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 506089271635021563400627 759133907452532345100941)
                    ·
                      refine ⟨284675215294699629412853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 759133907452532345100941 284675215294699629412853)
                      ·
                        rfl

theorem cell23_554403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_554403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554403 prefixEnd_554403 := by exact prefixLift 554403
  have htrace : WordTrace (prefixWord ++ tailWord_554403) baseStart_554403 baseEnd_554403 := by
    simpa [prefixWord, tailWord_554403, baseEnd_554403] using wordTrace_append hprefix tailTrace_554403
  have hstable : (prefixWord ++ tailWord_554403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554403).length < 2 ^ (prefixWord ++ tailWord_554403).sum := by decide
  have hdescent : baseEnd_554403 < baseStart_554403 := by decide
  rcases family_descends (prefixWord ++ tailWord_554403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554434 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_554434 : Nat := 118140960795 + 554434 * 2 ^ 59
def prefixEnd_554434 : Nat := 4983230072969 + 3 ^ 40 * 554434 * 2
def baseEnd_554434 : Nat := 284691133194989008125211

theorem tailTrace_554434 : CollatzResearch.WordTrace tailWord_554434 prefixEnd_554434 284691133194989008125211 := by
  unfold tailWord_554434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5055467318346945658417589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13481246182258521755780237 5055467318346945658417589)
  ·
    refine ⟨473950061095026155476649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5055467318346945658417589 473950061095026155476649)
    ·
      refine ⟨355462545821269616607487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 473950061095026155476649 355462545821269616607487)
      ·
        refine ⟨533193818731904424911231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355462545821269616607487 533193818731904424911231)
        ·
          refine ⟨799790728097856637366847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533193818731904424911231 799790728097856637366847)
          ·
            refine ⟨1199686092146784956050271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799790728097856637366847 1199686092146784956050271)
            ·
              refine ⟨1799529138220177434075407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199686092146784956050271 1799529138220177434075407)
              ·
                refine ⟨2699293707330266151113111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799529138220177434075407 2699293707330266151113111)
                ·
                  refine ⟨4048940560995399226669667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699293707330266151113111 4048940560995399226669667)
                  ·
                    refine ⟨6073410841493098840004501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4048940560995399226669667 6073410841493098840004501)
                    ·
                      refine ⟨284691133194989008125211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6073410841493098840004501 284691133194989008125211)
                      ·
                        rfl

theorem cell23_554434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_554434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554434 prefixEnd_554434 := by exact prefixLift 554434
  have htrace : WordTrace (prefixWord ++ tailWord_554434) baseStart_554434 baseEnd_554434 := by
    simpa [prefixWord, tailWord_554434, baseEnd_554434] using wordTrace_append hprefix tailTrace_554434
  have hstable : (prefixWord ++ tailWord_554434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554434).length < 2 ^ (prefixWord ++ tailWord_554434).sum := by decide
  have hdescent : baseEnd_554434 < baseStart_554434 := by decide
  rcases family_descends (prefixWord ++ tailWord_554434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554456 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_554456 : Nat := 118140960795 + 554456 * 2 ^ 59
def prefixEnd_554456 : Nat := 4983230072969 + 3 ^ 40 * 554456 * 2
def baseEnd_554456 : Nat := 284702429769387922050109

theorem tailTrace_554456 : CollatzResearch.WordTrace tailWord_554456 prefixEnd_554456 284702429769387922050109 := by
  unfold tailWord_554456
  simp only [CollatzResearch.WordTrace]
  refine ⟨10111335839654040195485611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13481781119538720260647481 10111335839654040195485611)
  ·
    refine ⟨15167003759481060293228417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10111335839654040195485611 15167003759481060293228417)
    ·
      refine ⟨11375252819610795219921313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15167003759481060293228417 11375252819610795219921313)
      ·
        refine ⟨8531439614708096414940985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11375252819610795219921313 8531439614708096414940985)
        ·
          refine ⟨6398579711031072311205739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8531439614708096414940985 6398579711031072311205739)
          ·
            refine ⟨9597869566546608466808609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6398579711031072311205739 9597869566546608466808609)
            ·
              refine ⟨7198402174909956350106457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9597869566546608466808609 7198402174909956350106457)
              ·
                refine ⟨5398801631182467262579843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7198402174909956350106457 5398801631182467262579843)
                ·
                  refine ⟨8098202446773700893869765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5398801631182467262579843 8098202446773700893869765)
                  ·
                    refine ⟨1518412958770068917600581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8098202446773700893869765 1518412958770068917600581)
                    ·
                      refine ⟨284702429769387922050109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1518412958770068917600581 284702429769387922050109)
                      ·
                        rfl

theorem cell23_554456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_554456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554456 prefixEnd_554456 := by exact prefixLift 554456
  have htrace : WordTrace (prefixWord ++ tailWord_554456) baseStart_554456 baseEnd_554456 := by
    simpa [prefixWord, tailWord_554456, baseEnd_554456] using wordTrace_append hprefix tailTrace_554456
  have hstable : (prefixWord ++ tailWord_554456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554456).length < 2 ^ (prefixWord ++ tailWord_554456).sum := by decide
  have hdescent : baseEnd_554456 < baseStart_554456 := by decide
  rcases family_descends (prefixWord ++ tailWord_554456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554513 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 2, 5]
def baseStart_554513 : Nat := 118140960795 + 554513 * 2 ^ 59
def prefixEnd_554513 : Nat := 4983230072969 + 3 ^ 40 * 554513 * 2
def baseEnd_554513 : Nat := 94910566055564733012449

theorem tailTrace_554513 : CollatzResearch.WordTrace tailWord_554513 prefixEnd_554513 94910566055564733012449 := by
  unfold tailWord_554513
  simp only [CollatzResearch.WordTrace]
  refine ⟨20224750640101579125796193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13483167093401052750530795 20224750640101579125796193)
  ·
    refine ⟨15168562980076184344347145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20224750640101579125796193 15168562980076184344347145)
    ·
      refine ⟨11376422235057138258260359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15168562980076184344347145 11376422235057138258260359)
      ·
        refine ⟨17064633352585707387390539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11376422235057138258260359 17064633352585707387390539)
        ·
          refine ⟨25596950028878561081085809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17064633352585707387390539 25596950028878561081085809)
          ·
            refine ⟨19197712521658920810814357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25596950028878561081085809 19197712521658920810814357)
            ·
              refine ⟨899892774452761913006923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19197712521658920810814357 899892774452761913006923)
              ·
                refine ⟨1349839161679142869510385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899892774452761913006923 1349839161679142869510385)
                ·
                  refine ⟨1012379371259357152132789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1349839161679142869510385 1012379371259357152132789)
                  ·
                    refine ⟨94910566055564733012449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1012379371259357152132789 94910566055564733012449)
                    ·
                      rfl

theorem cell23_554513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_554513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554513 prefixEnd_554513 := by exact prefixLift 554513
  have htrace : WordTrace (prefixWord ++ tailWord_554513) baseStart_554513 baseEnd_554513 := by
    simpa [prefixWord, tailWord_554513, baseEnd_554513] using wordTrace_append hprefix tailTrace_554513
  have hstable : (prefixWord ++ tailWord_554513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554513).length < 2 ^ (prefixWord ++ tailWord_554513).sum := by decide
  have hdescent : baseEnd_554513 < baseStart_554513 := by decide
  rcases family_descends (prefixWord ++ tailWord_554513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554567 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_554567 : Nat := 118140960795 + 554567 * 2 ^ 59
def prefixEnd_554567 : Nat := 4983230072969 + 3 ^ 40 * 554567 * 2
def baseEnd_554567 : Nat := 284759426122036987762099

theorem tailTrace_554567 : CollatzResearch.WordTrace tailWord_554567 prefixEnd_554567 284759426122036987762099 := by
  unfold tailWord_554567
  simp only [CollatzResearch.WordTrace]
  refine ⟨20226720181905946348261955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13484480121270630898841303 20226720181905946348261955)
  ·
    refine ⟨30340080272858919522392933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20226720181905946348261955 30340080272858919522392933)
    ·
      refine ⟨5688765051161047410448675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30340080272858919522392933 5688765051161047410448675)
      ·
        refine ⟨8533147576741571115673013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5688765051161047410448675 8533147576741571115673013)
        ·
          refine ⟨799982585319522292094345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8533147576741571115673013 799982585319522292094345)
          ·
            refine ⟨599986938989641719070759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 799982585319522292094345 599986938989641719070759)
            ·
              refine ⟨899980408484462578606139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599986938989641719070759 899980408484462578606139)
              ·
                refine ⟨1349970612726693867909209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899980408484462578606139 1349970612726693867909209)
                ·
                  refine ⟨1012477959545020400931907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1349970612726693867909209 1012477959545020400931907)
                  ·
                    refine ⟨1518716939317530601397861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1012477959545020400931907 1518716939317530601397861)
                    ·
                      refine ⟨284759426122036987762099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1518716939317530601397861 284759426122036987762099)
                      ·
                        rfl

theorem cell23_554567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_554567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554567 prefixEnd_554567 := by exact prefixLift 554567
  have htrace : WordTrace (prefixWord ++ tailWord_554567) baseStart_554567 baseEnd_554567 := by
    simpa [prefixWord, tailWord_554567, baseEnd_554567] using wordTrace_append hprefix tailTrace_554567
  have hstable : (prefixWord ++ tailWord_554567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554567).length < 2 ^ (prefixWord ++ tailWord_554567).sum := by decide
  have hdescent : baseEnd_554567 < baseStart_554567 := by decide
  rcases family_descends (prefixWord ++ tailWord_554567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554577 : List Nat := [1, 2, 2, 1, 3, 2, 4, 3, 1, 4]
def baseStart_554577 : Nat := 118140960795 + 554577 * 2 ^ 59
def prefixEnd_554577 : Nat := 4983230072969 + 3 ^ 40 * 554577 * 2
def baseEnd_554577 : Nat := 94921520309527316212351

theorem tailTrace_554577 : CollatzResearch.WordTrace tailWord_554577 prefixEnd_554577 94921520309527316212351 := by
  unfold tailWord_554577
  simp only [CollatzResearch.WordTrace]
  refine ⟨20227084911869718056125985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13484723274579812037417323 20227084911869718056125985)
  ·
    refine ⟨15170313683902288542094489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20227084911869718056125985 15170313683902288542094489)
    ·
      refine ⟨11377735262926716406570867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15170313683902288542094489 11377735262926716406570867)
      ·
        refine ⟨17066602894390074609856301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11377735262926716406570867 17066602894390074609856301)
        ·
          refine ⟨6399976085396277978696113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17066602894390074609856301 6399976085396277978696113)
          ·
            refine ⟨4799982064047208484022085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6399976085396277978696113 4799982064047208484022085)
            ·
              refine ⟨899996637008851590754141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4799982064047208484022085 899996637008851590754141)
              ·
                refine ⟨337498738878319346532803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 899996637008851590754141 337498738878319346532803)
                ·
                  refine ⟨506248108317479019799205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337498738878319346532803 506248108317479019799205)
                  ·
                    refine ⟨94921520309527316212351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 506248108317479019799205 94921520309527316212351)
                    ·
                      rfl

theorem cell23_554577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_554577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554577 prefixEnd_554577 := by exact prefixLift 554577
  have htrace : WordTrace (prefixWord ++ tailWord_554577) baseStart_554577 baseEnd_554577 := by
    simpa [prefixWord, tailWord_554577, baseEnd_554577] using wordTrace_append hprefix tailTrace_554577
  have hstable : (prefixWord ++ tailWord_554577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554577).length < 2 ^ (prefixWord ++ tailWord_554577).sum := by decide
  have hdescent : baseEnd_554577 < baseStart_554577 := by decide
  rcases family_descends (prefixWord ++ tailWord_554577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554623 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 4]
def baseStart_554623 : Nat := 118140960795 + 554623 * 2 ^ 59
def prefixEnd_554623 : Nat := 4983230072969 + 3 ^ 40 * 554623 * 2
def baseEnd_554623 : Nat := 284788181038688768661841

theorem tailTrace_554623 : CollatzResearch.WordTrace tailWord_554623 prefixEnd_554623 284788181038688768661841 := by
  unfold tailWord_554623
  simp only [CollatzResearch.WordTrace]
  refine ⟨20228762669703067912300523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13485841779802045274867015 20228762669703067912300523)
  ·
    refine ⟨30343144004554601868450785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20228762669703067912300523 30343144004554601868450785)
    ·
      refine ⟨22757358003415951401338089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30343144004554601868450785 22757358003415951401338089)
      ·
        refine ⟨17068018502561963551003567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22757358003415951401338089 17068018502561963551003567)
        ·
          refine ⟨25602027753842945326505351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17068018502561963551003567 25602027753842945326505351)
          ·
            refine ⟨38403041630764417989758027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25602027753842945326505351 38403041630764417989758027)
            ·
              refine ⟨57604562446146626984637041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38403041630764417989758027 57604562446146626984637041)
              ·
                refine ⟨43203421834609970238477781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57604562446146626984637041 43203421834609970238477781)
                ·
                  refine ⟨1012580199248671177464323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 43203421834609970238477781 1012580199248671177464323)
                  ·
                    refine ⟨1518870298873006766196485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1012580199248671177464323 1518870298873006766196485)
                    ·
                      refine ⟨284788181038688768661841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1518870298873006766196485 284788181038688768661841)
                      ·
                        rfl

theorem cell23_554623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_554623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554623 prefixEnd_554623 := by exact prefixLift 554623
  have htrace : WordTrace (prefixWord ++ tailWord_554623) baseStart_554623 baseEnd_554623 := by
    simpa [prefixWord, tailWord_554623, baseEnd_554623] using wordTrace_append hprefix tailTrace_554623
  have hstable : (prefixWord ++ tailWord_554623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554623).length < 2 ^ (prefixWord ++ tailWord_554623).sum := by decide
  have hdescent : baseEnd_554623 < baseStart_554623 := by decide
  rcases family_descends (prefixWord ++ tailWord_554623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554633 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 1, 6]
def baseStart_554633 : Nat := 118140960795 + 554633 * 2 ^ 59
def prefixEnd_554633 : Nat := 4983230072969 + 3 ^ 40 * 554633 * 2
def baseEnd_554633 : Nat := 94931105281744576512265

theorem tailTrace_554633 : CollatzResearch.WordTrace tailWord_554633 prefixEnd_554633 94931105281744576512265 := by
  unfold tailWord_554633
  simp only [CollatzResearch.WordTrace]
  refine ⟨20229127399666839620164553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13486084933111226413443035 20229127399666839620164553)
  ·
    refine ⟨15171845549750129715123415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20229127399666839620164553 15171845549750129715123415)
    ·
      refine ⟨22757768324625194572685123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15171845549750129715123415 22757768324625194572685123)
      ·
        refine ⟨34136652486937791859027685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22757768324625194572685123 34136652486937791859027685)
        ·
          refine ⟨6400622341300835973567691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34136652486937791859027685 6400622341300835973567691)
          ·
            refine ⟨9600933511951253960351537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6400622341300835973567691 9600933511951253960351537)
            ·
              refine ⟨7200700133963440470263653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9600933511951253960351537 7200700133963440470263653)
              ·
                refine ⟨1350131275118145088174435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7200700133963440470263653 1350131275118145088174435)
                ·
                  refine ⟨2025196912677217632261653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350131275118145088174435 2025196912677217632261653)
                  ·
                    refine ⟨94931105281744576512265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2025196912677217632261653 94931105281744576512265)
                    ·
                      rfl

theorem cell23_554633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 6].length) (baseStart_554633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554633 prefixEnd_554633 := by exact prefixLift 554633
  have htrace : WordTrace (prefixWord ++ tailWord_554633) baseStart_554633 baseEnd_554633 := by
    simpa [prefixWord, tailWord_554633, baseEnd_554633] using wordTrace_append hprefix tailTrace_554633
  have hstable : (prefixWord ++ tailWord_554633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554633).length < 2 ^ (prefixWord ++ tailWord_554633).sum := by decide
  have hdescent : baseEnd_554633 < baseStart_554633 := by decide
  rcases family_descends (prefixWord ++ tailWord_554633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554660 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_554660 : Nat := 118140960795 + 554660 * 2 ^ 59
def prefixEnd_554660 : Nat := 4983230072969 + 3 ^ 40 * 554660 * 2
def baseEnd_554660 : Nat := 284807179822905123899171

theorem tailTrace_554660 : CollatzResearch.WordTrace tailWord_554660 prefixEnd_554660 284807179822905123899171 := by
  unfold tailWord_554660
  simp only [CollatzResearch.WordTrace]
  refine ⟨10115056085284511615698717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13486741447046015487598289 10115056085284511615698717)
  ·
    refine ⟨3793146031981691855887019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10115056085284511615698717 3793146031981691855887019)
    ·
      refine ⟨5689719047972537783830529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3793146031981691855887019 5689719047972537783830529)
      ·
        refine ⟨4267289285979403337872897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5689719047972537783830529 4267289285979403337872897)
        ·
          refine ⟨3200466964484552503404673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4267289285979403337872897 3200466964484552503404673)
          ·
            refine ⟨2400350223363414377553505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3200466964484552503404673 2400350223363414377553505)
            ·
              refine ⟨1800262667522560783165129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2400350223363414377553505 1800262667522560783165129)
              ·
                refine ⟨1350197000641920587373847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1800262667522560783165129 1350197000641920587373847)
                ·
                  refine ⟨2025295500962880881060771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350197000641920587373847 2025295500962880881060771)
                  ·
                    refine ⟨3037943251444321321591157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2025295500962880881060771 3037943251444321321591157)
                    ·
                      refine ⟨284807179822905123899171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3037943251444321321591157 284807179822905123899171)
                      ·
                        rfl

theorem cell23_554660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_554660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554660 prefixEnd_554660 := by exact prefixLift 554660
  have htrace : WordTrace (prefixWord ++ tailWord_554660) baseStart_554660 baseEnd_554660 := by
    simpa [prefixWord, tailWord_554660, baseEnd_554660] using wordTrace_append hprefix tailTrace_554660
  have hstable : (prefixWord ++ tailWord_554660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554660).length < 2 ^ (prefixWord ++ tailWord_554660).sum := by decide
  have hdescent : baseEnd_554660 < baseStart_554660 := by decide
  rcases family_descends (prefixWord ++ tailWord_554660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554701 : List Nat := [1, 6, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_554701 : Nat := 118140960795 + 554701 * 2 ^ 59
def prefixEnd_554701 : Nat := 4983230072969 + 3 ^ 40 * 554701 * 2
def baseEnd_554701 : Nat := 94942744176579821162161

theorem tailTrace_554701 : CollatzResearch.WordTrace tailWord_554701 prefixEnd_554701 94942744176579821162161 := by
  unfold tailWord_554701
  simp only [CollatzResearch.WordTrace]
  refine ⟨20231607563420487233639957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13487738375613658155759971 20231607563420487233639957)
  ·
    refine ⟨948356604535335339076873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20231607563420487233639957 948356604535335339076873)
    ·
      refine ⟨711267453401501504307655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 948356604535335339076873 711267453401501504307655)
      ·
        refine ⟨1066901180102252256461483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711267453401501504307655 1066901180102252256461483)
        ·
          refine ⟨1600351770153378384692225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066901180102252256461483 1600351770153378384692225)
          ·
            refine ⟨1200263827615033788519169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1600351770153378384692225 1200263827615033788519169)
            ·
              refine ⟨900197870711275341389377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1200263827615033788519169 900197870711275341389377)
              ·
                refine ⟨675148403033456506042033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900197870711275341389377 675148403033456506042033)
                ·
                  refine ⟨506361302275092379531525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 675148403033456506042033 506361302275092379531525)
                  ·
                    refine ⟨94942744176579821162161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 506361302275092379531525 94942744176579821162161)
                    ·
                      rfl

theorem cell23_554701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_554701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554701 prefixEnd_554701 := by exact prefixLift 554701
  have htrace : WordTrace (prefixWord ++ tailWord_554701) baseStart_554701 baseEnd_554701 := by
    simpa [prefixWord, tailWord_554701, baseEnd_554701] using wordTrace_append hprefix tailTrace_554701
  have hstable : (prefixWord ++ tailWord_554701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554701).length < 2 ^ (prefixWord ++ tailWord_554701).sum := by decide
  have hdescent : baseEnd_554701 < baseStart_554701 := by decide
  rcases family_descends (prefixWord ++ tailWord_554701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554703 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 5]
def baseStart_554703 : Nat := 118140960795 + 554703 * 2 ^ 59
def prefixEnd_554703 : Nat := 4983230072969 + 3 ^ 40 * 554703 * 2
def baseEnd_554703 : Nat := 284829259491048455661473

theorem tailTrace_554703 : CollatzResearch.WordTrace tailWord_554703 prefixEnd_554703 284829259491048455661473 := by
  unfold tailWord_554703
  simp only [CollatzResearch.WordTrace]
  refine ⟨20231680509413241575212763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13487787006275494383475175 20231680509413241575212763)
  ·
    refine ⟨30347520764119862362819145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20231680509413241575212763 30347520764119862362819145)
    ·
      refine ⟨22760640573089896772114359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30347520764119862362819145 22760640573089896772114359)
      ·
        refine ⟨34140960859634845158171539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22760640573089896772114359 34140960859634845158171539)
        ·
          refine ⟨51211441289452267737257309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34140960859634845158171539 51211441289452267737257309)
          ·
            refine ⟨19204290483544600401471491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51211441289452267737257309 19204290483544600401471491)
            ·
              refine ⟨28806435725316900602207237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19204290483544600401471491 28806435725316900602207237)
              ·
                refine ⟨5401206698496918862913857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28806435725316900602207237 5401206698496918862913857)
                ·
                  refine ⟨4050905023872689147185393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5401206698496918862913857 4050905023872689147185393)
                  ·
                    refine ⟨3038178767904516860389045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4050905023872689147185393 3038178767904516860389045)
                    ·
                      refine ⟨284829259491048455661473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3038178767904516860389045 284829259491048455661473)
                      ·
                        rfl

theorem cell23_554703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_554703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554703 prefixEnd_554703 := by exact prefixLift 554703
  have htrace : WordTrace (prefixWord ++ tailWord_554703) baseStart_554703 baseEnd_554703 := by
    simpa [prefixWord, tailWord_554703, baseEnd_554703] using wordTrace_append hprefix tailTrace_554703
  have hstable : (prefixWord ++ tailWord_554703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554703).length < 2 ^ (prefixWord ++ tailWord_554703).sum := by decide
  have hdescent : baseEnd_554703 < baseStart_554703 := by decide
  rcases family_descends (prefixWord ++ tailWord_554703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554708 : List Nat := [2, 4, 1, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_554708 : Nat := 118140960795 + 554708 * 2 ^ 59
def prefixEnd_554708 : Nat := 4983230072969 + 3 ^ 40 * 554708 * 2
def baseEnd_554708 : Nat := 284831826894320936098951

theorem tailTrace_554708 : CollatzResearch.WordTrace tailWord_554708 prefixEnd_554708 284831826894320936098951 := by
  unfold tailWord_554708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10115931437197563714572389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13487908582930084952763185 10115931437197563714572389)
  ·
    refine ⟨1896737144474543196482323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10115931437197563714572389 1896737144474543196482323)
    ·
      refine ⟨2845105716711814794723485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1896737144474543196482323 2845105716711814794723485)
      ·
        refine ⟨1066914643766930548021307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2845105716711814794723485 1066914643766930548021307)
        ·
          refine ⟨1600371965650395822031961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066914643766930548021307 1600371965650395822031961)
          ·
            refine ⟨1200278974237796866523971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1600371965650395822031961 1200278974237796866523971)
            ·
              refine ⟨1800418461356695299785957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200278974237796866523971 1800418461356695299785957)
              ·
                refine ⟨337578461504380368709867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1800418461356695299785957 337578461504380368709867)
                ·
                  refine ⟨506367692256570553064801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337578461504380368709867 506367692256570553064801)
                  ·
                    refine ⟨379775769192427914798601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 506367692256570553064801 379775769192427914798601)
                    ·
                      refine ⟨284831826894320936098951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 379775769192427914798601 284831826894320936098951)
                      ·
                        rfl

theorem cell23_554708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_554708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554708 prefixEnd_554708 := by exact prefixLift 554708
  have htrace : WordTrace (prefixWord ++ tailWord_554708) baseStart_554708 baseEnd_554708 := by
    simpa [prefixWord, tailWord_554708, baseEnd_554708] using wordTrace_append hprefix tailTrace_554708
  have hstable : (prefixWord ++ tailWord_554708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554708).length < 2 ^ (prefixWord ++ tailWord_554708).sum := by decide
  have hdescent : baseEnd_554708 < baseStart_554708 := by decide
  rcases family_descends (prefixWord ++ tailWord_554708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554734 : List Nat := [4, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_554734 : Nat := 118140960795 + 554734 * 2 ^ 59
def prefixEnd_554734 : Nat := 4983230072969 + 3 ^ 40 * 554734 * 2
def baseEnd_554734 : Nat := 284845177391337834373831

theorem tailTrace_554734 : CollatzResearch.WordTrace tailWord_554734 prefixEnd_554734 284845177391337834373831 := by
  unfold tailWord_554734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2529101396537616733698907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13488540781533955913060837 2529101396537616733698907)
  ·
    refine ⟨3793652094806425100548361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2529101396537616733698907 3793652094806425100548361)
    ·
      refine ⟨2845239071104818825411271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3793652094806425100548361 2845239071104818825411271)
      ·
        refine ⟨4267858606657228238116907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2845239071104818825411271 4267858606657228238116907)
        ·
          refine ⟨6401787909985842357175361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4267858606657228238116907 6401787909985842357175361)
          ·
            refine ⟨4801340932489381767881521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6401787909985842357175361 4801340932489381767881521)
            ·
              refine ⟨3601005699367036325911141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4801340932489381767881521 3601005699367036325911141)
              ·
                refine ⟨675188568631319311108339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3601005699367036325911141 675188568631319311108339)
                ·
                  refine ⟨1012782852946978966662509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675188568631319311108339 1012782852946978966662509)
                  ·
                    refine ⟨379793569855117112498441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012782852946978966662509 379793569855117112498441)
                    ·
                      refine ⟨284845177391337834373831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 379793569855117112498441 284845177391337834373831)
                      ·
                        rfl

theorem cell23_554734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_554734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554734 prefixEnd_554734 := by exact prefixLift 554734
  have htrace : WordTrace (prefixWord ++ tailWord_554734) baseStart_554734 baseEnd_554734 := by
    simpa [prefixWord, tailWord_554734, baseEnd_554734] using wordTrace_append hprefix tailTrace_554734
  have hstable : (prefixWord ++ tailWord_554734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554734).length < 2 ^ (prefixWord ++ tailWord_554734).sum := by decide
  have hdescent : baseEnd_554734 < baseStart_554734 := by decide
  rcases family_descends (prefixWord ++ tailWord_554734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554760 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_554760 : Nat := 118140960795 + 554760 * 2 ^ 59
def prefixEnd_554760 : Nat := 4983230072969 + 3 ^ 40 * 554760 * 2
def baseEnd_554760 : Nat := 284858527888354732648711

theorem tailTrace_554760 : CollatzResearch.WordTrace tailWord_554760 prefixEnd_554760 284858527888354732648711 := by
  unfold tailWord_554760
  simp only [CollatzResearch.WordTrace]
  refine ⟨10116879735103370155018867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13489172980137826873358489 10116879735103370155018867)
  ·
    refine ⟨15175319602655055232528301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10116879735103370155018867 15175319602655055232528301)
    ·
      refine ⟨5690744850995645712198113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15175319602655055232528301 5690744850995645712198113)
      ·
        refine ⟨4268058638246734284148585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5690744850995645712198113 4268058638246734284148585)
        ·
          refine ⟨3201043978685050713111439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4268058638246734284148585 3201043978685050713111439)
          ·
            refine ⟨4801565968027576069667159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3201043978685050713111439 4801565968027576069667159)
            ·
              refine ⟨7202348952041364104500739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4801565968027576069667159 7202348952041364104500739)
              ·
                refine ⟨10803523428062046156751109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7202348952041364104500739 10803523428062046156751109)
                ·
                  refine ⟨2025660642761633654390833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10803523428062046156751109 2025660642761633654390833)
                  ·
                    refine ⟨1519245482071225240793125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2025660642761633654390833 1519245482071225240793125)
                    ·
                      refine ⟨284858527888354732648711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1519245482071225240793125 284858527888354732648711)
                      ·
                        rfl

theorem cell23_554760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_554760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554760 prefixEnd_554760 := by exact prefixLift 554760
  have htrace : WordTrace (prefixWord ++ tailWord_554760) baseStart_554760 baseEnd_554760 := by
    simpa [prefixWord, tailWord_554760, baseEnd_554760] using wordTrace_append hprefix tailTrace_554760
  have hstable : (prefixWord ++ tailWord_554760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554760).length < 2 ^ (prefixWord ++ tailWord_554760).sum := by decide
  have hdescent : baseEnd_554760 < baseStart_554760 := by decide
  rcases family_descends (prefixWord ++ tailWord_554760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554864 : List Nat := [2, 1, 1, 1, 4, 1, 1, 7, 1, 4]
def baseStart_554864 : Nat := 118140960795 + 554864 * 2 ^ 59
def prefixEnd_554864 : Nat := 4983230072969 + 3 ^ 40 * 554864 * 2
def baseEnd_554864 : Nat := 94970643292140775249411

theorem tailTrace_554864 : CollatzResearch.WordTrace tailWord_554864 prefixEnd_554864 94970643292140775249411 := by
  unfold tailWord_554864
  simp only [CollatzResearch.WordTrace]
  refine ⟨10118776330914983035911823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13491701774553310714549097 10118776330914983035911823)
  ·
    refine ⟨15178164496372474553867735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10118776330914983035911823 15178164496372474553867735)
    ·
      refine ⟨22767246744558711830801603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15178164496372474553867735 22767246744558711830801603)
      ·
        refine ⟨34150870116838067746202405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22767246744558711830801603 34150870116838067746202405)
        ·
          refine ⟨6403288146907137702412951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34150870116838067746202405 6403288146907137702412951)
          ·
            refine ⟨9604932220360706553619427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6403288146907137702412951 9604932220360706553619427)
            ·
              refine ⟨14407398330541059830429141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9604932220360706553619427 14407398330541059830429141)
              ·
                refine ⟨337673398372056089775683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14407398330541059830429141 337673398372056089775683)
                ·
                  refine ⟨506510097558084134663525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337673398372056089775683 506510097558084134663525)
                  ·
                    refine ⟨94970643292140775249411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 506510097558084134663525 94970643292140775249411)
                    ·
                      rfl

theorem cell23_554864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 1, 4].length) (baseStart_554864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554864 prefixEnd_554864 := by exact prefixLift 554864
  have htrace : WordTrace (prefixWord ++ tailWord_554864) baseStart_554864 baseEnd_554864 := by
    simpa [prefixWord, tailWord_554864, baseEnd_554864] using wordTrace_append hprefix tailTrace_554864
  have hstable : (prefixWord ++ tailWord_554864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554864).length < 2 ^ (prefixWord ++ tailWord_554864).sum := by decide
  have hdescent : baseEnd_554864 < baseStart_554864 := by decide
  rcases family_descends (prefixWord ++ tailWord_554864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554880 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 6]
def baseStart_554880 : Nat := 118140960795 + 554880 * 2 ^ 59
def prefixEnd_554880 : Nat := 4983230072969 + 3 ^ 40 * 554880 * 2
def baseEnd_554880 : Nat := 284920145566894263148159

theorem tailTrace_554880 : CollatzResearch.WordTrace tailWord_554880 prefixEnd_554880 284920145566894263148159 := by
  unfold tailWord_554880
  simp only [CollatzResearch.WordTrace]
  refine ⟨10119068114886000402203047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13492090819848000536270729 10119068114886000402203047)
  ·
    refine ⟨15178602172329000603304571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10119068114886000402203047 15178602172329000603304571)
    ·
      refine ⟨22767903258493500904956857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15178602172329000603304571 22767903258493500904956857)
      ·
        refine ⟨17075927443870125678717643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22767903258493500904956857 17075927443870125678717643)
        ·
          refine ⟨25613891165805188518076465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17075927443870125678717643 25613891165805188518076465)
          ·
            refine ⟨19210418374353891388557349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25613891165805188518076465 19210418374353891388557349)
            ·
              refine ⟨3601953445191354635354503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19210418374353891388557349 3601953445191354635354503)
              ·
                refine ⟨5402930167787031953031755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3601953445191354635354503 5402930167787031953031755)
                ·
                  refine ⟨8104395251680547929547633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5402930167787031953031755 8104395251680547929547633)
                  ·
                    refine ⟨6078296438760410947160725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8104395251680547929547633 6078296438760410947160725)
                    ·
                      refine ⟨284920145566894263148159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6078296438760410947160725 284920145566894263148159)
                      ·
                        rfl

theorem cell23_554880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_554880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554880 prefixEnd_554880 := by exact prefixLift 554880
  have htrace : WordTrace (prefixWord ++ tailWord_554880) baseStart_554880 baseEnd_554880 := by
    simpa [prefixWord, tailWord_554880, baseEnd_554880] using wordTrace_append hprefix tailTrace_554880
  have hstable : (prefixWord ++ tailWord_554880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554880).length < 2 ^ (prefixWord ++ tailWord_554880).sum := by decide
  have hdescent : baseEnd_554880 < baseStart_554880 := by decide
  rcases family_descends (prefixWord ++ tailWord_554880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554954 : List Nat := [3, 1, 2, 1, 2, 1, 2, 5, 2, 4]
def baseStart_554954 : Nat := 118140960795 + 554954 * 2 ^ 59
def prefixEnd_554954 : Nat := 4983230072969 + 3 ^ 40 * 554954 * 2
def baseEnd_554954 : Nat := 94986047711775657874273

theorem tailTrace_554954 : CollatzResearch.WordTrace tailWord_554954 prefixEnd_554954 94986047711775657874273 := by
  unfold tailWord_554954
  simp only [CollatzResearch.WordTrace]
  refine ⟨5060208807875977860649979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13493890154335940961733277 5060208807875977860649979)
  ·
    refine ⟨7590313211813966790974969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5060208807875977860649979 7590313211813966790974969)
    ·
      refine ⟨5692734908860475093231227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7590313211813966790974969 5692734908860475093231227)
      ·
        refine ⟨8539102363290712639846841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5692734908860475093231227 8539102363290712639846841)
        ·
          refine ⟨6404326772468034479885131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8539102363290712639846841 6404326772468034479885131)
          ·
            refine ⟨9606490158702051719827697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6404326772468034479885131 9606490158702051719827697)
            ·
              refine ⟨7204867619026538789870773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9606490158702051719827697 7204867619026538789870773)
              ·
                refine ⟨675456339283738011550385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7204867619026538789870773 675456339283738011550385)
                ·
                  refine ⟨506592254462803508662789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 675456339283738011550385 506592254462803508662789)
                  ·
                    refine ⟨94986047711775657874273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 506592254462803508662789 94986047711775657874273)
                    ·
                      rfl

theorem cell23_554954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_554954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_554954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_554954 prefixEnd_554954 := by exact prefixLift 554954
  have htrace : WordTrace (prefixWord ++ tailWord_554954) baseStart_554954 baseEnd_554954 := by
    simpa [prefixWord, tailWord_554954, baseEnd_554954] using wordTrace_append hprefix tailTrace_554954
  have hstable : (prefixWord ++ tailWord_554954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554954).length < 2 ^ (prefixWord ++ tailWord_554954).sum := by decide
  have hdescent : baseEnd_554954 < baseStart_554954 := by decide
  rcases family_descends (prefixWord ++ tailWord_554954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555068 : List Nat := [2, 2, 2, 2, 2, 1, 1, 5, 2, 2, 2]
def baseStart_555068 : Nat := 118140960795 + 555068 * 2 ^ 59
def prefixEnd_555068 : Nat := 4983230072969 + 3 ^ 40 * 555068 * 2
def baseEnd_555068 : Nat := 285016679929939527597295

theorem tailTrace_555068 : CollatzResearch.WordTrace tailWord_555068 prefixEnd_555068 285016679929939527597295 := by
  unfold tailWord_555068
  simp only [CollatzResearch.WordTrace]
  refine ⟨10122496576545454456124929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13496662102060605941499905 10122496576545454456124929)
  ·
    refine ⟨7591872432409090842093697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10122496576545454456124929 7591872432409090842093697)
    ·
      refine ⟨5693904324306818131570273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7591872432409090842093697 5693904324306818131570273)
      ·
        refine ⟨4270428243230113598677705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5693904324306818131570273 4270428243230113598677705)
        ·
          refine ⟨3202821182422585199008279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4270428243230113598677705 3202821182422585199008279)
          ·
            refine ⟨4804231773633877798512419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3202821182422585199008279 4804231773633877798512419)
            ·
              refine ⟨7206347660450816697768629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4804231773633877798512419 7206347660450816697768629)
              ·
                refine ⟨675595093167264065415809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7206347660450816697768629 675595093167264065415809)
                ·
                  refine ⟨506696319875448049061857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 675595093167264065415809 506696319875448049061857)
                  ·
                    refine ⟨380022239906586036796393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 506696319875448049061857 380022239906586036796393)
                    ·
                      refine ⟨285016679929939527597295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 380022239906586036796393 285016679929939527597295)
                      ·
                        rfl

theorem cell23_555068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_555068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555068 prefixEnd_555068 := by exact prefixLift 555068
  have htrace : WordTrace (prefixWord ++ tailWord_555068) baseStart_555068 baseEnd_555068 := by
    simpa [prefixWord, tailWord_555068, baseEnd_555068] using wordTrace_append hprefix tailTrace_555068
  have hstable : (prefixWord ++ tailWord_555068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555068).length < 2 ^ (prefixWord ++ tailWord_555068).sum := by decide
  have hdescent : baseEnd_555068 < baseStart_555068 := by decide
  rcases family_descends (prefixWord ++ tailWord_555068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555087 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 1, 7]
def baseStart_555087 : Nat := 118140960795 + 555087 * 2 ^ 59
def prefixEnd_555087 : Nat := 4983230072969 + 3 ^ 40 * 555087 * 2
def baseEnd_555087 : Nat := 95008812020791651086569

theorem tailTrace_555087 : CollatzResearch.WordTrace tailWord_555087 prefixEnd_555087 95008812020791651086569 := by
  unfold tailWord_555087
  simp only [CollatzResearch.WordTrace]
  refine ⟨20245686140022075157191515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13497124093348050104794343 20245686140022075157191515)
  ·
    refine ⟨30368529210033112735787273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20245686140022075157191515 30368529210033112735787273)
    ·
      refine ⟨22776396907524834551840455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30368529210033112735787273 22776396907524834551840455)
      ·
        refine ⟨34164595361287251827760683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22776396907524834551840455 34164595361287251827760683)
        ·
          refine ⟨51246893041930877741641025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34164595361287251827760683 51246893041930877741641025)
          ·
            refine ⟨38435169781448158306230769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51246893041930877741641025 38435169781448158306230769)
            ·
              refine ⟨28826377336086118729673077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38435169781448158306230769 28826377336086118729673077)
              ·
                refine ⟨2702472875258073630906851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28826377336086118729673077 2702472875258073630906851)
                ·
                  refine ⟨4053709312887110446360277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702472875258073630906851 4053709312887110446360277)
                  ·
                    refine ⟨95008812020791651086569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4053709312887110446360277 95008812020791651086569)
                    ·
                      rfl

theorem cell23_555087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_555087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555087 prefixEnd_555087 := by exact prefixLift 555087
  have htrace : WordTrace (prefixWord ++ tailWord_555087) baseStart_555087 baseEnd_555087 := by
    simpa [prefixWord, tailWord_555087, baseEnd_555087] using wordTrace_append hprefix tailTrace_555087
  have hstable : (prefixWord ++ tailWord_555087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555087).length < 2 ^ (prefixWord ++ tailWord_555087).sum := by decide
  have hdescent : baseEnd_555087 < baseStart_555087 := by decide
  rcases family_descends (prefixWord ++ tailWord_555087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555164 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 8]
def baseStart_555164 : Nat := 118140960795 + 555164 * 2 ^ 59
def prefixEnd_555164 : Nat := 4983230072969 + 3 ^ 40 * 555164 * 2
def baseEnd_555164 : Nat := 31673997119196794666317

theorem tailTrace_555164 : CollatzResearch.WordTrace tailWord_555164 prefixEnd_555164 31673997119196794666317 := by
  unfold tailWord_555164
  simp only [CollatzResearch.WordTrace]
  refine ⟨10124247280371558653872273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13498996373828744871829697 10124247280371558653872273)
  ·
    refine ⟨7593185460278668990404205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10124247280371558653872273 7593185460278668990404205)
    ·
      refine ⟨2847444547604500871401577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7593185460278668990404205 2847444547604500871401577)
      ·
        refine ⟨2135583410703375653551183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2847444547604500871401577 2135583410703375653551183)
        ·
          refine ⟨3203375116055063480326775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2135583410703375653551183 3203375116055063480326775)
          ·
            refine ⟨4805062674082595220490163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3203375116055063480326775 4805062674082595220490163)
            ·
              refine ⟨7207594011123892830735245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4805062674082595220490163 7207594011123892830735245)
              ·
                refine ⟨2702847754171459811525717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7207594011123892830735245 2702847754171459811525717)
                ·
                  refine ⟨31673997119196794666317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2702847754171459811525717 31673997119196794666317)
                  ·
                    rfl

theorem cell23_555164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_555164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555164 prefixEnd_555164 := by exact prefixLift 555164
  have htrace : WordTrace (prefixWord ++ tailWord_555164) baseStart_555164 baseEnd_555164 := by
    simpa [prefixWord, tailWord_555164, baseEnd_555164] using wordTrace_append hprefix tailTrace_555164
  have hstable : (prefixWord ++ tailWord_555164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555164).length < 2 ^ (prefixWord ++ tailWord_555164).sum := by decide
  have hdescent : baseEnd_555164 < baseStart_555164 := by decide
  rcases family_descends (prefixWord ++ tailWord_555164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555168 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 3, 4]
def baseStart_555168 : Nat := 118140960795 + 555168 * 2 ^ 59
def prefixEnd_555168 : Nat := 4983230072969 + 3 ^ 40 * 555168 * 2
def baseEnd_555168 : Nat := 95022675998463045448945

theorem tailTrace_555168 : CollatzResearch.WordTrace tailWord_555168 prefixEnd_555168 95022675998463045448945 := by
  unfold tailWord_555168
  simp only [CollatzResearch.WordTrace]
  refine ⟨10124320226364312995445079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13499093635152417327260105 10124320226364312995445079)
  ·
    refine ⟨15186480339546469493167619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10124320226364312995445079 15186480339546469493167619)
    ·
      refine ⟨22779720509319704239751429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15186480339546469493167619 22779720509319704239751429)
      ·
        refine ⟨4271197595497444544953393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22779720509319704239751429 4271197595497444544953393)
        ·
          refine ⟨3203398196623083408715045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4271197595497444544953393 3203398196623083408715045)
          ·
            refine ⟨600637161866828139134071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3203398196623083408715045 600637161866828139134071)
            ·
              refine ⟨900955742800242208701107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600637161866828139134071 900955742800242208701107)
              ·
                refine ⟨1351433614200363313051661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900955742800242208701107 1351433614200363313051661)
                ·
                  refine ⟨506787605325136242394373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1351433614200363313051661 506787605325136242394373)
                  ·
                    refine ⟨95022675998463045448945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 506787605325136242394373 95022675998463045448945)
                    ·
                      rfl

theorem cell23_555168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 3, 4].length) (baseStart_555168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555168 prefixEnd_555168 := by exact prefixLift 555168
  have htrace : WordTrace (prefixWord ++ tailWord_555168) baseStart_555168 baseEnd_555168 := by
    simpa [prefixWord, tailWord_555168, baseEnd_555168] using wordTrace_append hprefix tailTrace_555168
  have hstable : (prefixWord ++ tailWord_555168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555168).length < 2 ^ (prefixWord ++ tailWord_555168).sum := by decide
  have hdescent : baseEnd_555168 < baseStart_555168 := by decide
  rcases family_descends (prefixWord ++ tailWord_555168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555231 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 2, 6, 2]
def baseStart_555231 : Nat := 118140960795 + 555231 * 2 ^ 59
def prefixEnd_555231 : Nat := 4983230072969 + 3 ^ 40 * 555231 * 2
def baseEnd_555231 : Nat := 285100377276622389859045

theorem tailTrace_555231 : CollatzResearch.WordTrace tailWord_555231 prefixEnd_555231 285100377276622389859045 := by
  unfold tailWord_555231
  simp only [CollatzResearch.WordTrace]
  refine ⟨20250938251500387750433547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13500625501000258500289031 20250938251500387750433547)
  ·
    refine ⟨30376407377250581625650321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20250938251500387750433547 30376407377250581625650321)
    ·
      refine ⟨22782305532937936219237741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30376407377250581625650321 22782305532937936219237741)
      ·
        refine ⟨8543364574851726082214153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22782305532937936219237741 8543364574851726082214153)
        ·
          refine ⟨6407523431138794561660615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8543364574851726082214153 6407523431138794561660615)
          ·
            refine ⟨9611285146708191842490923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6407523431138794561660615 9611285146708191842490923)
            ·
              refine ⟨14416927720062287763736385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9611285146708191842490923 14416927720062287763736385)
              ·
                refine ⟨10812695790046715822802289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14416927720062287763736385 10812695790046715822802289)
                ·
                  refine ⟨8109521842535036867101717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10812695790046715822802289 8109521842535036867101717)
                  ·
                    refine ⟨380133836368829853145393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8109521842535036867101717 380133836368829853145393)
                    ·
                      refine ⟨285100377276622389859045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 380133836368829853145393 285100377276622389859045)
                      ·
                        rfl

theorem cell23_555231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_555231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555231 prefixEnd_555231 := by exact prefixLift 555231
  have htrace : WordTrace (prefixWord ++ tailWord_555231) baseStart_555231 baseEnd_555231 := by
    simpa [prefixWord, tailWord_555231, baseEnd_555231] using wordTrace_append hprefix tailTrace_555231
  have hstable : (prefixWord ++ tailWord_555231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555231).length < 2 ^ (prefixWord ++ tailWord_555231).sum := by decide
  have hdescent : baseEnd_555231 < baseStart_555231 := by decide
  rcases family_descends (prefixWord ++ tailWord_555231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555251 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 3]
def baseStart_555251 : Nat := 118140960795 + 555251 * 2 ^ 59
def prefixEnd_555251 : Nat := 4983230072969 + 3 ^ 40 * 555251 * 2
def baseEnd_555251 : Nat := 285110646889712311608953

theorem tailTrace_555251 : CollatzResearch.WordTrace tailWord_555251 prefixEnd_555251 285110646889712311608953 := by
  unfold tailWord_555251
  simp only [CollatzResearch.WordTrace]
  refine ⟨20251667711427931166161607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13501111807618620777441071 20251667711427931166161607)
  ·
    refine ⟨30377501567141896749242411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20251667711427931166161607 30377501567141896749242411)
    ·
      refine ⟨45566252350712845123863617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30377501567141896749242411 45566252350712845123863617)
      ·
        refine ⟨34174689263034633842897713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45566252350712845123863617 34174689263034633842897713)
        ·
          refine ⟨25631016947275975382173285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34174689263034633842897713 25631016947275975382173285)
          ·
            refine ⟨4805815677614245384157491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25631016947275975382173285 4805815677614245384157491)
            ·
              refine ⟨7208723516421368076236237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4805815677614245384157491 7208723516421368076236237)
              ·
                refine ⟨2703271318658013028588589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7208723516421368076236237 2703271318658013028588589)
                ·
                  refine ⟨1013726744496754885720721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2703271318658013028588589 1013726744496754885720721)
                  ·
                    refine ⟨760295058372566164290541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1013726744496754885720721 760295058372566164290541)
                    ·
                      refine ⟨285110646889712311608953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 760295058372566164290541 285110646889712311608953)
                      ·
                        rfl

theorem cell23_555251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 3].length) (baseStart_555251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555251 prefixEnd_555251 := by exact prefixLift 555251
  have htrace : WordTrace (prefixWord ++ tailWord_555251) baseStart_555251 baseEnd_555251 := by
    simpa [prefixWord, tailWord_555251, baseEnd_555251] using wordTrace_append hprefix tailTrace_555251
  have hstable : (prefixWord ++ tailWord_555251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555251).length < 2 ^ (prefixWord ++ tailWord_555251).sum := by decide
  have hdescent : baseEnd_555251 < baseStart_555251 := by decide
  rcases family_descends (prefixWord ++ tailWord_555251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555308 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 3, 3, 2]
def baseStart_555308 : Nat := 118140960795 + 555308 * 2 ^ 59
def prefixEnd_555308 : Nat := 4983230072969 + 3 ^ 40 * 555308 * 2
def baseEnd_555308 : Nat := 285139915287018588596191

theorem tailTrace_555308 : CollatzResearch.WordTrace tailWord_555308 prefixEnd_555308 285139915287018588596191 := by
  unfold tailWord_555308
  simp only [CollatzResearch.WordTrace]
  refine ⟨10126873336110714950493289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13502497781480953267324385 10126873336110714950493289)
  ·
    refine ⟨7595155002083036212869967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10126873336110714950493289 7595155002083036212869967)
    ·
      refine ⟨11392732503124554319304951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7595155002083036212869967 11392732503124554319304951)
      ·
        refine ⟨17089098754686831478957427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11392732503124554319304951 17089098754686831478957427)
        ·
          refine ⟨25633648132030247218436141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17089098754686831478957427 25633648132030247218436141)
          ·
            refine ⟨9612618049511342706913553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25633648132030247218436141 9612618049511342706913553)
            ·
              refine ⟨7209463537133507030185165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9612618049511342706913553 7209463537133507030185165)
              ·
                refine ⟨2703548826425065136319437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7209463537133507030185165 2703548826425065136319437)
                ·
                  refine ⟨1013830809909399426119789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2703548826425065136319437 1013830809909399426119789)
                  ·
                    refine ⟨380186553716024784794921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1013830809909399426119789 380186553716024784794921)
                    ·
                      refine ⟨285139915287018588596191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 380186553716024784794921 285139915287018588596191)
                      ·
                        rfl

theorem cell23_555308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 3, 2].length) (baseStart_555308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555308 prefixEnd_555308 := by exact prefixLift 555308
  have htrace : WordTrace (prefixWord ++ tailWord_555308) baseStart_555308 baseEnd_555308 := by
    simpa [prefixWord, tailWord_555308, baseEnd_555308] using wordTrace_append hprefix tailTrace_555308
  have hstable : (prefixWord ++ tailWord_555308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555308).length < 2 ^ (prefixWord ++ tailWord_555308).sum := by decide
  have hdescent : baseEnd_555308 < baseStart_555308 := by decide
  rcases family_descends (prefixWord ++ tailWord_555308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555316 : List Nat := [2, 5, 1, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_555316 : Nat := 118140960795 + 555316 * 2 ^ 59
def prefixEnd_555316 : Nat := 4983230072969 + 3 ^ 40 * 555316 * 2
def baseEnd_555316 : Nat := 285144023132254557296155

theorem tailTrace_555316 : CollatzResearch.WordTrace tailWord_555316 prefixEnd_555316 285144023132254557296155 := by
  unfold tailWord_555316
  simp only [CollatzResearch.WordTrace]
  refine ⟨10127019228096223633638901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13502692304128298178185201 10127019228096223633638901)
  ·
    refine ⟨949408052634020965653647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10127019228096223633638901 949408052634020965653647)
    ·
      refine ⟨1424112078951031448480471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 949408052634020965653647 1424112078951031448480471)
      ·
        refine ⟨2136168118426547172720707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1424112078951031448480471 2136168118426547172720707)
        ·
          refine ⟨3204252177639820759081061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2136168118426547172720707 3204252177639820759081061)
          ·
            refine ⟨600797283307466392327699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3204252177639820759081061 600797283307466392327699)
            ·
              refine ⟨901195924961199588491549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600797283307466392327699 901195924961199588491549)
              ·
                refine ⟨337948471860449845684331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 901195924961199588491549 337948471860449845684331)
                ·
                  refine ⟨506922707790674768526497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337948471860449845684331 506922707790674768526497)
                  ·
                    refine ⟨380192030843006076394873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 506922707790674768526497 380192030843006076394873)
                    ·
                      refine ⟨285144023132254557296155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 380192030843006076394873 285144023132254557296155)
                      ·
                        rfl

theorem cell23_555316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_555316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555316 prefixEnd_555316 := by exact prefixLift 555316
  have htrace : WordTrace (prefixWord ++ tailWord_555316) baseStart_555316 baseEnd_555316 := by
    simpa [prefixWord, tailWord_555316, baseEnd_555316] using wordTrace_append hprefix tailTrace_555316
  have hstable : (prefixWord ++ tailWord_555316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555316).length < 2 ^ (prefixWord ++ tailWord_555316).sum := by decide
  have hdescent : baseEnd_555316 < baseStart_555316 := by decide
  rcases family_descends (prefixWord ++ tailWord_555316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555349 : List Nat := [1, 3, 2, 2, 4, 2, 2, 1, 2, 1, 3]
def baseStart_555349 : Nat := 118140960795 + 555349 * 2 ^ 59
def prefixEnd_555349 : Nat := 4983230072969 + 3 ^ 40 * 555349 * 2
def baseEnd_555349 : Nat := 285160967993852928183503

theorem tailTrace_555349 : CollatzResearch.WordTrace tailWord_555349 prefixEnd_555349 285160967993852928183503 := by
  unfold tailWord_555349
  simp only [CollatzResearch.WordTrace]
  refine ⟨20255242065072893903229101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13503494710048595935486067 20255242065072893903229101)
  ·
    refine ⟨7595715774402335213710913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20255242065072893903229101 7595715774402335213710913)
    ·
      refine ⟨5696786830801751410283185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7595715774402335213710913 5696786830801751410283185)
      ·
        refine ⟨4272590123101313557712389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5696786830801751410283185 4272590123101313557712389)
        ·
          refine ⟨801110648081496292071073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4272590123101313557712389 801110648081496292071073)
          ·
            refine ⟨600832986061122219053305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 801110648081496292071073 600832986061122219053305)
            ·
              refine ⟨450624739545841664289979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600832986061122219053305 450624739545841664289979)
              ·
                refine ⟨675937109318762496434969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450624739545841664289979 675937109318762496434969)
                ·
                  refine ⟨506952831989071872326227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 675937109318762496434969 506952831989071872326227)
                  ·
                    refine ⟨760429247983607808489341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 506952831989071872326227 760429247983607808489341)
                    ·
                      refine ⟨285160967993852928183503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 760429247983607808489341 285160967993852928183503)
                      ·
                        rfl

theorem cell23_555349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_555349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555349 prefixEnd_555349 := by exact prefixLift 555349
  have htrace : WordTrace (prefixWord ++ tailWord_555349) baseStart_555349 baseEnd_555349 := by
    simpa [prefixWord, tailWord_555349, baseEnd_555349] using wordTrace_append hprefix tailTrace_555349
  have hstable : (prefixWord ++ tailWord_555349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555349).length < 2 ^ (prefixWord ++ tailWord_555349).sum := by decide
  have hdescent : baseEnd_555349 < baseStart_555349 := by decide
  rcases family_descends (prefixWord ++ tailWord_555349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555351 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_555351 : Nat := 118140960795 + 555351 * 2 ^ 59
def prefixEnd_555351 : Nat := 4983230072969 + 3 ^ 40 * 555351 * 2
def baseEnd_555351 : Nat := 285161994955161920358493

theorem tailTrace_555351 : CollatzResearch.WordTrace tailWord_555351 prefixEnd_555351 285161994955161920358493 := by
  unfold tailWord_555351
  simp only [CollatzResearch.WordTrace]
  refine ⟨20255315011065648244801907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13503543340710432163201271 20255315011065648244801907)
  ·
    refine ⟨30382972516598472367202861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20255315011065648244801907 30382972516598472367202861)
    ·
      refine ⟨11393614693724427137701073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30382972516598472367202861 11393614693724427137701073)
      ·
        refine ⟨8545211020293320353275805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11393614693724427137701073 8545211020293320353275805)
        ·
          refine ⟨3204454132609995132478427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8545211020293320353275805 3204454132609995132478427)
          ·
            refine ⟨4806681198914992698717641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3204454132609995132478427 4806681198914992698717641)
            ·
              refine ⟨3605010899186244524038231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4806681198914992698717641 3605010899186244524038231)
              ·
                refine ⟨5407516348779366786057347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3605010899186244524038231 5407516348779366786057347)
                ·
                  refine ⟨8111274523169050179086021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5407516348779366786057347 8111274523169050179086021)
                  ·
                    refine ⟨1520863973094196908578629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8111274523169050179086021 1520863973094196908578629)
                    ·
                      refine ⟨285161994955161920358493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1520863973094196908578629 285161994955161920358493)
                      ·
                        rfl

theorem cell23_555351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_555351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555351 prefixEnd_555351 := by exact prefixLift 555351
  have htrace : WordTrace (prefixWord ++ tailWord_555351) baseStart_555351 baseEnd_555351 := by
    simpa [prefixWord, tailWord_555351, baseEnd_555351] using wordTrace_append hprefix tailTrace_555351
  have hstable : (prefixWord ++ tailWord_555351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555351).length < 2 ^ (prefixWord ++ tailWord_555351).sum := by decide
  have hdescent : baseEnd_555351 < baseStart_555351 := by decide
  rcases family_descends (prefixWord ++ tailWord_555351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555371 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 3]
def baseStart_555371 : Nat := 118140960795 + 555371 * 2 ^ 59
def prefixEnd_555371 : Nat := 4983230072969 + 3 ^ 40 * 555371 * 2
def baseEnd_555371 : Nat := 285172264568251842108401

theorem tailTrace_555371 : CollatzResearch.WordTrace tailWord_555371 prefixEnd_555371 285172264568251842108401 := by
  unfold tailWord_555371
  simp only [CollatzResearch.WordTrace]
  refine ⟨20256044470993191660529967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13504029647328794440353311 20256044470993191660529967)
  ·
    refine ⟨30384066706489787490794951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20256044470993191660529967 30384066706489787490794951)
    ·
      refine ⟨45576100059734681236192427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30384066706489787490794951 45576100059734681236192427)
      ·
        refine ⟨68364150089602021854288641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45576100059734681236192427 68364150089602021854288641)
        ·
          refine ⟨51273112567201516390716481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68364150089602021854288641 51273112567201516390716481)
          ·
            refine ⟨38454834425401137293037361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51273112567201516390716481 38454834425401137293037361)
            ·
              refine ⟨28841125819050852969778021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38454834425401137293037361 28841125819050852969778021)
              ·
                refine ⟨5407711091072034931833379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28841125819050852969778021 5407711091072034931833379)
                ·
                  refine ⟨8111566636608052397750069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5407711091072034931833379 8111566636608052397750069)
                  ·
                    refine ⟨760459372182004912289069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8111566636608052397750069 760459372182004912289069)
                    ·
                      refine ⟨285172264568251842108401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 760459372182004912289069 285172264568251842108401)
                      ·
                        rfl

theorem cell23_555371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 3].length) (baseStart_555371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555371 prefixEnd_555371 := by exact prefixLift 555371
  have htrace : WordTrace (prefixWord ++ tailWord_555371) baseStart_555371 baseEnd_555371 := by
    simpa [prefixWord, tailWord_555371, baseEnd_555371] using wordTrace_append hprefix tailTrace_555371
  have hstable : (prefixWord ++ tailWord_555371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555371).length < 2 ^ (prefixWord ++ tailWord_555371).sum := by decide
  have hdescent : baseEnd_555371 < baseStart_555371 := by decide
  rcases family_descends (prefixWord ++ tailWord_555371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555395 : List Nat := [1, 1, 1, 3, 6, 1, 1, 4, 5]
def baseStart_555395 : Nat := 118140960795 + 555395 * 2 ^ 59
def prefixEnd_555395 : Nat := 4983230072969 + 3 ^ 40 * 555395 * 2
def baseEnd_555395 : Nat := 31687176455995527578699

theorem tailTrace_555395 : CollatzResearch.WordTrace tailWord_555395 prefixEnd_555395 31687176455995527578699 := by
  unfold tailWord_555395
  simp only [CollatzResearch.WordTrace]
  refine ⟨20256919822906243759403639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13504613215270829172935759 20256919822906243759403639)
  ·
    refine ⟨30385379734359365639105459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20256919822906243759403639 30385379734359365639105459)
    ·
      refine ⟨45578069601539048458658189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30385379734359365639105459 45578069601539048458658189)
      ·
        refine ⟨17091776100577143171996821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45578069601539048458658189 17091776100577143171996821)
        ·
          refine ⟨801177004714553586187351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17091776100577143171996821 801177004714553586187351)
          ·
            refine ⟨1201765507071830379281027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801177004714553586187351 1201765507071830379281027)
            ·
              refine ⟨1802648260607745568921541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201765507071830379281027 1802648260607745568921541)
              ·
                refine ⟨337996548863952294172789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1802648260607745568921541 337996548863952294172789)
                ·
                  refine ⟨31687176455995527578699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 337996548863952294172789 31687176455995527578699)
                  ·
                    rfl

theorem cell23_555395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 5].length) (baseStart_555395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555395 prefixEnd_555395 := by exact prefixLift 555395
  have htrace : WordTrace (prefixWord ++ tailWord_555395) baseStart_555395 baseEnd_555395 := by
    simpa [prefixWord, tailWord_555395, baseEnd_555395] using wordTrace_append hprefix tailTrace_555395
  have hstable : (prefixWord ++ tailWord_555395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555395).length < 2 ^ (prefixWord ++ tailWord_555395).sum := by decide
  have hdescent : baseEnd_555395 < baseStart_555395 := by decide
  rcases family_descends (prefixWord ++ tailWord_555395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555425 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 1, 7]
def baseStart_555425 : Nat := 118140960795 + 555425 * 2 ^ 59
def prefixEnd_555425 : Nat := 4983230072969 + 3 ^ 40 * 555425 * 2
def baseEnd_555425 : Nat := 95066664174531543611051

theorem tailTrace_555425 : CollatzResearch.WordTrace tailWord_555425 prefixEnd_555425 95066664174531543611051 := by
  unfold tailWord_555425
  simp only [CollatzResearch.WordTrace]
  refine ⟨20258014012797558882995729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13505342675198372588663819 20258014012797558882995729)
  ·
    refine ⟨15193510509598169162246797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20258014012797558882995729 15193510509598169162246797)
    ·
      refine ⟨5697566441099313435842549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15193510509598169162246797 5697566441099313435842549)
      ·
        refine ⟨534146853853060634610239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5697566441099313435842549 534146853853060634610239)
        ·
          refine ⟨801220280779590951915359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534146853853060634610239 801220280779590951915359)
          ·
            refine ⟨1201830421169386427873039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801220280779590951915359 1201830421169386427873039)
            ·
              refine ⟨1802745631754079641809559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201830421169386427873039 1802745631754079641809559)
              ·
                refine ⟨2704118447631119462714339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802745631754079641809559 2704118447631119462714339)
                ·
                  refine ⟨4056177671446679194071509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704118447631119462714339 4056177671446679194071509)
                  ·
                    refine ⟨95066664174531543611051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4056177671446679194071509 95066664174531543611051)
                    ·
                      rfl

theorem cell23_555425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_555425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555425 prefixEnd_555425 := by exact prefixLift 555425
  have htrace : WordTrace (prefixWord ++ tailWord_555425) baseStart_555425 baseEnd_555425 := by
    simpa [prefixWord, tailWord_555425, baseEnd_555425] using wordTrace_append hprefix tailTrace_555425
  have hstable : (prefixWord ++ tailWord_555425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555425).length < 2 ^ (prefixWord ++ tailWord_555425).sum := by decide
  have hdescent : baseEnd_555425 < baseStart_555425 := by decide
  rcases family_descends (prefixWord ++ tailWord_555425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555448 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 4, 2, 3]
def baseStart_555448 : Nat := 118140960795 + 555448 * 2 ^ 59
def prefixEnd_555448 : Nat := 4983230072969 + 3 ^ 40 * 555448 * 2
def baseEnd_555448 : Nat := 285211802578648040845547

theorem tailTrace_555448 : CollatzResearch.WordTrace tailWord_555448 prefixEnd_555448 285211802578648040845547 := by
  unfold tailWord_555448
  simp only [CollatzResearch.WordTrace]
  refine ⟨10129426445857116905541499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13505901927809489207388665 10129426445857116905541499)
  ·
    refine ⟨15194139668785675358312249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10129426445857116905541499 15194139668785675358312249)
    ·
      refine ⟨11395604751589256518734187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15194139668785675358312249 11395604751589256518734187)
      ·
        refine ⟨17093407127383884778101281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11395604751589256518734187 17093407127383884778101281)
        ·
          refine ⟨12820055345537913583575961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17093407127383884778101281 12820055345537913583575961)
          ·
            refine ⟨9615041509153435187681971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12820055345537913583575961 9615041509153435187681971)
            ·
              refine ⟨14422562263730152781522957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9615041509153435187681971 14422562263730152781522957)
              ·
                refine ⟨5408460848898807293071109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14422562263730152781522957 5408460848898807293071109)
                ·
                  refine ⟨1014086409168526367450833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5408460848898807293071109 1014086409168526367450833)
                  ·
                    refine ⟨760564806876394775588125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1014086409168526367450833 760564806876394775588125)
                    ·
                      refine ⟨285211802578648040845547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 760564806876394775588125 285211802578648040845547)
                      ·
                        rfl

theorem cell23_555448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_555448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555448 prefixEnd_555448 := by exact prefixLift 555448
  have htrace : WordTrace (prefixWord ++ tailWord_555448) baseStart_555448 baseEnd_555448 := by
    simpa [prefixWord, tailWord_555448, baseEnd_555448] using wordTrace_append hprefix tailTrace_555448
  have hstable : (prefixWord ++ tailWord_555448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555448).length < 2 ^ (prefixWord ++ tailWord_555448).sum := by decide
  have hdescent : baseEnd_555448 < baseStart_555448 := by decide
  rcases family_descends (prefixWord ++ tailWord_555448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555471 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 6]
def baseStart_555471 : Nat := 118140960795 + 555471 * 2 ^ 59
def prefixEnd_555471 : Nat := 4983230072969 + 3 ^ 40 * 555471 * 2
def baseEnd_555471 : Nat := 285223612633701450857941

theorem tailTrace_555471 : CollatzResearch.WordTrace tailWord_555471 prefixEnd_555471 285223612633701450857941 := by
  unfold tailWord_555471
  simp only [CollatzResearch.WordTrace]
  refine ⟨20259691770630908739170267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13506461180420605826113511 20259691770630908739170267)
  ·
    refine ⟨30389537655946363108755401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20259691770630908739170267 30389537655946363108755401)
    ·
      refine ⟨22792153241959772331566551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30389537655946363108755401 22792153241959772331566551)
      ·
        refine ⟨34188229862939658497349827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22792153241959772331566551 34188229862939658497349827)
        ·
          refine ⟨51282344794409487746024741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34188229862939658497349827 51282344794409487746024741)
          ·
            refine ⟨9615439648951778952379639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51282344794409487746024741 9615439648951778952379639)
            ·
              refine ⟨14423159473427668428569459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9615439648951778952379639 14423159473427668428569459)
              ·
                refine ⟨21634739210141502642854189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14423159473427668428569459 21634739210141502642854189)
                ·
                  refine ⟨8113027203803063491070321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21634739210141502642854189 8113027203803063491070321)
                  ·
                    refine ⟨6084770402852297618302741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8113027203803063491070321 6084770402852297618302741)
                    ·
                      refine ⟨285223612633701450857941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6084770402852297618302741 285223612633701450857941)
                      ·
                        rfl

theorem cell23_555471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_555471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555471 prefixEnd_555471 := by exact prefixLift 555471
  have htrace : WordTrace (prefixWord ++ tailWord_555471) baseStart_555471 baseEnd_555471 := by
    simpa [prefixWord, tailWord_555471, baseEnd_555471] using wordTrace_append hprefix tailTrace_555471
  have hstable : (prefixWord ++ tailWord_555471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555471).length < 2 ^ (prefixWord ++ tailWord_555471).sum := by decide
  have hdescent : baseEnd_555471 < baseStart_555471 := by decide
  rcases family_descends (prefixWord ++ tailWord_555471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555506 : List Nat := [3, 2, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_555506 : Nat := 118140960795 + 555506 * 2 ^ 59
def prefixEnd_555506 : Nat := 4983230072969 + 3 ^ 40 * 555506 * 2
def baseEnd_555506 : Nat := 95080528152202937973427

theorem tailTrace_555506 : CollatzResearch.WordTrace tailWord_555506 prefixEnd_555506 95080528152202937973427 := by
  unfold tailWord_555506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5065242081376027429173593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13507312217002739811129581 5065242081376027429173593)
  ·
    refine ⟨3798931561032020571880195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5065242081376027429173593 3798931561032020571880195)
    ·
      refine ⟨5698397341548030857820293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3798931561032020571880195 5698397341548030857820293)
      ·
        refine ⟨1068449501540255785841305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5698397341548030857820293 1068449501540255785841305)
        ·
          refine ⟨801337126155191839380979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1068449501540255785841305 801337126155191839380979)
          ·
            refine ⟨1202005689232787759071469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801337126155191839380979 1202005689232787759071469)
            ·
              refine ⟨450752133462295409651801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1202005689232787759071469 450752133462295409651801)
              ·
                refine ⟨338064100096721557238851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450752133462295409651801 338064100096721557238851)
                ·
                  refine ⟨507096150145082335858277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338064100096721557238851 507096150145082335858277)
                  ·
                    refine ⟨95080528152202937973427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 507096150145082335858277 95080528152202937973427)
                    ·
                      rfl

theorem cell23_555506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_555506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555506 prefixEnd_555506 := by exact prefixLift 555506
  have htrace : WordTrace (prefixWord ++ tailWord_555506) baseStart_555506 baseEnd_555506 := by
    simpa [prefixWord, tailWord_555506, baseEnd_555506] using wordTrace_append hprefix tailTrace_555506
  have hstable : (prefixWord ++ tailWord_555506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555506).length < 2 ^ (prefixWord ++ tailWord_555506).sum := by decide
  have hdescent : baseEnd_555506 < baseStart_555506 := by decide
  rcases family_descends (prefixWord ++ tailWord_555506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555528 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 1, 6]
def baseStart_555528 : Nat := 118140960795 + 555528 * 2 ^ 59
def prefixEnd_555528 : Nat := 4983230072969 + 3 ^ 40 * 555528 * 2
def baseEnd_555528 : Nat := 95084293677002575948393

theorem tailTrace_555528 : CollatzResearch.WordTrace tailWord_555528 prefixEnd_555528 95084293677002575948393 := by
  unfold tailWord_555528
  simp only [CollatzResearch.WordTrace]
  refine ⟨10130885365712203736997619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13507847154282938315996825 10130885365712203736997619)
  ·
    refine ⟨15196328048568305605496429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10130885365712203736997619 15196328048568305605496429)
    ·
      refine ⟨5698623018213114602061161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15196328048568305605496429 5698623018213114602061161)
      ·
        refine ⟨4273967263659835951545871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5698623018213114602061161 4273967263659835951545871)
        ·
          refine ⟨6410950895489753927318807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4273967263659835951545871 6410950895489753927318807)
          ·
            refine ⟨9616426343234630890978211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6410950895489753927318807 9616426343234630890978211)
            ·
              refine ⟨14424639514851946336467317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9616426343234630890978211 14424639514851946336467317)
              ·
                refine ⟨1352309954517369969043811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14424639514851946336467317 1352309954517369969043811)
                ·
                  refine ⟨2028464931776054953565717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352309954517369969043811 2028464931776054953565717)
                  ·
                    refine ⟨95084293677002575948393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2028464931776054953565717 95084293677002575948393)
                    ·
                      rfl

theorem cell23_555528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_555528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555528 prefixEnd_555528 := by exact prefixLift 555528
  have htrace : WordTrace (prefixWord ++ tailWord_555528) baseStart_555528 baseEnd_555528 := by
    simpa [prefixWord, tailWord_555528, baseEnd_555528] using wordTrace_append hprefix tailTrace_555528
  have hstable : (prefixWord ++ tailWord_555528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555528).length < 2 ^ (prefixWord ++ tailWord_555528).sum := by decide
  have hdescent : baseEnd_555528 < baseStart_555528 := by decide
  rcases family_descends (prefixWord ++ tailWord_555528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555532 : List Nat := [2, 2, 1, 2, 4, 3, 1, 2, 1, 5]
def baseStart_555532 : Nat := 118140960795 + 555532 * 2 ^ 59
def prefixEnd_555532 : Nat := 4983230072969 + 3 ^ 40 * 555532 * 2
def baseEnd_555532 : Nat := 95084978317875237398387

theorem tailTrace_555532 : CollatzResearch.WordTrace tailWord_555532 prefixEnd_555532 95084978317875237398387 := by
  unfold tailWord_555532
  simp only [CollatzResearch.WordTrace]
  refine ⟨10130958311704958078570425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13507944415606610771427233 10130958311704958078570425)
  ·
    refine ⟨7598218733778718558927819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10130958311704958078570425 7598218733778718558927819)
    ·
      refine ⟨11397328100668077838391729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7598218733778718558927819 11397328100668077838391729)
      ·
        refine ⟨8547996075501058378793797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11397328100668077838391729 8547996075501058378793797)
        ·
          refine ⟨1602749264156448446023837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8547996075501058378793797 1602749264156448446023837)
          ·
            refine ⟨601030974058668167258939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1602749264156448446023837 601030974058668167258939)
            ·
              refine ⟨901546461088002250888409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601030974058668167258939 901546461088002250888409)
              ·
                refine ⟨676159845816001688166307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 901546461088002250888409 676159845816001688166307)
                ·
                  refine ⟨1014239768724002532249461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 676159845816001688166307 1014239768724002532249461)
                  ·
                    refine ⟨95084978317875237398387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1014239768724002532249461 95084978317875237398387)
                    ·
                      rfl

theorem cell23_555532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_555532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555532 prefixEnd_555532 := by exact prefixLift 555532
  have htrace : WordTrace (prefixWord ++ tailWord_555532) baseStart_555532 baseEnd_555532 := by
    simpa [prefixWord, tailWord_555532, baseEnd_555532] using wordTrace_append hprefix tailTrace_555532
  have hstable : (prefixWord ++ tailWord_555532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555532).length < 2 ^ (prefixWord ++ tailWord_555532).sum := by decide
  have hdescent : baseEnd_555532 < baseStart_555532 := by decide
  rcases family_descends (prefixWord ++ tailWord_555532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555555 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 5]
def baseStart_555555 : Nat := 118140960795 + 555555 * 2 ^ 59
def prefixEnd_555555 : Nat := 4983230072969 + 3 ^ 40 * 555555 * 2
def baseEnd_555555 : Nat := 285266745008679122207555

theorem tailTrace_555555 : CollatzResearch.WordTrace tailWord_555555 prefixEnd_555555 285266745008679122207555 := by
  unfold tailWord_555555
  simp only [CollatzResearch.WordTrace]
  refine ⟨20262755502326591085228119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13508503668217727390152079 20262755502326591085228119)
  ·
    refine ⟨30394133253489886627842179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20262755502326591085228119 30394133253489886627842179)
    ·
      refine ⟨45591199880234829941763269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30394133253489886627842179 45591199880234829941763269)
      ·
        refine ⟨8548349977544030614080613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45591199880234829941763269 8548349977544030614080613)
        ·
          refine ⟨1602815620789505740140115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8548349977544030614080613 1602815620789505740140115)
          ·
            refine ⟨2404223431184258610210173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602815620789505740140115 2404223431184258610210173)
            ·
              refine ⟨901583786694096978828815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2404223431184258610210173 901583786694096978828815)
              ·
                refine ⟨1352375680041145468243223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 901583786694096978828815 1352375680041145468243223)
                ·
                  refine ⟨2028563520061718202364835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352375680041145468243223 2028563520061718202364835)
                  ·
                    refine ⟨3042845280092577303547253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2028563520061718202364835 3042845280092577303547253)
                    ·
                      refine ⟨285266745008679122207555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3042845280092577303547253 285266745008679122207555)
                      ·
                        rfl

theorem cell23_555555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_555555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555555 prefixEnd_555555 := by exact prefixLift 555555
  have htrace : WordTrace (prefixWord ++ tailWord_555555) baseStart_555555 baseEnd_555555 := by
    simpa [prefixWord, tailWord_555555, baseEnd_555555] using wordTrace_append hprefix tailTrace_555555
  have hstable : (prefixWord ++ tailWord_555555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555555).length < 2 ^ (prefixWord ++ tailWord_555555).sum := by decide
  have hdescent : baseEnd_555555 < baseStart_555555 := by decide
  rcases family_descends (prefixWord ++ tailWord_555555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555562 : List Nat := [3, 1, 4, 1, 1, 2, 1, 4, 2, 4]
def baseStart_555562 : Nat := 118140960795 + 555562 * 2 ^ 59
def prefixEnd_555562 : Nat := 4983230072969 + 3 ^ 40 * 555562 * 2
def baseEnd_555562 : Nat := 95090113124420198273341

theorem tailTrace_555562 : CollatzResearch.WordTrace tailWord_555562 prefixEnd_555562 95090113124420198273341 := by
  unfold tailWord_555562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5065752703325307820183235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13508673875534154187155293 5065752703325307820183235)
  ·
    refine ⟨7598629054987961730274853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5065752703325307820183235 7598629054987961730274853)
    ·
      refine ⟨1424742947810242824426535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7598629054987961730274853 1424742947810242824426535)
      ·
        refine ⟨2137114421715364236639803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1424742947810242824426535 2137114421715364236639803)
        ·
          refine ⟨3205671632573046354959705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137114421715364236639803 3205671632573046354959705)
          ·
            refine ⟨2404253724429784766219779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3205671632573046354959705 2404253724429784766219779)
            ·
              refine ⟨3606380586644677149329669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2404253724429784766219779 3606380586644677149329669)
              ·
                refine ⟨676196359995876965499313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3606380586644677149329669 676196359995876965499313)
                ·
                  refine ⟨507147269996907724124485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 676196359995876965499313 507147269996907724124485)
                  ·
                    refine ⟨95090113124420198273341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 507147269996907724124485 95090113124420198273341)
                    ·
                      rfl

theorem cell23_555562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_555562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555562 prefixEnd_555562 := by exact prefixLift 555562
  have htrace : WordTrace (prefixWord ++ tailWord_555562) baseStart_555562 baseEnd_555562 := by
    simpa [prefixWord, tailWord_555562, baseEnd_555562] using wordTrace_append hprefix tailTrace_555562
  have hstable : (prefixWord ++ tailWord_555562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555562).length < 2 ^ (prefixWord ++ tailWord_555562).sum := by decide
  have hdescent : baseEnd_555562 < baseStart_555562 := by decide
  rcases family_descends (prefixWord ++ tailWord_555562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555602 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_555602 : Nat := 118140960795 + 555602 * 2 ^ 59
def prefixEnd_555602 : Nat := 4983230072969 + 3 ^ 40 * 555602 * 2
def baseEnd_555602 : Nat := 285290878599440438319839

theorem tailTrace_555602 : CollatzResearch.WordTrace tailWord_555602 prefixEnd_555602 285290878599440438319839 := by
  unfold tailWord_555602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5066117433289079528047265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13509646488770878741459373 5066117433289079528047265)
  ·
    refine ⟨3799588074966809646035449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5066117433289079528047265 3799588074966809646035449)
    ·
      refine ⟨2849691056225107234526587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3799588074966809646035449 2849691056225107234526587)
      ·
        refine ⟨4274536584337660851789881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2849691056225107234526587 4274536584337660851789881)
        ·
          refine ⟨3205902438253245638842411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4274536584337660851789881 3205902438253245638842411)
          ·
            refine ⟨4808853657379868458263617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3205902438253245638842411 4808853657379868458263617)
            ·
              refine ⟨3606640243034901343697713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4808853657379868458263617 3606640243034901343697713)
              ·
                refine ⟨2704980182276176007773285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3606640243034901343697713 2704980182276176007773285)
                ·
                  refine ⟨507183784176783001457491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2704980182276176007773285 507183784176783001457491)
                  ·
                    refine ⟨760775676265174502186237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 507183784176783001457491 760775676265174502186237)
                    ·
                      refine ⟨285290878599440438319839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 760775676265174502186237 285290878599440438319839)
                      ·
                        rfl

theorem cell23_555602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_555602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555602 prefixEnd_555602 := by exact prefixLift 555602
  have htrace : WordTrace (prefixWord ++ tailWord_555602) baseStart_555602 baseEnd_555602 := by
    simpa [prefixWord, tailWord_555602, baseEnd_555602] using wordTrace_append hprefix tailTrace_555602
  have hstable : (prefixWord ++ tailWord_555602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555602).length < 2 ^ (prefixWord ++ tailWord_555602).sum := by decide
  have hdescent : baseEnd_555602 < baseStart_555602 := by decide
  rcases family_descends (prefixWord ++ tailWord_555602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555693 : List Nat := [1, 5, 2, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_555693 : Nat := 118140960795 + 555693 * 2 ^ 59
def prefixEnd_555693 : Nat := 4983230072969 + 3 ^ 40 * 555693 * 2
def baseEnd_555693 : Nat := 285337605338999582281921

theorem tailTrace_555693 : CollatzResearch.WordTrace tailWord_555693 prefixEnd_555693 285337605338999582281921 := by
  unfold tailWord_555693
  simp only [CollatzResearch.WordTrace]
  refine ⟨20267788775826640653751733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13511859183884427102501155 20267788775826640653751733)
  ·
    refine ⟨1900105197733747561289225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20267788775826640653751733 1900105197733747561289225)
    ·
      refine ⟨1425078898300310670966919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1900105197733747561289225 1425078898300310670966919)
      ·
        refine ⟨2137618347450466006450379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1425078898300310670966919 2137618347450466006450379)
        ·
          refine ⟨3206427521175699009675569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137618347450466006450379 3206427521175699009675569)
          ·
            refine ⟨2404820640881774257256677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3206427521175699009675569 2404820640881774257256677)
            ·
              refine ⟨450903870165332673235627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2404820640881774257256677 450903870165332673235627)
              ·
                refine ⟨676355805247999009853441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450903870165332673235627 676355805247999009853441)
                ·
                  refine ⟨507266853935999257390081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 676355805247999009853441 507266853935999257390081)
                  ·
                    refine ⟨380450140451999443042561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 507266853935999257390081 380450140451999443042561)
                    ·
                      refine ⟨285337605338999582281921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 380450140451999443042561 285337605338999582281921)
                      ·
                        rfl

theorem cell23_555693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_555693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555693 prefixEnd_555693 := by exact prefixLift 555693
  have htrace : WordTrace (prefixWord ++ tailWord_555693) baseStart_555693 baseEnd_555693 := by
    simpa [prefixWord, tailWord_555693, baseEnd_555693] using wordTrace_append hprefix tailTrace_555693
  have hstable : (prefixWord ++ tailWord_555693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555693).length < 2 ^ (prefixWord ++ tailWord_555693).sum := by decide
  have hdescent : baseEnd_555693 < baseStart_555693 := by decide
  rcases family_descends (prefixWord ++ tailWord_555693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555712 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 2, 5]
def baseStart_555712 : Nat := 118140960795 + 555712 * 2 ^ 59
def prefixEnd_555712 : Nat := 4983230072969 + 3 ^ 40 * 555712 * 2
def baseEnd_555712 : Nat := 95115787157145002648111

theorem tailTrace_555712 : CollatzResearch.WordTrace tailWord_555712 prefixEnd_555712 95115787157145002648111 := by
  unfold tailWord_555712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10134240881378903449346695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13512321175171871265795593 10134240881378903449346695)
  ·
    refine ⟨15201361322068355174020043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10134240881378903449346695 15201361322068355174020043)
    ·
      refine ⟨22802041983102532761030065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15201361322068355174020043 22802041983102532761030065)
      ·
        refine ⟨17101531487326899570772549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22802041983102532761030065 17101531487326899570772549)
        ·
          refine ⟨3206537153873793669519853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17101531487326899570772549 3206537153873793669519853)
          ·
            refine ⟨1202451432702672626069945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3206537153873793669519853 1202451432702672626069945)
            ·
              refine ⟨901838574527004469552459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1202451432702672626069945 901838574527004469552459)
              ·
                refine ⟨1352757861790506704328689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 901838574527004469552459 1352757861790506704328689)
                ·
                  refine ⟨1014568396342880028246517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1352757861790506704328689 1014568396342880028246517)
                  ·
                    refine ⟨95115787157145002648111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1014568396342880028246517 95115787157145002648111)
                    ·
                      rfl

theorem cell23_555712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 2, 5].length) (baseStart_555712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555712 prefixEnd_555712 := by exact prefixLift 555712
  have htrace : WordTrace (prefixWord ++ tailWord_555712) baseStart_555712 baseEnd_555712 := by
    simpa [prefixWord, tailWord_555712, baseEnd_555712] using wordTrace_append hprefix tailTrace_555712
  have hstable : (prefixWord ++ tailWord_555712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555712).length < 2 ^ (prefixWord ++ tailWord_555712).sum := by decide
  have hdescent : baseEnd_555712 < baseStart_555712 := by decide
  rcases family_descends (prefixWord ++ tailWord_555712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555733 : List Nat := [1, 3, 2, 5, 1, 2, 2, 2, 5]
def baseStart_555733 : Nat := 118140960795 + 555733 * 2 ^ 59
def prefixEnd_555733 : Nat := 4983230072969 + 3 ^ 40 * 555733 * 2
def baseEnd_555733 : Nat := 31706460507242158420193

theorem tailTrace_555733 : CollatzResearch.WordTrace tailWord_555733 prefixEnd_555733 31706460507242158420193 := by
  unfold tailWord_555733
  simp only [CollatzResearch.WordTrace]
  refine ⟨20269247695681727485207853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13512831797121151656805235 20269247695681727485207853)
  ·
    refine ⟨7600967885880647806952945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20269247695681727485207853 7600967885880647806952945)
    ·
      refine ⟨5700725914410485855214709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7600967885880647806952945 5700725914410485855214709)
      ·
        refine ⟨534443054475983048926379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5700725914410485855214709 534443054475983048926379)
        ·
          refine ⟨801664581713974573389569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534443054475983048926379 801664581713974573389569)
          ·
            refine ⟨601248436285480930042177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 801664581713974573389569 601248436285480930042177)
            ·
              refine ⟨450936327214110697531633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601248436285480930042177 450936327214110697531633)
              ·
                refine ⟨338202245410583023148725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450936327214110697531633 338202245410583023148725)
                ·
                  refine ⟨31706460507242158420193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 338202245410583023148725 31706460507242158420193)
                  ·
                    rfl

theorem cell23_555733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 5].length) (baseStart_555733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555733 prefixEnd_555733 := by exact prefixLift 555733
  have htrace : WordTrace (prefixWord ++ tailWord_555733) baseStart_555733 baseEnd_555733 := by
    simpa [prefixWord, tailWord_555733, baseEnd_555733] using wordTrace_append hprefix tailTrace_555733
  have hstable : (prefixWord ++ tailWord_555733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555733).length < 2 ^ (prefixWord ++ tailWord_555733).sum := by decide
  have hdescent : baseEnd_555733 < baseStart_555733 := by decide
  rcases family_descends (prefixWord ++ tailWord_555733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555749 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 2, 4, 2]
def baseStart_555749 : Nat := 118140960795 + 555749 * 2 ^ 59
def prefixEnd_555749 : Nat := 4983230072969 + 3 ^ 40 * 555749 * 2
def baseEnd_555749 : Nat := 285366360255651363181663

theorem tailTrace_555749 : CollatzResearch.WordTrace tailWord_555749 prefixEnd_555749 285366360255651363181663 := by
  unfold tailWord_555749
  simp only [CollatzResearch.WordTrace]
  refine ⟨20269831263623762217790301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13513220842415841478526867 20269831263623762217790301)
  ·
    refine ⟨7601186723858910831671363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20269831263623762217790301 7601186723858910831671363)
    ·
      refine ⟨11401780085788366247507045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7601186723858910831671363 11401780085788366247507045)
      ·
        refine ⟨2137833766085318671407571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11401780085788366247507045 2137833766085318671407571)
        ·
          refine ⟨3206750649127978007111357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137833766085318671407571 3206750649127978007111357)
          ·
            refine ⟨1202531493422991752666759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3206750649127978007111357 1202531493422991752666759)
            ·
              refine ⟨1803797240134487629000139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202531493422991752666759 1803797240134487629000139)
              ·
                refine ⟨2705695860201731443500209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803797240134487629000139 2705695860201731443500209)
                ·
                  refine ⟨2029271895151298582625157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2705695860201731443500209 2029271895151298582625157)
                  ·
                    refine ⟨380488480340868484242217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2029271895151298582625157 380488480340868484242217)
                    ·
                      refine ⟨285366360255651363181663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 380488480340868484242217 285366360255651363181663)
                      ·
                        rfl

theorem cell23_555749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_555749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555749 prefixEnd_555749 := by exact prefixLift 555749
  have htrace : WordTrace (prefixWord ++ tailWord_555749) baseStart_555749 baseEnd_555749 := by
    simpa [prefixWord, tailWord_555749, baseEnd_555749] using wordTrace_append hprefix tailTrace_555749
  have hstable : (prefixWord ++ tailWord_555749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555749).length < 2 ^ (prefixWord ++ tailWord_555749).sum := by decide
  have hdescent : baseEnd_555749 < baseStart_555749 := by decide
  rcases family_descends (prefixWord ++ tailWord_555749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555832 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 6, 4]
def baseStart_555832 : Nat := 118140960795 + 555832 * 2 ^ 59
def prefixEnd_555832 : Nat := 4983230072969 + 3 ^ 40 * 555832 * 2
def baseEnd_555832 : Nat := 95136326383324846147927

theorem tailTrace_555832 : CollatzResearch.WordTrace tailWord_555832 prefixEnd_555832 95136326383324846147927 := by
  unfold tailWord_555832
  simp only [CollatzResearch.WordTrace]
  refine ⟨10136429261161533696530875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13515239014882044928707833 10136429261161533696530875)
  ·
    refine ⟨15204643891742300544796313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10136429261161533696530875 15204643891742300544796313)
    ·
      refine ⟨11403482918806725408597235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15204643891742300544796313 11403482918806725408597235)
      ·
        refine ⟨17105224378210088112895853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11403482918806725408597235 17105224378210088112895853)
        ·
          refine ⟨6414459141828783042335945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17105224378210088112895853 6414459141828783042335945)
          ·
            refine ⟨4810844356371587281751959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6414459141828783042335945 4810844356371587281751959)
            ·
              refine ⟨7216266534557380922627939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4810844356371587281751959 7216266534557380922627939)
              ·
                refine ⟨10824399801836071383941909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7216266534557380922627939 10824399801836071383941909)
                ·
                  refine ⟨507393740711065846122277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10824399801836071383941909 507393740711065846122277)
                  ·
                    refine ⟨95136326383324846147927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 507393740711065846122277 95136326383324846147927)
                    ·
                      rfl

theorem cell23_555832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_555832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555832 prefixEnd_555832 := by exact prefixLift 555832
  have htrace : WordTrace (prefixWord ++ tailWord_555832) baseStart_555832 baseEnd_555832 := by
    simpa [prefixWord, tailWord_555832, baseEnd_555832] using wordTrace_append hprefix tailTrace_555832
  have hstable : (prefixWord ++ tailWord_555832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555832).length < 2 ^ (prefixWord ++ tailWord_555832).sum := by decide
  have hdescent : baseEnd_555832 < baseStart_555832 := by decide
  rcases family_descends (prefixWord ++ tailWord_555832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555839 : List Nat := [1, 1, 2, 2, 5, 1, 2, 3, 1, 1, 4]
def baseStart_555839 : Nat := 118140960795 + 555839 * 2 ^ 59
def prefixEnd_555839 : Nat := 4983230072969 + 3 ^ 40 * 555839 * 2
def baseEnd_555839 : Nat := 285412573514556011056249

theorem tailTrace_555839 : CollatzResearch.WordTrace tailWord_555839 prefixEnd_555839 285412573514556011056249 := by
  unfold tailWord_555839
  simp only [CollatzResearch.WordTrace]
  refine ⟨20273113833297707588566571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13515409222198471725711047 20273113833297707588566571)
  ·
    refine ⟨30409670749946561382849857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20273113833297707588566571 30409670749946561382849857)
    ·
      refine ⟨22807253062459921037137393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30409670749946561382849857 22807253062459921037137393)
      ·
        refine ⟨17105439796844940777853045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22807253062459921037137393 17105439796844940777853045)
        ·
          refine ⟨1603634980954213197923723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17105439796844940777853045 1603634980954213197923723)
          ·
            refine ⟨2405452471431319796885585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603634980954213197923723 2405452471431319796885585)
            ·
              refine ⟨1804089353573489847664189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2405452471431319796885585 1804089353573489847664189)
              ·
                refine ⟨676533507590058692874071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1804089353573489847664189 676533507590058692874071)
                ·
                  refine ⟨1014800261385088039311107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 676533507590058692874071 1014800261385088039311107)
                  ·
                    refine ⟨1522200392077632058966661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1014800261385088039311107 1522200392077632058966661)
                    ·
                      refine ⟨285412573514556011056249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1522200392077632058966661 285412573514556011056249)
                      ·
                        rfl

theorem cell23_555839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_555839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555839 prefixEnd_555839 := by exact prefixLift 555839
  have htrace : WordTrace (prefixWord ++ tailWord_555839) baseStart_555839 baseEnd_555839 := by
    simpa [prefixWord, tailWord_555839, baseEnd_555839] using wordTrace_append hprefix tailTrace_555839
  have hstable : (prefixWord ++ tailWord_555839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555839).length < 2 ^ (prefixWord ++ tailWord_555839).sum := by decide
  have hdescent : baseEnd_555839 < baseStart_555839 := by decide
  rcases family_descends (prefixWord ++ tailWord_555839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555852 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_555852 : Nat := 118140960795 + 555852 * 2 ^ 59
def prefixEnd_555852 : Nat := 4983230072969 + 3 ^ 40 * 555852 * 2
def baseEnd_555852 : Nat := 285419248763064460193689

theorem tailTrace_555852 : CollatzResearch.WordTrace tailWord_555852 prefixEnd_555852 285419248763064460193689 := by
  unfold tailWord_555852
  simp only [CollatzResearch.WordTrace]
  refine ⟨10136793991125305404394905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13515725321500407205859873 10136793991125305404394905)
  ·
    refine ⟨7602595493343979053296179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10136793991125305404394905 7602595493343979053296179)
    ·
      refine ⟨11403893240015968579944269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7602595493343979053296179 11403893240015968579944269)
      ·
        refine ⟨4276459965005988217479101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11403893240015968579944269 4276459965005988217479101)
        ·
          refine ⟨1603672486877245581554663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4276459965005988217479101 1603672486877245581554663)
          ·
            refine ⟨2405508730315868372331995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603672486877245581554663 2405508730315868372331995)
            ·
              refine ⟨3608263095473802558497993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405508730315868372331995 3608263095473802558497993)
              ·
                refine ⟨2706197321605351918873495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3608263095473802558497993 2706197321605351918873495)
                ·
                  refine ⟨4059295982408027878310243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706197321605351918873495 4059295982408027878310243)
                  ·
                    refine ⟨6088943973612041817465365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4059295982408027878310243 6088943973612041817465365)
                    ·
                      refine ⟨285419248763064460193689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6088943973612041817465365 285419248763064460193689)
                      ·
                        rfl

theorem cell23_555852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_555852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555852 prefixEnd_555852 := by exact prefixLift 555852
  have htrace : WordTrace (prefixWord ++ tailWord_555852) baseStart_555852 baseEnd_555852 := by
    simpa [prefixWord, tailWord_555852, baseEnd_555852] using wordTrace_append hprefix tailTrace_555852
  have hstable : (prefixWord ++ tailWord_555852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555852).length < 2 ^ (prefixWord ++ tailWord_555852).sum := by decide
  have hdescent : baseEnd_555852 < baseStart_555852 := by decide
  rcases family_descends (prefixWord ++ tailWord_555852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555856 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 3, 2, 2]
def baseStart_555856 : Nat := 118140960795 + 555856 * 2 ^ 59
def prefixEnd_555856 : Nat := 4983230072969 + 3 ^ 40 * 555856 * 2
def baseEnd_555856 : Nat := 285421302685682444543671

theorem tailTrace_555856 : CollatzResearch.WordTrace tailWord_555856 prefixEnd_555856 285421302685682444543671 := by
  unfold tailWord_555856
  simp only [CollatzResearch.WordTrace]
  refine ⟨10136866937118059745967711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13515822582824079661290281 10136866937118059745967711)
  ·
    refine ⟨15205300405677089618951567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10136866937118059745967711 15205300405677089618951567)
    ·
      refine ⟨22807950608515634428427351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15205300405677089618951567 22807950608515634428427351)
      ·
        refine ⟨34211925912773451642641027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22807950608515634428427351 34211925912773451642641027)
        ·
          refine ⟨51317888869160177463961541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34211925912773451642641027 51317888869160177463961541)
          ·
            refine ⟨9622104162967533274492789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51317888869160177463961541 9622104162967533274492789)
            ·
              refine ⟨902072265278206244483699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9622104162967533274492789 902072265278206244483699)
              ·
                refine ⟨1353108397917309366725549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 902072265278206244483699 1353108397917309366725549)
                ·
                  refine ⟨507415649218991012522081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1353108397917309366725549 507415649218991012522081)
                  ·
                    refine ⟨380561736914243259391561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 507415649218991012522081 380561736914243259391561)
                    ·
                      refine ⟨285421302685682444543671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 380561736914243259391561 285421302685682444543671)
                      ·
                        rfl

theorem cell23_555856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 3, 2, 2].length) (baseStart_555856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555856 prefixEnd_555856 := by exact prefixLift 555856
  have htrace : WordTrace (prefixWord ++ tailWord_555856) baseStart_555856 baseEnd_555856 := by
    simpa [prefixWord, tailWord_555856, baseEnd_555856] using wordTrace_append hprefix tailTrace_555856
  have hstable : (prefixWord ++ tailWord_555856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555856).length < 2 ^ (prefixWord ++ tailWord_555856).sum := by decide
  have hdescent : baseEnd_555856 < baseStart_555856 := by decide
  rcases family_descends (prefixWord ++ tailWord_555856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555866 : List Nat := [3, 1, 1, 2, 1, 4, 4, 1, 2, 4]
def baseStart_555866 : Nat := 118140960795 + 555866 * 2 ^ 59
def prefixEnd_555866 : Nat := 4983230072969 + 3 ^ 40 * 555866 * 2
def baseEnd_555866 : Nat := 95142145830742468472875

theorem tailTrace_555866 : CollatzResearch.WordTrace tailWord_555866 prefixEnd_555866 95142145830742468472875 := by
  unfold tailWord_555866
  simp only [CollatzResearch.WordTrace]
  refine ⟨5068524651049972799949863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13516065736133260799866301 5068524651049972799949863)
  ·
    refine ⟨7602786976574959199924795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5068524651049972799949863 7602786976574959199924795)
    ·
      refine ⟨11404180464862438799887193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7602786976574959199924795 11404180464862438799887193)
      ·
        refine ⟨8553135348646829099915395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11404180464862438799887193 8553135348646829099915395)
        ·
          refine ⟨12829703022970243649873093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8553135348646829099915395 12829703022970243649873093)
          ·
            refine ⟨2405569316806920684351205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12829703022970243649873093 2405569316806920684351205)
            ·
              refine ⟨451044246901297628315851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2405569316806920684351205 451044246901297628315851)
              ·
                refine ⟨676566370351946442473777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451044246901297628315851 676566370351946442473777)
                ·
                  refine ⟨507424777763959831855333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 676566370351946442473777 507424777763959831855333)
                  ·
                    refine ⟨95142145830742468472875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 507424777763959831855333 95142145830742468472875)
                    ·
                      rfl

theorem cell23_555866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_555866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555866 prefixEnd_555866 := by exact prefixLift 555866
  have htrace : WordTrace (prefixWord ++ tailWord_555866) baseStart_555866 baseEnd_555866 := by
    simpa [prefixWord, tailWord_555866, baseEnd_555866] using wordTrace_append hprefix tailTrace_555866
  have hstable : (prefixWord ++ tailWord_555866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555866).length < 2 ^ (prefixWord ++ tailWord_555866).sum := by decide
  have hdescent : baseEnd_555866 < baseStart_555866 := by decide
  rcases family_descends (prefixWord ++ tailWord_555866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555876 : List Nat := [2, 3, 1, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_555876 : Nat := 118140960795 + 555876 * 2 ^ 59
def prefixEnd_555876 : Nat := 4983230072969 + 3 ^ 40 * 555876 * 2
def baseEnd_555876 : Nat := 285431572298772366293579

theorem tailTrace_555876 : CollatzResearch.WordTrace tailWord_555876 prefixEnd_555876 285431572298772366293579 := by
  unfold tailWord_555876
  simp only [CollatzResearch.WordTrace]
  refine ⟨10137231667081831453831741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13516308889442441938442321 10137231667081831453831741)
  ·
    refine ⟨3801461875155686795186903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10137231667081831453831741 3801461875155686795186903)
    ·
      refine ⟨5702192812733530192780355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3801461875155686795186903 5702192812733530192780355)
      ·
        refine ⟨8553289219100295289170533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5702192812733530192780355 8553289219100295289170533)
        ·
          refine ⟨1603741728581305366719475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8553289219100295289170533 1603741728581305366719475)
          ·
            refine ⟨2405612592871958050079213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603741728581305366719475 2405612592871958050079213)
            ·
              refine ⟨902104722326984268779705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2405612592871958050079213 902104722326984268779705)
              ·
                refine ⟨676578541745238201584779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 902104722326984268779705 676578541745238201584779)
                ·
                  refine ⟨1014867812617857302377169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 676578541745238201584779 1014867812617857302377169)
                  ·
                    refine ⟨761150859463392976782877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1014867812617857302377169 761150859463392976782877)
                    ·
                      refine ⟨285431572298772366293579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761150859463392976782877 285431572298772366293579)
                      ·
                        rfl

theorem cell23_555876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_555876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555876 prefixEnd_555876 := by exact prefixLift 555876
  have htrace : WordTrace (prefixWord ++ tailWord_555876) baseStart_555876 baseEnd_555876 := by
    simpa [prefixWord, tailWord_555876, baseEnd_555876] using wordTrace_append hprefix tailTrace_555876
  have hstable : (prefixWord ++ tailWord_555876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555876).length < 2 ^ (prefixWord ++ tailWord_555876).sum := by decide
  have hdescent : baseEnd_555876 < baseStart_555876 := by decide
  rcases family_descends (prefixWord ++ tailWord_555876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555886 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_555886 : Nat := 118140960795 + 555886 * 2 ^ 59
def prefixEnd_555886 : Nat := 4983230072969 + 3 ^ 40 * 555886 * 2
def baseEnd_555886 : Nat := 285436707105317327168533

theorem tailTrace_555886 : CollatzResearch.WordTrace tailWord_555886 prefixEnd_555886 285436707105317327168533 := by
  unfold tailWord_555886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2534353508015929326940939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13516552042751623077018341 2534353508015929326940939)
  ·
    refine ⟨3801530262023893990411409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2534353508015929326940939 3801530262023893990411409)
    ·
      refine ⟨2851147696517920492808557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3801530262023893990411409 2851147696517920492808557)
      ·
        refine ⟨1069180386194220184803209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2851147696517920492808557 1069180386194220184803209)
        ·
          refine ⟨801885289645665138602407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1069180386194220184803209 801885289645665138602407)
          ·
            refine ⟨1202827934468497707903611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801885289645665138602407 1202827934468497707903611)
            ·
              refine ⟨1804241901702746561855417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202827934468497707903611 1804241901702746561855417)
              ·
                refine ⟨1353181426277059921391563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1804241901702746561855417 1353181426277059921391563)
                ·
                  refine ⟨2029772139415589882087345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353181426277059921391563 2029772139415589882087345)
                  ·
                    refine ⟨1522329104561692411565509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2029772139415589882087345 1522329104561692411565509)
                    ·
                      refine ⟨285436707105317327168533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1522329104561692411565509 285436707105317327168533)
                      ·
                        rfl

theorem cell23_555886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_555886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555886 prefixEnd_555886 := by exact prefixLift 555886
  have htrace : WordTrace (prefixWord ++ tailWord_555886) baseStart_555886 baseEnd_555886 := by
    simpa [prefixWord, tailWord_555886, baseEnd_555886] using wordTrace_append hprefix tailTrace_555886
  have hstable : (prefixWord ++ tailWord_555886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555886).length < 2 ^ (prefixWord ++ tailWord_555886).sum := by decide
  have hdescent : baseEnd_555886 < baseStart_555886 := by decide
  rcases family_descends (prefixWord ++ tailWord_555886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555889 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 1, 3, 3]
def baseStart_555889 : Nat := 118140960795 + 555889 * 2 ^ 59
def prefixEnd_555889 : Nat := 4983230072969 + 3 ^ 40 * 555889 * 2
def baseEnd_555889 : Nat := 285438247547280815431019

theorem tailTrace_555889 : CollatzResearch.WordTrace tailWord_555889 prefixEnd_555889 285438247547280815431019 := by
  unfold tailWord_555889
  simp only [CollatzResearch.WordTrace]
  refine ⟨20274937483116566127886721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13516624988744377418591147 20274937483116566127886721)
  ·
    refine ⟨15206203112337424595915041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20274937483116566127886721 15206203112337424595915041)
    ·
      refine ⟨11404652334253068446936281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15206203112337424595915041 11404652334253068446936281)
      ·
        refine ⟨8553489250689801335202211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11404652334253068446936281 8553489250689801335202211)
        ·
          refine ⟨12830233876034702002803317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8553489250689801335202211 12830233876034702002803317)
          ·
            refine ⟨1202834425878253312762811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12830233876034702002803317 1202834425878253312762811)
            ·
              refine ⟨1804251638817379969144217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202834425878253312762811 1804251638817379969144217)
              ·
                refine ⟨1353188729113034976858163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1804251638817379969144217 1353188729113034976858163)
                ·
                  refine ⟨2029783093669552465287245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353188729113034976858163 2029783093669552465287245)
                  ·
                    refine ⟨761168660126082174482717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2029783093669552465287245 761168660126082174482717)
                    ·
                      refine ⟨285438247547280815431019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761168660126082174482717 285438247547280815431019)
                      ·
                        rfl

theorem cell23_555889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_555889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555889 prefixEnd_555889 := by exact prefixLift 555889
  have htrace : WordTrace (prefixWord ++ tailWord_555889) baseStart_555889 baseEnd_555889 := by
    simpa [prefixWord, tailWord_555889, baseEnd_555889] using wordTrace_append hprefix tailTrace_555889
  have hstable : (prefixWord ++ tailWord_555889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555889).length < 2 ^ (prefixWord ++ tailWord_555889).sum := by decide
  have hdescent : baseEnd_555889 < baseStart_555889 := by decide
  rcases family_descends (prefixWord ++ tailWord_555889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555893 : List Nat := [1, 3, 4, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_555893 : Nat := 118140960795 + 555893 * 2 ^ 59
def prefixEnd_555893 : Nat := 4983230072969 + 3 ^ 40 * 555893 * 2
def baseEnd_555893 : Nat := 285440301469898799781001

theorem tailTrace_555893 : CollatzResearch.WordTrace tailWord_555893 prefixEnd_555893 285440301469898799781001 := by
  unfold tailWord_555893
  simp only [CollatzResearch.WordTrace]
  refine ⟨20275083375102074811032333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13516722250068049874021555 20275083375102074811032333)
  ·
    refine ⟨7603156265663278054137125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20275083375102074811032333 7603156265663278054137125)
    ·
      refine ⟨1425591799811864635150711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7603156265663278054137125 1425591799811864635150711)
      ·
        refine ⟨2138387699717796952726067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1425591799811864635150711 2138387699717796952726067)
        ·
          refine ⟨3207581549576695429089101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2138387699717796952726067 3207581549576695429089101)
          ·
            refine ⟨1202843081091260785908413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3207581549576695429089101 1202843081091260785908413)
            ·
              refine ⟨451066155409222794715655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1202843081091260785908413 451066155409222794715655)
              ·
                refine ⟨676599233113834192073483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451066155409222794715655 676599233113834192073483)
                ·
                  refine ⟨1014898849670751288110225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 676599233113834192073483 1014898849670751288110225)
                  ·
                    refine ⟨761174137253063466082669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1014898849670751288110225 761174137253063466082669)
                    ·
                      refine ⟨285440301469898799781001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761174137253063466082669 285440301469898799781001)
                      ·
                        rfl

theorem cell23_555893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_555893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555893 prefixEnd_555893 := by exact prefixLift 555893
  have htrace : WordTrace (prefixWord ++ tailWord_555893) baseStart_555893 baseEnd_555893 := by
    simpa [prefixWord, tailWord_555893, baseEnd_555893] using wordTrace_append hprefix tailTrace_555893
  have hstable : (prefixWord ++ tailWord_555893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555893).length < 2 ^ (prefixWord ++ tailWord_555893).sum := by decide
  have hdescent : baseEnd_555893 < baseStart_555893 := by decide
  rcases family_descends (prefixWord ++ tailWord_555893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555956 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_555956 : Nat := 118140960795 + 555956 * 2 ^ 59
def prefixEnd_555956 : Nat := 4983230072969 + 3 ^ 40 * 555956 * 2
def baseEnd_555956 : Nat := 95157550250377351097737

theorem tailTrace_555956 : CollatzResearch.WordTrace tailWord_555956 prefixEnd_555956 95157550250377351097737 := by
  unfold tailWord_555956
  simp only [CollatzResearch.WordTrace]
  refine ⟨10138690586936918285287861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13518254115915891047050481 10138690586936918285287861)
  ·
    refine ⟨950502242525336089245737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10138690586936918285287861 950502242525336089245737)
    ·
      refine ⟨712876681894002066934303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 950502242525336089245737 712876681894002066934303)
      ·
        refine ⟨1069315022841003100401455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712876681894002066934303 1069315022841003100401455)
        ·
          refine ⟨1603972534261504650602183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1069315022841003100401455 1603972534261504650602183)
          ·
            refine ⟨2405958801392256975903275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603972534261504650602183 2405958801392256975903275)
            ·
              refine ⟨3608938202088385463854913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405958801392256975903275 3608938202088385463854913)
              ·
                refine ⟨2706703651566289097891185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3608938202088385463854913 2706703651566289097891185)
                ·
                  refine ⟨2030027738674716823418389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2706703651566289097891185 2030027738674716823418389)
                  ·
                    refine ⟨95157550250377351097737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2030027738674716823418389 95157550250377351097737)
                    ·
                      rfl

theorem cell23_555956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_555956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555956 prefixEnd_555956 := by exact prefixLift 555956
  have htrace : WordTrace (prefixWord ++ tailWord_555956) baseStart_555956 baseEnd_555956 := by
    simpa [prefixWord, tailWord_555956, baseEnd_555956] using wordTrace_append hprefix tailTrace_555956
  have hstable : (prefixWord ++ tailWord_555956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555956).length < 2 ^ (prefixWord ++ tailWord_555956).sum := by decide
  have hdescent : baseEnd_555956 < baseStart_555956 := by decide
  rcases family_descends (prefixWord ++ tailWord_555956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555974 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_555974 : Nat := 118140960795 + 555974 * 2 ^ 59
def prefixEnd_555974 : Nat := 4983230072969 + 3 ^ 40 * 555974 * 2
def baseEnd_555974 : Nat := 285481893402912982868129

theorem tailTrace_555974 : CollatzResearch.WordTrace tailWord_555974 prefixEnd_555974 285481893402912982868129 := by
  unfold tailWord_555974
  simp only [CollatzResearch.WordTrace]
  refine ⟨633688677744019551397843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13518691791872417096487317 633688677744019551397843)
  ·
    refine ⟨950533016616029327096765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 633688677744019551397843 950533016616029327096765)
    ·
      refine ⟨356449881231010997661287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 950533016616029327096765 356449881231010997661287)
      ·
        refine ⟨534674821846516496491931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356449881231010997661287 534674821846516496491931)
        ·
          refine ⟨802012232769774744737897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534674821846516496491931 802012232769774744737897)
          ·
            refine ⟨601509174577331058553423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802012232769774744737897 601509174577331058553423)
            ·
              refine ⟨902263761865996587830135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601509174577331058553423 902263761865996587830135)
              ·
                refine ⟨1353395642798994881745203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 902263761865996587830135 1353395642798994881745203)
                ·
                  refine ⟨2030093464198492322617805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353395642798994881745203 2030093464198492322617805)
                  ·
                    refine ⟨761285049074434620981677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2030093464198492322617805 761285049074434620981677)
                    ·
                      refine ⟨285481893402912982868129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761285049074434620981677 285481893402912982868129)
                      ·
                        rfl

theorem cell23_555974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_555974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555974 prefixEnd_555974 := by exact prefixLift 555974
  have htrace : WordTrace (prefixWord ++ tailWord_555974) baseStart_555974 baseEnd_555974 := by
    simpa [prefixWord, tailWord_555974, baseEnd_555974] using wordTrace_append hprefix tailTrace_555974
  have hstable : (prefixWord ++ tailWord_555974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555974).length < 2 ^ (prefixWord ++ tailWord_555974).sum := by decide
  have hdescent : baseEnd_555974 < baseStart_555974 := by decide
  rcases family_descends (prefixWord ++ tailWord_555974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555979 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 3]
def baseStart_555979 : Nat := 118140960795 + 555979 * 2 ^ 59
def prefixEnd_555979 : Nat := 4983230072969 + 3 ^ 40 * 555979 * 2
def baseEnd_555979 : Nat := 285484460806185463305605

theorem tailTrace_555979 : CollatzResearch.WordTrace tailWord_555979 prefixEnd_555979 285484460806185463305605 := by
  unfold tailWord_555979
  simp only [CollatzResearch.WordTrace]
  refine ⟨20278220052790511498662991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13518813368527007665775327 20278220052790511498662991)
  ·
    refine ⟨30417330079185767247994487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20278220052790511498662991 30417330079185767247994487)
    ·
      refine ⟨45625995118778650871991731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30417330079185767247994487 45625995118778650871991731)
      ·
        refine ⟨68438992678167976307987597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45625995118778650871991731 68438992678167976307987597)
        ·
          refine ⟨25664622254312991115495349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68438992678167976307987597 25664622254312991115495349)
          ·
            refine ⟨2406058336341842917077689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25664622254312991115495349 2406058336341842917077689)
            ·
              refine ⟨1804543752256382187808267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2406058336341842917077689 1804543752256382187808267)
              ·
                refine ⟨2706815628384573281712401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1804543752256382187808267 2706815628384573281712401)
                ·
                  refine ⟨2030111721288429961284301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2706815628384573281712401 2030111721288429961284301)
                  ·
                    refine ⟨761291895483161235481613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2030111721288429961284301 761291895483161235481613)
                    ·
                      refine ⟨285484460806185463305605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761291895483161235481613 285484460806185463305605)
                      ·
                        rfl

theorem cell23_555979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 3].length) (baseStart_555979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555979 prefixEnd_555979 := by exact prefixLift 555979
  have htrace : WordTrace (prefixWord ++ tailWord_555979) baseStart_555979 baseEnd_555979 := by
    simpa [prefixWord, tailWord_555979, baseEnd_555979] using wordTrace_append hprefix tailTrace_555979
  have hstable : (prefixWord ++ tailWord_555979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555979).length < 2 ^ (prefixWord ++ tailWord_555979).sum := by decide
  have hdescent : baseEnd_555979 < baseStart_555979 := by decide
  rcases family_descends (prefixWord ++ tailWord_555979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555980 : List Nat := [2, 2, 1, 4, 1, 1, 5, 1, 2, 2, 2]
def baseStart_555980 : Nat := 118140960795 + 555980 * 2 ^ 59
def prefixEnd_555980 : Nat := 4983230072969 + 3 ^ 40 * 555980 * 2
def baseEnd_555980 : Nat := 285484974286839959393101

theorem tailTrace_555980 : CollatzResearch.WordTrace tailWord_555980 prefixEnd_555980 285484974286839959393101 := by
  unfold tailWord_555980
  simp only [CollatzResearch.WordTrace]
  refine ⟨10139128262893444334724697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13518837683857925779632929 10139128262893444334724697)
  ·
    refine ⟨7604346197170083251043523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10139128262893444334724697 7604346197170083251043523)
    ·
      refine ⟨11406519295755124876565285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7604346197170083251043523 11406519295755124876565285)
      ·
        refine ⟨2138722367954085914355991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11406519295755124876565285 2138722367954085914355991)
        ·
          refine ⟨3208083551931128871533987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2138722367954085914355991 3208083551931128871533987)
          ·
            refine ⟨4812125327896693307300981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3208083551931128871533987 4812125327896693307300981)
            ·
              refine ⟨451136749490314997559467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4812125327896693307300981 451136749490314997559467)
              ·
                refine ⟨676705124235472496339201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451136749490314997559467 676705124235472496339201)
                ·
                  refine ⟨507528843176604372254401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 676705124235472496339201 507528843176604372254401)
                  ·
                    refine ⟨380646632382453279190801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 507528843176604372254401 380646632382453279190801)
                    ·
                      refine ⟨285484974286839959393101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 380646632382453279190801 285484974286839959393101)
                      ·
                        rfl

theorem cell23_555980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_555980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_555980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_555980 prefixEnd_555980 := by exact prefixLift 555980
  have htrace : WordTrace (prefixWord ++ tailWord_555980) baseStart_555980 baseEnd_555980 := by
    simpa [prefixWord, tailWord_555980, baseEnd_555980] using wordTrace_append hprefix tailTrace_555980
  have hstable : (prefixWord ++ tailWord_555980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555980).length < 2 ^ (prefixWord ++ tailWord_555980).sum := by decide
  have hdescent : baseEnd_555980 < baseStart_555980 := by decide
  rcases family_descends (prefixWord ++ tailWord_555980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556032 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 6]
def baseStart_556032 : Nat := 118140960795 + 556032 * 2 ^ 59
def prefixEnd_556032 : Nat := 4983230072969 + 3 ^ 40 * 556032 * 2
def baseEnd_556032 : Nat := 285511675280873755942861

theorem tailTrace_556032 : CollatzResearch.WordTrace tailWord_556032 prefixEnd_556032 285511675280873755942861 := by
  unfold tailWord_556032
  simp only [CollatzResearch.WordTrace]
  refine ⟨10140076560799250775171175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13520102081065667700228233 10140076560799250775171175)
  ·
    refine ⟨15210114841198876162756763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10140076560799250775171175 15210114841198876162756763)
    ·
      refine ⟨22815172261798314244135145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15210114841198876162756763 22815172261798314244135145)
      ·
        refine ⟨17111379196348735683101359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22815172261798314244135145 17111379196348735683101359)
        ·
          refine ⟨25667068794523103524652039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17111379196348735683101359 25667068794523103524652039)
          ·
            refine ⟨38500603191784655286978059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25667068794523103524652039 38500603191784655286978059)
            ·
              refine ⟨57750904787676982930467089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38500603191784655286978059 57750904787676982930467089)
              ·
                refine ⟨43313178590757737197850317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57750904787676982930467089 43313178590757737197850317)
                ·
                  refine ⟨16242441971534151449193869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43313178590757737197850317 16242441971534151449193869)
                  ·
                    refine ⟨6090915739325306793447701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16242441971534151449193869 6090915739325306793447701)
                    ·
                      refine ⟨285511675280873755942861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6090915739325306793447701 285511675280873755942861)
                      ·
                        rfl

theorem cell23_556032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_556032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556032 prefixEnd_556032 := by exact prefixLift 556032
  have htrace : WordTrace (prefixWord ++ tailWord_556032) baseStart_556032 baseEnd_556032 := by
    simpa [prefixWord, tailWord_556032, baseEnd_556032] using wordTrace_append hprefix tailTrace_556032
  have hstable : (prefixWord ++ tailWord_556032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556032).length < 2 ^ (prefixWord ++ tailWord_556032).sum := by decide
  have hdescent : baseEnd_556032 < baseStart_556032 := by decide
  rcases family_descends (prefixWord ++ tailWord_556032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556056 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 2, 2, 3]
def baseStart_556056 : Nat := 118140960795 + 556056 * 2 ^ 59
def prefixEnd_556056 : Nat := 4983230072969 + 3 ^ 40 * 556056 * 2
def baseEnd_556056 : Nat := 285523998816581662042751

theorem tailTrace_556056 : CollatzResearch.WordTrace tailWord_556056 prefixEnd_556056 285523998816581662042751 := by
  unfold tailWord_556056
  simp only [CollatzResearch.WordTrace]
  refine ⟨10140514236755776824608011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13520685649007702432810681 10140514236755776824608011)
  ·
    refine ⟨15210771355133665236912017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10140514236755776824608011 15210771355133665236912017)
    ·
      refine ⟨11408078516350248927684013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15210771355133665236912017 11408078516350248927684013)
      ·
        refine ⟨4278029443631343347881505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11408078516350248927684013 4278029443631343347881505)
        ·
          refine ⟨3208522082723507510911129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4278029443631343347881505 3208522082723507510911129)
          ·
            refine ⟨2406391562042630633183347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3208522082723507510911129 2406391562042630633183347)
            ·
              refine ⟨3609587343063945949775021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2406391562042630633183347 3609587343063945949775021)
              ·
                refine ⟨1353595253648979731165633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3609587343063945949775021 1353595253648979731165633)
                ·
                  refine ⟨1015196440236734798374225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1353595253648979731165633 1015196440236734798374225)
                  ·
                    refine ⟨761397330177551098780669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1015196440236734798374225 761397330177551098780669)
                    ·
                      refine ⟨285523998816581662042751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761397330177551098780669 285523998816581662042751)
                      ·
                        rfl

theorem cell23_556056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_556056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556056 prefixEnd_556056 := by exact prefixLift 556056
  have htrace : WordTrace (prefixWord ++ tailWord_556056) baseStart_556056 baseEnd_556056 := by
    simpa [prefixWord, tailWord_556056, baseEnd_556056] using wordTrace_append hprefix tailTrace_556056
  have hstable : (prefixWord ++ tailWord_556056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556056).length < 2 ^ (prefixWord ++ tailWord_556056).sum := by decide
  have hdescent : baseEnd_556056 < baseStart_556056 := by decide
  rcases family_descends (prefixWord ++ tailWord_556056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556096 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 1, 5, 2]
def baseStart_556096 : Nat := 118140960795 + 556096 * 2 ^ 59
def prefixEnd_556096 : Nat := 4983230072969 + 3 ^ 40 * 556096 * 2
def baseEnd_556096 : Nat := 285544538042761505542567

theorem tailTrace_556096 : CollatzResearch.WordTrace tailWord_556096 prefixEnd_556096 285544538042761505542567 := by
  unfold tailWord_556096
  simp only [CollatzResearch.WordTrace]
  refine ⟨10141243696683320240336071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13521658262244426987114761 10141243696683320240336071)
  ·
    refine ⟨15211865545024980360504107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10141243696683320240336071 15211865545024980360504107)
    ·
      refine ⟨22817798317537470540756161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15211865545024980360504107 22817798317537470540756161)
      ·
        refine ⟨17113348738153102905567121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22817798317537470540756161 17113348738153102905567121)
        ·
          refine ⟨12835011553614827179175341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17113348738153102905567121 12835011553614827179175341)
          ·
            refine ⟨4813129332605560192190753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12835011553614827179175341 4813129332605560192190753)
            ·
              refine ⟨3609846999454170144143065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4813129332605560192190753 3609846999454170144143065)
              ·
                refine ⟨2707385249590627608107299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3609846999454170144143065 2707385249590627608107299)
                ·
                  refine ⟨4061077874385941412160949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2707385249590627608107299 4061077874385941412160949)
                  ·
                    refine ⟨380726050723682007390089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4061077874385941412160949 380726050723682007390089)
                    ·
                      refine ⟨285544538042761505542567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 380726050723682007390089 285544538042761505542567)
                      ·
                        rfl

theorem cell23_556096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 5, 2].length) (baseStart_556096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556096 prefixEnd_556096 := by exact prefixLift 556096
  have htrace : WordTrace (prefixWord ++ tailWord_556096) baseStart_556096 baseEnd_556096 := by
    simpa [prefixWord, tailWord_556096, baseEnd_556096] using wordTrace_append hprefix tailTrace_556096
  have hstable : (prefixWord ++ tailWord_556096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556096).length < 2 ^ (prefixWord ++ tailWord_556096).sum := by decide
  have hdescent : baseEnd_556096 < baseStart_556096 := by decide
  rcases family_descends (prefixWord ++ tailWord_556096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556103 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_556103 : Nat := 118140960795 + 556103 * 2 ^ 59
def prefixEnd_556103 : Nat := 4983230072969 + 3 ^ 40 * 556103 * 2
def baseEnd_556103 : Nat := 285548132407342978155035

theorem tailTrace_556103 : CollatzResearch.WordTrace tailWord_556103 prefixEnd_556103 285548132407342978155035 := by
  unfold tailWord_556103
  simp only [CollatzResearch.WordTrace]
  refine ⟨20282742704341280676176963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13521828469560853784117975 20282742704341280676176963)
  ·
    refine ⟨30424114056511921014265445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20282742704341280676176963 30424114056511921014265445)
    ·
      refine ⟨5704521385595985190174771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30424114056511921014265445 5704521385595985190174771)
      ·
        refine ⟨8556782078393977785262157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5704521385595985190174771 8556782078393977785262157)
        ·
          refine ⟨3208793279397741669473309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8556782078393977785262157 3208793279397741669473309)
          ·
            refine ⟨1203297479774153126052491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3208793279397741669473309 1203297479774153126052491)
            ·
              refine ⟨1804946219661229689078737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203297479774153126052491 1804946219661229689078737)
              ·
                refine ⟨1353709664745922266809053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1804946219661229689078737 1353709664745922266809053)
                ·
                  refine ⟨507641124279720850053395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1353709664745922266809053 507641124279720850053395)
                  ·
                    refine ⟨761461686419581275080093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 507641124279720850053395 761461686419581275080093)
                    ·
                      refine ⟨285548132407342978155035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761461686419581275080093 285548132407342978155035)
                      ·
                        rfl

theorem cell23_556103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_556103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556103 prefixEnd_556103 := by exact prefixLift 556103
  have htrace : WordTrace (prefixWord ++ tailWord_556103) baseStart_556103 baseEnd_556103 := by
    simpa [prefixWord, tailWord_556103, baseEnd_556103] using wordTrace_append hprefix tailTrace_556103
  have hstable : (prefixWord ++ tailWord_556103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556103).length < 2 ^ (prefixWord ++ tailWord_556103).sum := by decide
  have hdescent : baseEnd_556103 < baseStart_556103 := by decide
  rcases family_descends (prefixWord ++ tailWord_556103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556113 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 2, 3, 2]
def baseStart_556113 : Nat := 118140960795 + 556113 * 2 ^ 59
def prefixEnd_556113 : Nat := 4983230072969 + 3 ^ 40 * 556113 * 2
def baseEnd_556113 : Nat := 285553267213887939029989

theorem tailTrace_556113 : CollatzResearch.WordTrace tailWord_556113 prefixEnd_556113 285553267213887939029989 := by
  unfold tailWord_556113
  simp only [CollatzResearch.WordTrace]
  refine ⟨20283107434305052384040993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13522071622870034922693995 20283107434305052384040993)
  ·
    refine ⟨15212330575728789288030745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20283107434305052384040993 15212330575728789288030745)
    ·
      refine ⟨11409247931796591966023059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15212330575728789288030745 11409247931796591966023059)
      ·
        refine ⟨17113871897694887949034589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11409247931796591966023059 17113871897694887949034589)
        ·
          refine ⟨6417701961635582980887971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17113871897694887949034589 6417701961635582980887971)
          ·
            refine ⟨9626552942453374471331957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6417701961635582980887971 9626552942453374471331957)
            ·
              refine ⟨902489338355003856687371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9626552942453374471331957 902489338355003856687371)
              ·
                refine ⟨1353734007532505785031057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 902489338355003856687371 1353734007532505785031057)
                ·
                  refine ⟨1015300505649379338773293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1353734007532505785031057 1015300505649379338773293)
                  ·
                    refine ⟨380737689618517252039985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1015300505649379338773293 380737689618517252039985)
                    ·
                      refine ⟨285553267213887939029989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 380737689618517252039985 285553267213887939029989)
                      ·
                        rfl

theorem cell23_556113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 3, 2].length) (baseStart_556113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556113 prefixEnd_556113 := by exact prefixLift 556113
  have htrace : WordTrace (prefixWord ++ tailWord_556113) baseStart_556113 baseEnd_556113 := by
    simpa [prefixWord, tailWord_556113, baseEnd_556113] using wordTrace_append hprefix tailTrace_556113
  have hstable : (prefixWord ++ tailWord_556113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556113).length < 2 ^ (prefixWord ++ tailWord_556113).sum := by decide
  have hdescent : baseEnd_556113 < baseStart_556113 := by decide
  rcases family_descends (prefixWord ++ tailWord_556113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556120 : List Nat := [2, 1, 2, 2, 1, 3, 4, 3, 1, 1, 3]
def baseStart_556120 : Nat := 118140960795 + 556120 * 2 ^ 59
def prefixEnd_556120 : Nat := 4983230072969 + 3 ^ 40 * 556120 * 2
def baseEnd_556120 : Nat := 285556861578469411642457

theorem tailTrace_556120 : CollatzResearch.WordTrace tailWord_556120 prefixEnd_556120 285556861578469411642457 := by
  unfold tailWord_556120
  simp only [CollatzResearch.WordTrace]
  refine ⟨10141681372639846289772907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13522241830186461719697209 10141681372639846289772907)
  ·
    refine ⟨15212522058959769434659361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10141681372639846289772907 15212522058959769434659361)
    ·
      refine ⟨11409391544219827075994521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15212522058959769434659361 11409391544219827075994521)
      ·
        refine ⟨8557043658164870306995891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11409391544219827075994521 8557043658164870306995891)
        ·
          refine ⟨12835565487247305460493837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8557043658164870306995891 12835565487247305460493837)
          ·
            refine ⟨4813337057717739547685189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12835565487247305460493837 4813337057717739547685189)
            ·
              refine ⟨902500698322076165190973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4813337057717739547685189 902500698322076165190973)
              ·
                refine ⟨338437761870778561946615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 902500698322076165190973 338437761870778561946615)
                ·
                  refine ⟨507656642806167842919923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338437761870778561946615 507656642806167842919923)
                  ·
                    refine ⟨761484964209251764379885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 507656642806167842919923 761484964209251764379885)
                    ·
                      refine ⟨285556861578469411642457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761484964209251764379885 285556861578469411642457)
                      ·
                        rfl

theorem cell23_556120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_556120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556120 prefixEnd_556120 := by exact prefixLift 556120
  have htrace : WordTrace (prefixWord ++ tailWord_556120) baseStart_556120 baseEnd_556120 := by
    simpa [prefixWord, tailWord_556120, baseEnd_556120] using wordTrace_append hprefix tailTrace_556120
  have hstable : (prefixWord ++ tailWord_556120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556120).length < 2 ^ (prefixWord ++ tailWord_556120).sum := by decide
  have hdescent : baseEnd_556120 < baseStart_556120 := by decide
  rcases family_descends (prefixWord ++ tailWord_556120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556146 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_556146 : Nat := 118140960795 + 556146 * 2 ^ 59
def prefixEnd_556146 : Nat := 4983230072969 + 3 ^ 40 * 556146 * 2
def baseEnd_556146 : Nat := 285570212075486309917337

theorem tailTrace_556146 : CollatzResearch.WordTrace tailWord_556146 prefixEnd_556146 285570212075486309917337 := by
  unfold tailWord_556146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5071077760796374754998073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13522874028790332679994861 5071077760796374754998073)
  ·
    refine ⟨3803308320597281066248555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5071077760796374754998073 3803308320597281066248555)
    ·
      refine ⟨5704962480895921599372833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3803308320597281066248555 5704962480895921599372833)
      ·
        refine ⟨4278721860671941199529625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5704962480895921599372833 4278721860671941199529625)
        ·
          refine ⟨3209041395503955899647219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4278721860671941199529625 3209041395503955899647219)
          ·
            refine ⟨4813562093255933849470829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3209041395503955899647219 4813562093255933849470829)
            ·
              refine ⟨1805085784970975193551561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4813562093255933849470829 1805085784970975193551561)
              ·
                refine ⟨1353814338728231395163671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1805085784970975193551561 1353814338728231395163671)
                ·
                  refine ⟨2030721508092347092745507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353814338728231395163671 2030721508092347092745507)
                  ·
                    refine ⟨3046082262138520639118261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2030721508092347092745507 3046082262138520639118261)
                    ·
                      refine ⟨285570212075486309917337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3046082262138520639118261 285570212075486309917337)
                      ·
                        rfl

theorem cell23_556146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_556146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556146 prefixEnd_556146 := by exact prefixLift 556146
  have htrace : WordTrace (prefixWord ++ tailWord_556146) baseStart_556146 baseEnd_556146 := by
    simpa [prefixWord, tailWord_556146, baseEnd_556146] using wordTrace_append hprefix tailTrace_556146
  have hstable : (prefixWord ++ tailWord_556146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556146).length < 2 ^ (prefixWord ++ tailWord_556146).sum := by decide
  have hdescent : baseEnd_556146 < baseStart_556146 := by decide
  rcases family_descends (prefixWord ++ tailWord_556146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556153 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 1, 6]
def baseStart_556153 : Nat := 118140960795 + 556153 * 2 ^ 59
def prefixEnd_556153 : Nat := 4983230072969 + 3 ^ 40 * 556153 * 2
def baseEnd_556153 : Nat := 95191268813355927509935

theorem tailTrace_556153 : CollatzResearch.WordTrace tailWord_556153 prefixEnd_556153 95191268813355927509935 := by
  unfold tailWord_556153
  simp only [CollatzResearch.WordTrace]
  refine ⟨20284566354160139215497113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13523044236106759476998075 20284566354160139215497113)
  ·
    refine ⟨15213424765620104411622835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20284566354160139215497113 15213424765620104411622835)
    ·
      refine ⟨22820137148430156617434253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15213424765620104411622835 22820137148430156617434253)
      ·
        refine ⟨8557551430661308731537845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22820137148430156617434253 8557551430661308731537845)
        ·
          refine ⟨802270446624497693581673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8557551430661308731537845 802270446624497693581673)
          ·
            refine ⟨601702834968373270186255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802270446624497693581673 601702834968373270186255)
            ·
              refine ⟨902554252452559905279383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601702834968373270186255 902554252452559905279383)
              ·
                refine ⟨1353831378678839857919075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 902554252452559905279383 1353831378678839857919075)
                ·
                  refine ⟨2030747068018259786878613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353831378678839857919075 2030747068018259786878613)
                  ·
                    refine ⟨95191268813355927509935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2030747068018259786878613 95191268813355927509935)
                    ·
                      rfl

theorem cell23_556153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 6].length) (baseStart_556153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556153 prefixEnd_556153 := by exact prefixLift 556153
  have htrace : WordTrace (prefixWord ++ tailWord_556153) baseStart_556153 baseEnd_556153 := by
    simpa [prefixWord, tailWord_556153, baseEnd_556153] using wordTrace_append hprefix tailTrace_556153
  have hstable : (prefixWord ++ tailWord_556153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556153).length < 2 ^ (prefixWord ++ tailWord_556153).sum := by decide
  have hdescent : baseEnd_556153 < baseStart_556153 := by decide
  rcases family_descends (prefixWord ++ tailWord_556153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556163 : List Nat := [1, 1, 1, 3, 3, 2, 4, 2, 1, 2, 3]
def baseStart_556163 : Nat := 118140960795 + 556163 * 2 ^ 59
def prefixEnd_556163 : Nat := 4983230072969 + 3 ^ 40 * 556163 * 2
def baseEnd_556163 : Nat := 285578941246612743404759

theorem tailTrace_556163 : CollatzResearch.WordTrace tailWord_556163 prefixEnd_556163 285578941246612743404759 := by
  unfold tailWord_556163
  simp only [CollatzResearch.WordTrace]
  refine ⟨20284931084123910923361143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13523287389415940615574095 20284931084123910923361143)
  ·
    refine ⟨30427396626185866385041715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20284931084123910923361143 30427396626185866385041715)
    ·
      refine ⟨45641094939278799577562573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30427396626185866385041715 45641094939278799577562573)
      ·
        refine ⟨17115410602229549841585965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45641094939278799577562573 17115410602229549841585965)
        ·
          refine ⟨6418278975836081190594737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17115410602229549841585965 6418278975836081190594737)
          ·
            refine ⟨4813709231877060892946053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6418278975836081190594737 4813709231877060892946053)
            ·
              refine ⟨902570480976948917427385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4813709231877060892946053 902570480976948917427385)
              ·
                refine ⟨676927860732711688070539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 902570480976948917427385 676927860732711688070539)
                ·
                  refine ⟨1015391791099067532105809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 676927860732711688070539 1015391791099067532105809)
                  ·
                    refine ⟨761543843324300649079357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1015391791099067532105809 761543843324300649079357)
                    ·
                      refine ⟨285578941246612743404759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761543843324300649079357 285578941246612743404759)
                      ·
                        rfl

theorem cell23_556163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_556163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556163 prefixEnd_556163 := by exact prefixLift 556163
  have htrace : WordTrace (prefixWord ++ tailWord_556163) baseStart_556163 baseEnd_556163 := by
    simpa [prefixWord, tailWord_556163, baseEnd_556163] using wordTrace_append hprefix tailTrace_556163
  have hstable : (prefixWord ++ tailWord_556163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556163).length < 2 ^ (prefixWord ++ tailWord_556163).sum := by decide
  have hdescent : baseEnd_556163 < baseStart_556163 := by decide
  rcases family_descends (prefixWord ++ tailWord_556163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556193 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_556193 : Nat := 118140960795 + 556193 * 2 ^ 59
def prefixEnd_556193 : Nat := 4983230072969 + 3 ^ 40 * 556193 * 2
def baseEnd_556193 : Nat := 285594345666247626029621

theorem tailTrace_556193 : CollatzResearch.WordTrace tailWord_556193 prefixEnd_556193 285594345666247626029621 := by
  unfold tailWord_556193
  simp only [CollatzResearch.WordTrace]
  refine ⟨20286025274015226046953233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13524016849343484031302155 20286025274015226046953233)
  ·
    refine ⟨15214518955511419535214925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20286025274015226046953233 15214518955511419535214925)
    ·
      refine ⟨5705444608316782325705597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15214518955511419535214925 5705444608316782325705597)
      ·
        refine ⟨2139541728118793372139599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5705444608316782325705597 2139541728118793372139599)
        ·
          refine ⟨3209312592178190058209399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139541728118793372139599 3209312592178190058209399)
          ·
            refine ⟨4813968888267285087314099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3209312592178190058209399 4813968888267285087314099)
            ·
              refine ⟨7220953332400927630971149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4813968888267285087314099 7220953332400927630971149)
              ·
                refine ⟨2707857499650347861614181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7220953332400927630971149 2707857499650347861614181)
                ·
                  refine ⟨507723281184440224052659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2707857499650347861614181 507723281184440224052659)
                  ·
                    refine ⟨761584921776660336078989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 507723281184440224052659 761584921776660336078989)
                    ·
                      refine ⟨285594345666247626029621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761584921776660336078989 285594345666247626029621)
                      ·
                        rfl

theorem cell23_556193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_556193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556193 prefixEnd_556193 := by exact prefixLift 556193
  have htrace : WordTrace (prefixWord ++ tailWord_556193) baseStart_556193 baseEnd_556193 := by
    simpa [prefixWord, tailWord_556193, baseEnd_556193] using wordTrace_append hprefix tailTrace_556193
  have hstable : (prefixWord ++ tailWord_556193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556193).length < 2 ^ (prefixWord ++ tailWord_556193).sum := by decide
  have hdescent : baseEnd_556193 < baseStart_556193 := by decide
  rcases family_descends (prefixWord ++ tailWord_556193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556194 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_556194 : Nat := 118140960795 + 556194 * 2 ^ 59
def prefixEnd_556194 : Nat := 4983230072969 + 3 ^ 40 * 556194 * 2
def baseEnd_556194 : Nat := 285594859146902122117117

theorem tailTrace_556194 : CollatzResearch.WordTrace tailWord_556194 prefixEnd_556194 285594859146902122117117 := by
  unfold tailWord_556194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5071515436752900804434909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13524041164674402145159757 5071515436752900804434909)
  ·
    refine ⟨1901818288782337801663091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5071515436752900804434909 1901818288782337801663091)
    ·
      refine ⟨2852727433173506702494637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1901818288782337801663091 2852727433173506702494637)
      ·
        refine ⟨1069772787440065013435489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2852727433173506702494637 1069772787440065013435489)
        ·
          refine ⟨802329590580048760076617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1069772787440065013435489 802329590580048760076617)
          ·
            refine ⟨601747192935036570057463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802329590580048760076617 601747192935036570057463)
            ·
              refine ⟨902620789402554855086195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601747192935036570057463 902620789402554855086195)
              ·
                refine ⟨1353931184103832282629293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 902620789402554855086195 1353931184103832282629293)
                ·
                  refine ⟨507724194038937105985985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1353931184103832282629293 507724194038937105985985)
                  ·
                    refine ⟨380793145529202829489489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 507724194038937105985985 380793145529202829489489)
                    ·
                      refine ⟨285594859146902122117117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 380793145529202829489489 285594859146902122117117)
                      ·
                        rfl

theorem cell23_556194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_556194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556194 prefixEnd_556194 := by exact prefixLift 556194
  have htrace : WordTrace (prefixWord ++ tailWord_556194) baseStart_556194 baseEnd_556194 := by
    simpa [prefixWord, tailWord_556194, baseEnd_556194] using wordTrace_append hprefix tailTrace_556194
  have hstable : (prefixWord ++ tailWord_556194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556194).length < 2 ^ (prefixWord ++ tailWord_556194).sum := by decide
  have hdescent : baseEnd_556194 < baseStart_556194 := by decide
  rcases family_descends (prefixWord ++ tailWord_556194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556210 : List Nat := [3, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_556210 : Nat := 118140960795 + 556210 * 2 ^ 59
def prefixEnd_556210 : Nat := 4983230072969 + 3 ^ 40 * 556210 * 2
def baseEnd_556210 : Nat := 285603074837374059517043

theorem tailTrace_556210 : CollatzResearch.WordTrace tailWord_556210 prefixEnd_556210 285603074837374059517043 := by
  unfold tailWord_556210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5071661328738409487580521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13524430209969091966881389 5071661328738409487580521)
  ·
    refine ⟨3803745996553807115685391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5071661328738409487580521 3803745996553807115685391)
    ·
      refine ⟨5705618994830710673528087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3803745996553807115685391 5705618994830710673528087)
      ·
        refine ⟨8558428492246066010292131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5705618994830710673528087 8558428492246066010292131)
        ·
          refine ⟨12837642738369099015438197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8558428492246066010292131 12837642738369099015438197)
          ·
            refine ⟨1203529006722103032697331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12837642738369099015438197 1203529006722103032697331)
            ·
              refine ⟨1805293510083154549045997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203529006722103032697331 1805293510083154549045997)
              ·
                refine ⟨676985066281182955892249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1805293510083154549045997 676985066281182955892249)
                ·
                  refine ⟨507738799710887216919187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 676985066281182955892249 507738799710887216919187)
                  ·
                    refine ⟨761608199566330825378781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 507738799710887216919187 761608199566330825378781)
                    ·
                      refine ⟨285603074837374059517043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761608199566330825378781 285603074837374059517043)
                      ·
                        rfl

theorem cell23_556210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_556210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556210 prefixEnd_556210 := by exact prefixLift 556210
  have htrace : WordTrace (prefixWord ++ tailWord_556210) baseStart_556210 baseEnd_556210 := by
    simpa [prefixWord, tailWord_556210, baseEnd_556210] using wordTrace_append hprefix tailTrace_556210
  have hstable : (prefixWord ++ tailWord_556210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556210).length < 2 ^ (prefixWord ++ tailWord_556210).sum := by decide
  have hdescent : baseEnd_556210 < baseStart_556210 := by decide
  rcases family_descends (prefixWord ++ tailWord_556210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556220 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 3, 3, 2]
def baseStart_556220 : Nat := 118140960795 + 556220 * 2 ^ 59
def prefixEnd_556220 : Nat := 4983230072969 + 3 ^ 40 * 556220 * 2
def baseEnd_556220 : Nat := 285608209643919020391997

theorem tailTrace_556220 : CollatzResearch.WordTrace tailWord_556220 prefixEnd_556220 285608209643919020391997 := by
  unfold tailWord_556220
  simp only [CollatzResearch.WordTrace]
  refine ⟨10143505022458704829093057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13524673363278273105457409 10143505022458704829093057)
  ·
    refine ⟨7607628766844028621819793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10143505022458704829093057 7607628766844028621819793)
    ·
      refine ⟨5705721575133021466364845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7607628766844028621819793 5705721575133021466364845)
      ·
        refine ⟨2139645590674883049886817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5705721575133021466364845 2139645590674883049886817)
        ·
          refine ⟨1604734193006162287415113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2139645590674883049886817 1604734193006162287415113)
          ·
            refine ⟨1203550644754621715561335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1604734193006162287415113 1203550644754621715561335)
            ·
              refine ⟨1805325967131932573342003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203550644754621715561335 1805325967131932573342003)
              ·
                refine ⟨2707988950697898860013005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805325967131932573342003 2707988950697898860013005)
                ·
                  refine ⟨1015495856511712072504877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2707988950697898860013005 1015495856511712072504877)
                  ·
                    refine ⟨380810946191892027189329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1015495856511712072504877 380810946191892027189329)
                    ·
                      refine ⟨285608209643919020391997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 380810946191892027189329 285608209643919020391997)
                      ·
                        rfl

theorem cell23_556220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_556220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556220 prefixEnd_556220 := by exact prefixLift 556220
  have htrace : WordTrace (prefixWord ++ tailWord_556220) baseStart_556220 baseEnd_556220 := by
    simpa [prefixWord, tailWord_556220, baseEnd_556220] using wordTrace_append hprefix tailTrace_556220
  have hstable : (prefixWord ++ tailWord_556220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556220).length < 2 ^ (prefixWord ++ tailWord_556220).sum := by decide
  have hdescent : baseEnd_556220 < baseStart_556220 := by decide
  rcases family_descends (prefixWord ++ tailWord_556220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556239 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 11]
def baseStart_556239 : Nat := 118140960795 + 556239 * 2 ^ 59
def prefixEnd_556239 : Nat := 4983230072969 + 3 ^ 40 * 556239 * 2
def baseEnd_556239 : Nat := 31735329530706049561601

theorem tailTrace_556239 : CollatzResearch.WordTrace tailWord_556239 prefixEnd_556239 31735329530706049561601 := by
  unfold tailWord_556239
  simp only [CollatzResearch.WordTrace]
  refine ⟨20287703031848575903127771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13525135354565717268751847 20287703031848575903127771)
  ·
    refine ⟨30431554547772863854691657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20287703031848575903127771 30431554547772863854691657)
    ·
      refine ⟨22823665910829647891018743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30431554547772863854691657 22823665910829647891018743)
      ·
        refine ⟨34235498866244471836528115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22823665910829647891018743 34235498866244471836528115)
        ·
          refine ⟨51353248299366707754792173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34235498866244471836528115 51353248299366707754792173)
          ·
            refine ⟨19257468112262515408047065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51353248299366707754792173 19257468112262515408047065)
            ·
              refine ⟨14443101084196886556035299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19257468112262515408047065 14443101084196886556035299)
              ·
                refine ⟨21664651626295329834052949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14443101084196886556035299 21664651626295329834052949)
                ·
                  refine ⟨31735329530706049561601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 21664651626295329834052949 31735329530706049561601)
                  ·
                    rfl

theorem cell23_556239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 11].length) (baseStart_556239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556239 prefixEnd_556239 := by exact prefixLift 556239
  have htrace : WordTrace (prefixWord ++ tailWord_556239) baseStart_556239 baseEnd_556239 := by
    simpa [prefixWord, tailWord_556239, baseEnd_556239] using wordTrace_append hprefix tailTrace_556239
  have hstable : (prefixWord ++ tailWord_556239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556239).length < 2 ^ (prefixWord ++ tailWord_556239).sum := by decide
  have hdescent : baseEnd_556239 < baseStart_556239 := by decide
  rcases family_descends (prefixWord ++ tailWord_556239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556244 : List Nat := [2, 4, 1, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_556244 : Nat := 118140960795 + 556244 * 2 ^ 59
def prefixEnd_556244 : Nat := 4983230072969 + 3 ^ 40 * 556244 * 2
def baseEnd_556244 : Nat := 285620533179626926491887

theorem tailTrace_556244 : CollatzResearch.WordTrace tailWord_556244 prefixEnd_556244 285620533179626926491887 := by
  unfold tailWord_556244
  simp only [CollatzResearch.WordTrace]
  refine ⟨10143942698415230878529893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13525256931220307838039857 10143942698415230878529893)
  ·
    refine ⟨1901989255952855789724355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10143942698415230878529893 1901989255952855789724355)
    ·
      refine ⟨2852983883929283684586533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1901989255952855789724355 2852983883929283684586533)
      ·
        refine ⟨534934478236740690859975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2852983883929283684586533 534934478236740690859975)
        ·
          refine ⟨802401717355111036289963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534934478236740690859975 802401717355111036289963)
          ·
            refine ⟨1203602576032666554434945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802401717355111036289963 1203602576032666554434945)
            ·
              refine ⟨902701932024499915826209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1203602576032666554434945 902701932024499915826209)
              ·
                refine ⟨677026449018374936869657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 902701932024499915826209 677026449018374936869657)
                ·
                  refine ⟨507769836763781202652243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 677026449018374936869657 507769836763781202652243)
                  ·
                    refine ⟨761654755145671803978365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 507769836763781202652243 761654755145671803978365)
                    ·
                      refine ⟨285620533179626926491887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761654755145671803978365 285620533179626926491887)
                      ·
                        rfl

theorem cell23_556244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_556244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556244 prefixEnd_556244 := by exact prefixLift 556244
  have htrace : WordTrace (prefixWord ++ tailWord_556244) baseStart_556244 baseEnd_556244 := by
    simpa [prefixWord, tailWord_556244, baseEnd_556244] using wordTrace_append hprefix tailTrace_556244
  have hstable : (prefixWord ++ tailWord_556244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556244).length < 2 ^ (prefixWord ++ tailWord_556244).sum := by decide
  have hdescent : baseEnd_556244 < baseStart_556244 := by decide
  rcases family_descends (prefixWord ++ tailWord_556244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556318 : List Nat := [4, 3, 2, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_556318 : Nat := 118140960795 + 556318 * 2 ^ 59
def prefixEnd_556318 : Nat := 4983230072969 + 3 ^ 40 * 556318 * 2
def baseEnd_556318 : Nat := 285658530748059636966547

theorem tailTrace_556318 : CollatzResearch.WordTrace tailWord_556318 prefixEnd_556318 285658530748059636966547 := by
  unfold tailWord_556318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536323049820296549406701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13527056265708248263502405 2536323049820296549406701)
  ·
    refine ⟨951121143682611206027513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2536323049820296549406701 951121143682611206027513)
    ·
      refine ⟨713340857761958404520635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 951121143682611206027513 713340857761958404520635)
      ·
        refine ⟨1070011286642937606780953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713340857761958404520635 1070011286642937606780953)
        ·
          refine ⟨802508464982203205085715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1070011286642937606780953 802508464982203205085715)
          ·
            refine ⟨1203762697473304807628573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802508464982203205085715 1203762697473304807628573)
            ·
              refine ⟨451411011552489302860715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1203762697473304807628573 451411011552489302860715)
              ·
                refine ⟨677116517328733954291073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451411011552489302860715 677116517328733954291073)
                ·
                  refine ⟨507837387996550465718305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 677116517328733954291073 507837387996550465718305)
                  ·
                    refine ⟨380878040997412849288729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 507837387996550465718305 380878040997412849288729)
                    ·
                      refine ⟨285658530748059636966547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 380878040997412849288729 285658530748059636966547)
                      ·
                        rfl

theorem cell23_556318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_556318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556318 prefixEnd_556318 := by exact prefixLift 556318
  have htrace : WordTrace (prefixWord ++ tailWord_556318) baseStart_556318 baseEnd_556318 := by
    simpa [prefixWord, tailWord_556318, baseEnd_556318] using wordTrace_append hprefix tailTrace_556318
  have hstable : (prefixWord ++ tailWord_556318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556318).length < 2 ^ (prefixWord ++ tailWord_556318).sum := by decide
  have hdescent : baseEnd_556318 < baseStart_556318 := by decide
  rcases family_descends (prefixWord ++ tailWord_556318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556336 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 4]
def baseStart_556336 : Nat := 118140960795 + 556336 * 2 ^ 59
def prefixEnd_556336 : Nat := 4983230072969 + 3 ^ 40 * 556336 * 2
def baseEnd_556336 : Nat := 285667773399840566541463

theorem tailTrace_556336 : CollatzResearch.WordTrace tailWord_556336 prefixEnd_556336 285667773399840566541463 := by
  unfold tailWord_556336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10145620456248580734704431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13527493941664774312939241 10145620456248580734704431)
  ·
    refine ⟨15218430684372871102056647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10145620456248580734704431 15218430684372871102056647)
    ·
      refine ⟨22827646026559306653084971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15218430684372871102056647 22827646026559306653084971)
      ·
        refine ⟨34241469039838959979627457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22827646026559306653084971 34241469039838959979627457)
        ·
          refine ⟨25681101779879219984720593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34241469039838959979627457 25681101779879219984720593)
          ·
            refine ⟨19260826334909414988540445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25681101779879219984720593 19260826334909414988540445)
            ·
              refine ⟨7222809875591030620702667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19260826334909414988540445 7222809875591030620702667)
              ·
                refine ⟨10834214813386545931054001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7222809875591030620702667 10834214813386545931054001)
                ·
                  refine ⟨8125661110039909448290501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10834214813386545931054001 8125661110039909448290501)
                  ·
                    refine ⟨1523561458132483021554469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8125661110039909448290501 1523561458132483021554469)
                    ·
                      refine ⟨285667773399840566541463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1523561458132483021554469 285667773399840566541463)
                      ·
                        rfl

theorem cell23_556336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_556336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556336 prefixEnd_556336 := by exact prefixLift 556336
  have htrace : WordTrace (prefixWord ++ tailWord_556336) baseStart_556336 baseEnd_556336 := by
    simpa [prefixWord, tailWord_556336, baseEnd_556336] using wordTrace_append hprefix tailTrace_556336
  have hstable : (prefixWord ++ tailWord_556336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556336).length < 2 ^ (prefixWord ++ tailWord_556336).sum := by decide
  have hdescent : baseEnd_556336 < baseStart_556336 := by decide
  rcases family_descends (prefixWord ++ tailWord_556336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556340 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_556340 : Nat := 118140960795 + 556340 * 2 ^ 59
def prefixEnd_556340 : Nat := 4983230072969 + 3 ^ 40 * 556340 * 2
def baseEnd_556340 : Nat := 285669827322458550891445

theorem tailTrace_556340 : CollatzResearch.WordTrace tailWord_556340 prefixEnd_556340 285669827322458550891445 := by
  unfold tailWord_556340
  simp only [CollatzResearch.WordTrace]
  refine ⟨10145693402241335076277237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13527591202988446768369649 10145693402241335076277237)
  ·
    refine ⟨951158756460125163400991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10145693402241335076277237 951158756460125163400991)
    ·
      refine ⟨1426738134690187745101487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 951158756460125163400991 1426738134690187745101487)
      ·
        refine ⟨2140107202035281617652231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1426738134690187745101487 2140107202035281617652231)
        ·
          refine ⟨3210160803052922426478347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2140107202035281617652231 3210160803052922426478347)
          ·
            refine ⟨4815241204579383639717521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3210160803052922426478347 4815241204579383639717521)
            ·
              refine ⟨3611430903434537729788141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4815241204579383639717521 3611430903434537729788141)
              ·
                refine ⟨1354286588787951648670553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3611430903434537729788141 1354286588787951648670553)
                ·
                  refine ⟨1015714941590963736502915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1354286588787951648670553 1015714941590963736502915)
                  ·
                    refine ⟨1523572412386445604754373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1015714941590963736502915 1523572412386445604754373)
                    ·
                      refine ⟨285669827322458550891445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1523572412386445604754373 285669827322458550891445)
                      ·
                        rfl

theorem cell23_556340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_556340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556340 prefixEnd_556340 := by exact prefixLift 556340
  have htrace : WordTrace (prefixWord ++ tailWord_556340) baseStart_556340 baseEnd_556340 := by
    simpa [prefixWord, tailWord_556340, baseEnd_556340] using wordTrace_append hprefix tailTrace_556340
  have hstable : (prefixWord ++ tailWord_556340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556340).length < 2 ^ (prefixWord ++ tailWord_556340).sum := by decide
  have hdescent : baseEnd_556340 < baseStart_556340 := by decide
  rcases family_descends (prefixWord ++ tailWord_556340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556346 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 10]
def baseStart_556346 : Nat := 118140960795 + 556346 * 2 ^ 59
def prefixEnd_556346 : Nat := 4983230072969 + 3 ^ 40 * 556346 * 2
def baseEnd_556346 : Nat := 31741434245153947490713

theorem tailTrace_556346 : CollatzResearch.WordTrace tailWord_556346 prefixEnd_556346 31741434245153947490713 := by
  unfold tailWord_556346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5072901410615233294318223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13527737094973955451515261 5072901410615233294318223)
  ·
    refine ⟨7609352115922849941477335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5072901410615233294318223 7609352115922849941477335)
    ·
      refine ⟨11414028173884274912216003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7609352115922849941477335 11414028173884274912216003)
      ·
        refine ⟨17121042260826412368324005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11414028173884274912216003 17121042260826412368324005)
        ·
          refine ⟨3210195423904952319060751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17121042260826412368324005 3210195423904952319060751)
          ·
            refine ⟨4815293135857428478591127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3210195423904952319060751 4815293135857428478591127)
            ·
              refine ⟨7222939703786142717886691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4815293135857428478591127 7222939703786142717886691)
              ·
                refine ⟨10834409555679214076830037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7222939703786142717886691 10834409555679214076830037)
                ·
                  refine ⟨31741434245153947490713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 10834409555679214076830037 31741434245153947490713)
                  ·
                    rfl

theorem cell23_556346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_556346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556346 prefixEnd_556346 := by exact prefixLift 556346
  have htrace : WordTrace (prefixWord ++ tailWord_556346) baseStart_556346 baseEnd_556346 := by
    simpa [prefixWord, tailWord_556346, baseEnd_556346] using wordTrace_append hprefix tailTrace_556346
  have hstable : (prefixWord ++ tailWord_556346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556346).length < 2 ^ (prefixWord ++ tailWord_556346).sum := by decide
  have hdescent : baseEnd_556346 < baseStart_556346 := by decide
  rcases family_descends (prefixWord ++ tailWord_556346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556393 : List Nat := [1, 2, 1, 1, 1, 3, 2, 6, 1, 5]
def baseStart_556393 : Nat := 118140960795 + 556393 * 2 ^ 59
def prefixEnd_556393 : Nat := 4983230072969 + 3 ^ 40 * 556393 * 2
def baseEnd_556393 : Nat := 95232347265715614509567

theorem tailTrace_556393 : CollatzResearch.WordTrace tailWord_556393 prefixEnd_556393 95232347265715614509567 := by
  unfold tailWord_556393
  simp only [CollatzResearch.WordTrace]
  refine ⟨20293319873290660204233833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13528879915527106802822555 20293319873290660204233833)
  ·
    refine ⟨15219989904967995153175375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20293319873290660204233833 15219989904967995153175375)
    ·
      refine ⟨22829984857451992729763063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15219989904967995153175375 22829984857451992729763063)
      ·
        refine ⟨34244977286177989094644595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22829984857451992729763063 34244977286177989094644595)
        ·
          refine ⟨51367465929266983641966893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34244977286177989094644595 51367465929266983641966893)
          ·
            refine ⟨19262799723475118865737585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51367465929266983641966893 19262799723475118865737585)
            ·
              refine ⟨14447099792606339149303189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19262799723475118865737585 14447099792606339149303189)
              ·
                refine ⟨677207802778422147623587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14447099792606339149303189 677207802778422147623587)
                ·
                  refine ⟨1015811704167633221435381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677207802778422147623587 1015811704167633221435381)
                  ·
                    refine ⟨95232347265715614509567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1015811704167633221435381 95232347265715614509567)
                    ·
                      rfl

theorem cell23_556393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 5].length) (baseStart_556393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556393 prefixEnd_556393 := by exact prefixLift 556393
  have htrace : WordTrace (prefixWord ++ tailWord_556393) baseStart_556393 baseEnd_556393 := by
    simpa [prefixWord, tailWord_556393, baseEnd_556393] using wordTrace_append hprefix tailTrace_556393
  have hstable : (prefixWord ++ tailWord_556393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556393).length < 2 ^ (prefixWord ++ tailWord_556393).sum := by decide
  have hdescent : baseEnd_556393 < baseStart_556393 := by decide
  rcases family_descends (prefixWord ++ tailWord_556393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556407 : List Nat := [1, 1, 3, 1, 1, 2, 4, 5, 1, 1, 3]
def baseStart_556407 : Nat := 118140960795 + 556407 * 2 ^ 59
def prefixEnd_556407 : Nat := 4983230072969 + 3 ^ 40 * 556407 * 2
def baseEnd_556407 : Nat := 285704230526309788753637

theorem tailTrace_556407 : CollatzResearch.WordTrace tailWord_556407 prefixEnd_556407 285704230526309788753637 := by
  unfold tailWord_556407
  simp only [CollatzResearch.WordTrace]
  refine ⟨20293830495239940595243475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13529220330159960396828983 20293830495239940595243475)
  ·
    refine ⟨30440745742859910892865213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20293830495239940595243475 30440745742859910892865213)
    ·
      refine ⟨11415279653572466584824455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30440745742859910892865213 11415279653572466584824455)
      ·
        refine ⟨17122919480358699877236683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11415279653572466584824455 17122919480358699877236683)
        ·
          refine ⟨25684379220538049815855025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17122919480358699877236683 25684379220538049815855025)
          ·
            refine ⟨19263284415403537361891269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25684379220538049815855025 19263284415403537361891269)
            ·
              refine ⟨3611865827888163255354613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19263284415403537361891269 3611865827888163255354613)
              ·
                refine ⟨338612421364515305189495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3611865827888163255354613 338612421364515305189495)
                ·
                  refine ⟨507918632046772957784243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338612421364515305189495 507918632046772957784243)
                  ·
                    refine ⟨761877948070159436676365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 507918632046772957784243 761877948070159436676365)
                    ·
                      refine ⟨285704230526309788753637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761877948070159436676365 285704230526309788753637)
                      ·
                        rfl

theorem cell23_556407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 1, 1, 3].length) (baseStart_556407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556407 prefixEnd_556407 := by exact prefixLift 556407
  have htrace : WordTrace (prefixWord ++ tailWord_556407) baseStart_556407 baseEnd_556407 := by
    simpa [prefixWord, tailWord_556407, baseEnd_556407] using wordTrace_append hprefix tailTrace_556407
  have hstable : (prefixWord ++ tailWord_556407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556407).length < 2 ^ (prefixWord ++ tailWord_556407).sum := by decide
  have hdescent : baseEnd_556407 < baseStart_556407 := by decide
  rcases family_descends (prefixWord ++ tailWord_556407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556414 : List Nat := [4, 2, 3, 2, 1, 1, 2, 2, 6]
def baseStart_556414 : Nat := 118140960795 + 556414 * 2 ^ 59
def prefixEnd_556414 : Nat := 4983230072969 + 3 ^ 40 * 556414 * 2
def baseEnd_556414 : Nat := 31745313876765695707345

theorem tailTrace_556414 : CollatzResearch.WordTrace tailWord_556414 prefixEnd_556414 31745313876765695707345 := by
  unfold tailWord_556414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536760725776822598843537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13529390537476387193832197 2536760725776822598843537)
  ·
    refine ⟨1902570544332616949132653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2536760725776822598843537 1902570544332616949132653)
    ·
      refine ⟨713463954124731355924745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1902570544332616949132653 713463954124731355924745)
      ·
        refine ⟨535097965593548516943559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 713463954124731355924745 535097965593548516943559)
        ·
          refine ⟨802646948390322775415339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535097965593548516943559 802646948390322775415339)
          ·
            refine ⟨1203970422585484163123009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802646948390322775415339 1203970422585484163123009)
            ·
              refine ⟨902977816939113122342257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1203970422585484163123009 902977816939113122342257)
              ·
                refine ⟨677233362704334841756693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 902977816939113122342257 677233362704334841756693)
                ·
                  refine ⟨31745313876765695707345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 677233362704334841756693 31745313876765695707345)
                  ·
                    rfl

theorem cell23_556414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_556414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556414 prefixEnd_556414 := by exact prefixLift 556414
  have htrace : WordTrace (prefixWord ++ tailWord_556414) baseStart_556414 baseEnd_556414 := by
    simpa [prefixWord, tailWord_556414, baseEnd_556414] using wordTrace_append hprefix tailTrace_556414
  have hstable : (prefixWord ++ tailWord_556414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556414).length < 2 ^ (prefixWord ++ tailWord_556414).sum := by decide
  have hdescent : baseEnd_556414 < baseStart_556414 := by decide
  rcases family_descends (prefixWord ++ tailWord_556414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556418 : List Nat := [3, 4, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_556418 : Nat := 118140960795 + 556418 * 2 ^ 59
def prefixEnd_556418 : Nat := 4983230072969 + 3 ^ 40 * 556418 * 2
def baseEnd_556418 : Nat := 95236626271169748572029

theorem tailTrace_556418 : CollatzResearch.WordTrace tailWord_556418 prefixEnd_556418 95236626271169748572029 := by
  unfold tailWord_556418
  simp only [CollatzResearch.WordTrace]
  refine ⟨5073557924550022368473477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13529487798800059649262605 5073557924550022368473477)
  ·
    refine ⟨951292110853129194088777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5073557924550022368473477 951292110853129194088777)
    ·
      refine ⟨713469083139846895566583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 951292110853129194088777 713469083139846895566583)
      ·
        refine ⟨1070203624709770343349875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713469083139846895566583 1070203624709770343349875)
        ·
          refine ⟨1605305437064655515024813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070203624709770343349875 1605305437064655515024813)
          ·
            refine ⟨601989538899245818134305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1605305437064655515024813 601989538899245818134305)
            ·
              refine ⟨451492154174434363600729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601989538899245818134305 451492154174434363600729)
              ·
                refine ⟨338619115630825772700547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451492154174434363600729 338619115630825772700547)
                ·
                  refine ⟨507928673446238659050821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338619115630825772700547 507928673446238659050821)
                  ·
                    refine ⟨95236626271169748572029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 507928673446238659050821 95236626271169748572029)
                    ·
                      rfl

theorem cell23_556418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_556418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556418 prefixEnd_556418 := by exact prefixLift 556418
  have htrace : WordTrace (prefixWord ++ tailWord_556418) baseStart_556418 baseEnd_556418 := by
    simpa [prefixWord, tailWord_556418, baseEnd_556418] using wordTrace_append hprefix tailTrace_556418
  have hstable : (prefixWord ++ tailWord_556418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556418).length < 2 ^ (prefixWord ++ tailWord_556418).sum := by decide
  have hdescent : baseEnd_556418 < baseStart_556418 := by decide
  rcases family_descends (prefixWord ++ tailWord_556418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556424 : List Nat := [2, 1, 3, 3, 1, 3, 1, 4, 1, 1, 3]
def baseStart_556424 : Nat := 118140960795 + 556424 * 2 ^ 59
def prefixEnd_556424 : Nat := 4983230072969 + 3 ^ 40 * 556424 * 2
def baseEnd_556424 : Nat := 285712959697436222241059

theorem tailTrace_556424 : CollatzResearch.WordTrace tailWord_556424 prefixEnd_556424 285712959697436222241059 := by
  unfold tailWord_556424
  simp only [CollatzResearch.WordTrace]
  refine ⟨10147225268089176249306163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13529633690785568332408217 10147225268089176249306163)
  ·
    refine ⟨15220837902133764373959245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10147225268089176249306163 15220837902133764373959245)
    ·
      refine ⟨5707814213300161640234717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15220837902133764373959245 5707814213300161640234717)
      ·
        refine ⟨2140430329987560615088019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5707814213300161640234717 2140430329987560615088019)
        ·
          refine ⟨3210645494981340922632029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2140430329987560615088019 3210645494981340922632029)
          ·
            refine ⟨1203992060618002845987011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3210645494981340922632029 1203992060618002845987011)
            ·
              refine ⟨1805988090927004268980517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203992060618002845987011 1805988090927004268980517)
              ·
                refine ⟨338622767048813300433847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1805988090927004268980517 338622767048813300433847)
                ·
                  refine ⟨507934150573219950650771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338622767048813300433847 507934150573219950650771)
                  ·
                    refine ⟨761901225859829925976157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 507934150573219950650771 761901225859829925976157)
                    ·
                      refine ⟨285712959697436222241059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 761901225859829925976157 285712959697436222241059)
                      ·
                        rfl

theorem cell23_556424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_556424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556424 prefixEnd_556424 := by exact prefixLift 556424
  have htrace : WordTrace (prefixWord ++ tailWord_556424) baseStart_556424 baseEnd_556424 := by
    simpa [prefixWord, tailWord_556424, baseEnd_556424] using wordTrace_append hprefix tailTrace_556424
  have hstable : (prefixWord ++ tailWord_556424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556424).length < 2 ^ (prefixWord ++ tailWord_556424).sum := by decide
  have hdescent : baseEnd_556424 < baseStart_556424 := by decide
  rcases family_descends (prefixWord ++ tailWord_556424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556447 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 5, 2, 2]
def baseStart_556447 : Nat := 118140960795 + 556447 * 2 ^ 59
def prefixEnd_556447 : Nat := 4983230072969 + 3 ^ 40 * 556447 * 2
def baseEnd_556447 : Nat := 285724769752489632253453

theorem tailTrace_556447 : CollatzResearch.WordTrace tailWord_556447 prefixEnd_556447 285724769752489632253453 := by
  unfold tailWord_556447
  simp only [CollatzResearch.WordTrace]
  refine ⟨20295289415095027426699595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13530192943396684951133063 20295289415095027426699595)
  ·
    refine ⟨30442934122642541140049393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20295289415095027426699595 30442934122642541140049393)
    ·
      refine ⟨22832200591981905855037045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30442934122642541140049393 22832200591981905855037045)
      ·
        refine ⟨2140518805498303673909723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22832200591981905855037045 2140518805498303673909723)
        ·
          refine ⟨3210778208247455510864585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2140518805498303673909723 3210778208247455510864585)
          ·
            refine ⟨2408083656185591633148439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3210778208247455510864585 2408083656185591633148439)
            ·
              refine ⟨3612125484278387449722659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408083656185591633148439 3612125484278387449722659)
              ·
                refine ⟨5418188226417581174583989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612125484278387449722659 5418188226417581174583989)
                ·
                  refine ⟨507955146226648235117249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5418188226417581174583989 507955146226648235117249)
                  ·
                    refine ⟨380966359669986176337937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 507955146226648235117249 380966359669986176337937)
                    ·
                      refine ⟨285724769752489632253453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 380966359669986176337937 285724769752489632253453)
                      ·
                        rfl

theorem cell23_556447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_556447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556447 prefixEnd_556447 := by exact prefixLift 556447
  have htrace : WordTrace (prefixWord ++ tailWord_556447) baseStart_556447 baseEnd_556447 := by
    simpa [prefixWord, tailWord_556447, baseEnd_556447] using wordTrace_append hprefix tailTrace_556447
  have hstable : (prefixWord ++ tailWord_556447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556447).length < 2 ^ (prefixWord ++ tailWord_556447).sum := by decide
  have hdescent : baseEnd_556447 < baseStart_556447 := by decide
  rcases family_descends (prefixWord ++ tailWord_556447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556503 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_556503 : Nat := 118140960795 + 556503 * 2 ^ 59
def prefixEnd_556503 : Nat := 4983230072969 + 3 ^ 40 * 556503 * 2
def baseEnd_556503 : Nat := 285753524669141413153195

theorem tailTrace_556503 : CollatzResearch.WordTrace tailWord_556503 prefixEnd_556503 285753524669141413153195 := by
  unfold tailWord_556503
  simp only [CollatzResearch.WordTrace]
  refine ⟨20297331902892148990738163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13531554601928099327158775 20297331902892148990738163)
  ·
    refine ⟨30445997854338223486107245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20297331902892148990738163 30445997854338223486107245)
    ·
      refine ⟨11417249195376833807290217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30445997854338223486107245 11417249195376833807290217)
      ·
        refine ⟨8562936896532625355467663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11417249195376833807290217 8562936896532625355467663)
        ·
          refine ⟨12844405344798938033201495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8562936896532625355467663 12844405344798938033201495)
          ·
            refine ⟨19266608017198407049802243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12844405344798938033201495 19266608017198407049802243)
            ·
              refine ⟨28899912025797610574703365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19266608017198407049802243 28899912025797610574703365)
              ·
                refine ⟨5418733504837051982756881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28899912025797610574703365 5418733504837051982756881)
                ·
                  refine ⟨4064050128627788987067661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5418733504837051982756881 4064050128627788987067661)
                  ·
                    refine ⟨1524018798235420870150373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4064050128627788987067661 1524018798235420870150373)
                    ·
                      refine ⟨285753524669141413153195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1524018798235420870150373 285753524669141413153195)
                      ·
                        rfl

theorem cell23_556503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_556503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556503 prefixEnd_556503 := by exact prefixLift 556503
  have htrace : WordTrace (prefixWord ++ tailWord_556503) baseStart_556503 baseEnd_556503 := by
    simpa [prefixWord, tailWord_556503, baseEnd_556503] using wordTrace_append hprefix tailTrace_556503
  have hstable : (prefixWord ++ tailWord_556503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556503).length < 2 ^ (prefixWord ++ tailWord_556503).sum := by decide
  have hdescent : baseEnd_556503 < baseStart_556503 := by decide
  rcases family_descends (prefixWord ++ tailWord_556503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556543 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 7]
def baseStart_556543 : Nat := 118140960795 + 556543 * 2 ^ 59
def prefixEnd_556543 : Nat := 4983230072969 + 3 ^ 40 * 556543 * 2
def baseEnd_556543 : Nat := 31752673766146806294779

theorem tailTrace_556543 : CollatzResearch.WordTrace tailWord_556543 prefixEnd_556543 31752673766146806294779 := by
  unfold tailWord_556543
  simp only [CollatzResearch.WordTrace]
  refine ⟨20298790822747235822194283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13532527215164823881462855 20298790822747235822194283)
  ·
    refine ⟨30448186234120853733291425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20298790822747235822194283 30448186234120853733291425)
    ·
      refine ⟨22836139675590640299968569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30448186234120853733291425 22836139675590640299968569)
      ·
        refine ⟨17127104756692980224976427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22836139675590640299968569 17127104756692980224976427)
        ·
          refine ⟨25690657135039470337464641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17127104756692980224976427 25690657135039470337464641)
          ·
            refine ⟨19267992851279602753098481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25690657135039470337464641 19267992851279602753098481)
            ·
              refine ⟨14450994638459702064823861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19267992851279602753098481 14450994638459702064823861)
              ·
                refine ⟨1354780747355597068577237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14450994638459702064823861 1354780747355597068577237)
                ·
                  refine ⟨31752673766146806294779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1354780747355597068577237 31752673766146806294779)
                  ·
                    rfl

theorem cell23_556543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 7].length) (baseStart_556543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556543 prefixEnd_556543 := by exact prefixLift 556543
  have htrace : WordTrace (prefixWord ++ tailWord_556543) baseStart_556543 baseEnd_556543 := by
    simpa [prefixWord, tailWord_556543, baseEnd_556543] using wordTrace_append hprefix tailTrace_556543
  have hstable : (prefixWord ++ tailWord_556543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556543).length < 2 ^ (prefixWord ++ tailWord_556543).sum := by decide
  have hdescent : baseEnd_556543 < baseStart_556543 := by decide
  rcases family_descends (prefixWord ++ tailWord_556543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556548 : List Nat := [2, 3, 2, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_556548 : Nat := 118140960795 + 556548 * 2 ^ 59
def prefixEnd_556548 : Nat := 4983230072969 + 3 ^ 40 * 556548 * 2
def baseEnd_556548 : Nat := 285776631298593737090489

theorem tailTrace_556548 : CollatzResearch.WordTrace tailWord_556548 prefixEnd_556548 285776631298593737090489 := by
  unfold tailWord_556548
  simp only [CollatzResearch.WordTrace]
  refine ⟨10149486593864560838063149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13532648791819414450750865 10149486593864560838063149)
  ·
    refine ⟨3806057472699210314273681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10149486593864560838063149 3806057472699210314273681)
    ·
      refine ⟨2854543104524407735705261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3806057472699210314273681 2854543104524407735705261)
      ·
        refine ⟨1070453664196652900889473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2854543104524407735705261 1070453664196652900889473)
        ·
          refine ⟨802840248147489675667105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1070453664196652900889473 802840248147489675667105)
          ·
            refine ⟨602130186110617256750329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802840248147489675667105 602130186110617256750329)
            ·
              refine ⟨451597639582962942562747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602130186110617256750329 451597639582962942562747)
              ·
                refine ⟨677396459374444413844121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451597639582962942562747 677396459374444413844121)
                ·
                  refine ⟨508047344530833310383091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 677396459374444413844121 508047344530833310383091)
                  ·
                    refine ⟨762071016796249965574637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 508047344530833310383091 762071016796249965574637)
                    ·
                      refine ⟨285776631298593737090489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 762071016796249965574637 285776631298593737090489)
                      ·
                        rfl

theorem cell23_556548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_556548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556548 prefixEnd_556548 := by exact prefixLift 556548
  have htrace : WordTrace (prefixWord ++ tailWord_556548) baseStart_556548 baseEnd_556548 := by
    simpa [prefixWord, tailWord_556548, baseEnd_556548] using wordTrace_append hprefix tailTrace_556548
  have hstable : (prefixWord ++ tailWord_556548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556548).length < 2 ^ (prefixWord ++ tailWord_556548).sum := by decide
  have hdescent : baseEnd_556548 < baseStart_556548 := by decide
  rcases family_descends (prefixWord ++ tailWord_556548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556558 : List Nat := [4, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2]
def baseStart_556558 : Nat := 118140960795 + 556558 * 2 ^ 59
def prefixEnd_556558 : Nat := 4983230072969 + 3 ^ 40 * 556558 * 2
def baseEnd_556558 : Nat := 285781766105138697965443

theorem tailTrace_556558 : CollatzResearch.WordTrace tailWord_556558 prefixEnd_556558 285781766105138697965443 := by
  unfold tailWord_556558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2537417239711611672998791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13532891945128595589326885 2537417239711611672998791)
  ·
    refine ⟨3806125859567417509498187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2537417239711611672998791 3806125859567417509498187)
    ·
      refine ⟨5709188789351126264247281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3806125859567417509498187 5709188789351126264247281)
      ·
        refine ⟨4281891592013344698185461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5709188789351126264247281 4281891592013344698185461)
        ·
          refine ⟨401427336751251065454887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4281891592013344698185461 401427336751251065454887)
          ·
            refine ⟨602141005126876598182331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401427336751251065454887 602141005126876598182331)
            ·
              refine ⟨903211507690314897273497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602141005126876598182331 903211507690314897273497)
              ·
                refine ⟨677408630767736172955123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 903211507690314897273497 677408630767736172955123)
                ·
                  refine ⟨1016112946151604259432685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677408630767736172955123 1016112946151604259432685)
                  ·
                    refine ⟨381042354806851597287257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1016112946151604259432685 381042354806851597287257)
                    ·
                      refine ⟨285781766105138697965443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 381042354806851597287257 285781766105138697965443)
                      ·
                        rfl

theorem cell23_556558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_556558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556558 prefixEnd_556558 := by exact prefixLift 556558
  have htrace : WordTrace (prefixWord ++ tailWord_556558) baseStart_556558 baseEnd_556558 := by
    simpa [prefixWord, tailWord_556558, baseEnd_556558] using wordTrace_append hprefix tailTrace_556558
  have hstable : (prefixWord ++ tailWord_556558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556558).length < 2 ^ (prefixWord ++ tailWord_556558).sum := by decide
  have hdescent : baseEnd_556558 < baseStart_556558 := by decide
  rcases family_descends (prefixWord ++ tailWord_556558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556570 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3]
def baseStart_556570 : Nat := 118140960795 + 556570 * 2 ^ 59
def prefixEnd_556570 : Nat := 4983230072969 + 3 ^ 40 * 556570 * 2
def baseEnd_556570 : Nat := 285787927872992651015387

theorem tailTrace_556570 : CollatzResearch.WordTrace tailWord_556570 prefixEnd_556570 285787927872992651015387 := by
  unfold tailWord_556570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5074943898412354858356791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13533183729099612955618109 5074943898412354858356791)
  ·
    refine ⟨7612415847618532287535187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5074943898412354858356791 7612415847618532287535187)
    ·
      refine ⟨11418623771427798431302781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7612415847618532287535187 11418623771427798431302781)
      ·
        refine ⟨4281983914285424411738543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11418623771427798431302781 4281983914285424411738543)
        ·
          refine ⟨6422975871428136617607815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4281983914285424411738543 6422975871428136617607815)
          ·
            refine ⟨9634463807142204926411723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6422975871428136617607815 9634463807142204926411723)
            ·
              refine ⟨14451695710713307389617585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9634463807142204926411723 14451695710713307389617585)
              ·
                refine ⟨10838771783034980542213189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14451695710713307389617585 10838771783034980542213189)
                ·
                  refine ⟨2032269709319058851664973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10838771783034980542213189 2032269709319058851664973)
                  ·
                    refine ⟨762101140994647069374365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2032269709319058851664973 762101140994647069374365)
                    ·
                      refine ⟨285787927872992651015387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 762101140994647069374365 285787927872992651015387)
                      ·
                        rfl

theorem cell23_556570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_556570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556570 prefixEnd_556570 := by exact prefixLift 556570
  have htrace : WordTrace (prefixWord ++ tailWord_556570) baseStart_556570 baseEnd_556570 := by
    simpa [prefixWord, tailWord_556570, baseEnd_556570] using wordTrace_append hprefix tailTrace_556570
  have hstable : (prefixWord ++ tailWord_556570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556570).length < 2 ^ (prefixWord ++ tailWord_556570).sum := by decide
  have hdescent : baseEnd_556570 < baseStart_556570 := by decide
  rcases family_descends (prefixWord ++ tailWord_556570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556597 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_556597 : Nat := 118140960795 + 556597 * 2 ^ 59
def prefixEnd_556597 : Nat := 4983230072969 + 3 ^ 40 * 556597 * 2
def baseEnd_556597 : Nat := 285801791850664045377763

theorem tailTrace_556597 : CollatzResearch.WordTrace tailWord_556597 prefixEnd_556597 285801791850664045377763 := by
  unfold tailWord_556597
  simp only [CollatzResearch.WordTrace]
  refine ⟨20300760364551603044660045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13533840243034402029773363 20300760364551603044660045)
  ·
    refine ⟨7612785136706851141747517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20300760364551603044660045 7612785136706851141747517)
    ·
      refine ⟨2854794426265069178155319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7612785136706851141747517 2854794426265069178155319)
      ·
        refine ⟨4282191639397603767232979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2854794426265069178155319 4282191639397603767232979)
        ·
          refine ⟨6423287459096405650849469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4282191639397603767232979 6423287459096405650849469)
          ·
            refine ⟨2408732797161152119068551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6423287459096405650849469 2408732797161152119068551)
            ·
              refine ⟨3613099195741728178602827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408732797161152119068551 3613099195741728178602827)
              ·
                refine ⟨5419648793612592267904241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3613099195741728178602827 5419648793612592267904241)
                ·
                  refine ⟨4064736595209444200928181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5419648793612592267904241 4064736595209444200928181)
                  ·
                    refine ⟨381069055800885393837017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4064736595209444200928181 381069055800885393837017)
                    ·
                      refine ⟨285801791850664045377763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 381069055800885393837017 285801791850664045377763)
                      ·
                        rfl

theorem cell23_556597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_556597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556597 prefixEnd_556597 := by exact prefixLift 556597
  have htrace : WordTrace (prefixWord ++ tailWord_556597) baseStart_556597 baseEnd_556597 := by
    simpa [prefixWord, tailWord_556597, baseEnd_556597] using wordTrace_append hprefix tailTrace_556597
  have hstable : (prefixWord ++ tailWord_556597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556597).length < 2 ^ (prefixWord ++ tailWord_556597).sum := by decide
  have hdescent : baseEnd_556597 < baseStart_556597 := by decide
  rcases family_descends (prefixWord ++ tailWord_556597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556600 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_556600 : Nat := 118140960795 + 556600 * 2 ^ 59
def prefixEnd_556600 : Nat := 4983230072969 + 3 ^ 40 * 556600 * 2
def baseEnd_556600 : Nat := 285803332292627533640249

theorem tailTrace_556600 : CollatzResearch.WordTrace tailWord_556600 prefixEnd_556600 285803332292627533640249 := by
  unfold tailWord_556600
  simp only [CollatzResearch.WordTrace]
  refine ⟨10150434891770367278509627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13533913189027156371346169 10150434891770367278509627)
  ·
    refine ⟨15225652337655550917764441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10150434891770367278509627 15225652337655550917764441)
    ·
      refine ⟨11419239253241663188323331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15225652337655550917764441 11419239253241663188323331)
      ·
        refine ⟨17128858879862494782484997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11419239253241663188323331 17128858879862494782484997)
        ·
          refine ⟨3211661039974217771715937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17128858879862494782484997 3211661039974217771715937)
          ·
            refine ⟨2408745779980663328786953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3211661039974217771715937 2408745779980663328786953)
            ·
              refine ⟨1806559334985497496590215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2408745779980663328786953 1806559334985497496590215)
              ·
                refine ⟨2709839002478246244885323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806559334985497496590215 2709839002478246244885323)
                ·
                  refine ⟨4064758503717369367327985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709839002478246244885323 4064758503717369367327985)
                  ·
                    refine ⟨3048568877788027025495989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4064758503717369367327985 3048568877788027025495989)
                    ·
                      refine ⟨285803332292627533640249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3048568877788027025495989 285803332292627533640249)
                      ·
                        rfl

theorem cell23_556600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_556600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556600 prefixEnd_556600 := by exact prefixLift 556600
  have htrace : WordTrace (prefixWord ++ tailWord_556600) baseStart_556600 baseEnd_556600 := by
    simpa [prefixWord, tailWord_556600, baseEnd_556600] using wordTrace_append hprefix tailTrace_556600
  have hstable : (prefixWord ++ tailWord_556600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556600).length < 2 ^ (prefixWord ++ tailWord_556600).sum := by decide
  have hdescent : baseEnd_556600 < baseStart_556600 := by decide
  rcases family_descends (prefixWord ++ tailWord_556600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556647 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_556647 : Nat := 118140960795 + 556647 * 2 ^ 59
def prefixEnd_556647 : Nat := 4983230072969 + 3 ^ 40 * 556647 * 2
def baseEnd_556647 : Nat := 285827465883388849752533

theorem tailTrace_556647 : CollatzResearch.WordTrace tailWord_556647 prefixEnd_556647 285827465883388849752533 := by
  unfold tailWord_556647
  simp only [CollatzResearch.WordTrace]
  refine ⟨20302584014370461583980195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13535056009580307722653463 20302584014370461583980195)
  ·
    refine ⟨30453876021555692375970293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20302584014370461583980195 30453876021555692375970293)
    ·
      refine ⟨2855050877020846160247215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30453876021555692375970293 2855050877020846160247215)
      ·
        refine ⟨4282576315531269240370823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2855050877020846160247215 4282576315531269240370823)
        ·
          refine ⟨6423864473296903860556235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4282576315531269240370823 6423864473296903860556235)
          ·
            refine ⟨9635796709945355790834353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6423864473296903860556235 9635796709945355790834353)
            ·
              refine ⟨7226847532459016843125765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9635796709945355790834353 7226847532459016843125765)
              ·
                refine ⟨1355033912336065658086081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7226847532459016843125765 1355033912336065658086081)
                ·
                  refine ⟨1016275434252049243564561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1355033912336065658086081 1016275434252049243564561)
                  ·
                    refine ⟨762206575689036932673421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1016275434252049243564561 762206575689036932673421)
                    ·
                      refine ⟨285827465883388849752533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 762206575689036932673421 285827465883388849752533)
                      ·
                        rfl

theorem cell23_556647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_556647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556647 prefixEnd_556647 := by exact prefixLift 556647
  have htrace : WordTrace (prefixWord ++ tailWord_556647) baseStart_556647 baseEnd_556647 := by
    simpa [prefixWord, tailWord_556647, baseEnd_556647] using wordTrace_append hprefix tailTrace_556647
  have hstable : (prefixWord ++ tailWord_556647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556647).length < 2 ^ (prefixWord ++ tailWord_556647).sum := by decide
  have hdescent : baseEnd_556647 < baseStart_556647 := by decide
  rcases family_descends (prefixWord ++ tailWord_556647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556667 : List Nat := [1, 1, 1, 1, 1, 4, 7, 1, 6]
def baseStart_556667 : Nat := 118140960795 + 556667 * 2 ^ 59
def prefixEnd_556667 : Nat := 4983230072969 + 3 ^ 40 * 556667 * 2
def baseEnd_556667 : Nat := 31759748388497641278049

theorem tailTrace_556667 : CollatzResearch.WordTrace tailWord_556667 prefixEnd_556667 31759748388497641278049 := by
  unfold tailWord_556667
  simp only [CollatzResearch.WordTrace]
  refine ⟨20303313474298004999708255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13535542316198669999805503 20303313474298004999708255)
  ·
    refine ⟨30454970211447007499562383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20303313474298004999708255 30454970211447007499562383)
    ·
      refine ⟨45682455317170511249343575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30454970211447007499562383 45682455317170511249343575)
      ·
        refine ⟨68523682975755766874015363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45682455317170511249343575 68523682975755766874015363)
        ·
          refine ⟨102785524463633650311023045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68523682975755766874015363 102785524463633650311023045)
          ·
            refine ⟨19272285836931309433316821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102785524463633650311023045 19272285836931309433316821)
            ·
              refine ⟨451694199303077564843363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19272285836931309433316821 451694199303077564843363)
              ·
                refine ⟨677541298954616347265045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451694199303077564843363 677541298954616347265045)
                ·
                  refine ⟨31759748388497641278049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 677541298954616347265045 31759748388497641278049)
                  ·
                    rfl

theorem cell23_556667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 6].length) (baseStart_556667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556667 prefixEnd_556667 := by exact prefixLift 556667
  have htrace : WordTrace (prefixWord ++ tailWord_556667) baseStart_556667 baseEnd_556667 := by
    simpa [prefixWord, tailWord_556667, baseEnd_556667] using wordTrace_append hprefix tailTrace_556667
  have hstable : (prefixWord ++ tailWord_556667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556667).length < 2 ^ (prefixWord ++ tailWord_556667).sum := by decide
  have hdescent : baseEnd_556667 < baseStart_556667 := by decide
  rcases family_descends (prefixWord ++ tailWord_556667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556704 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 4, 3, 2]
def baseStart_556704 : Nat := 118140960795 + 556704 * 2 ^ 59
def prefixEnd_556704 : Nat := 4983230072969 + 3 ^ 40 * 556704 * 2
def baseEnd_556704 : Nat := 285856734280695126739771

theorem tailTrace_556704 : CollatzResearch.WordTrace tailWord_556704 prefixEnd_556704 285856734280695126739771 := by
  unfold tailWord_556704
  simp only [CollatzResearch.WordTrace]
  refine ⟨10152331487581980159402583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13536441983442640212536777 10152331487581980159402583)
  ·
    refine ⟨15228497231372970239103875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10152331487581980159402583 15228497231372970239103875)
    ·
      refine ⟨22842745847059455358655813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15228497231372970239103875 22842745847059455358655813)
      ·
        refine ⟨4283014846323647879747965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22842745847059455358655813 4283014846323647879747965)
        ·
          refine ⟨1606130567371367954905487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4283014846323647879747965 1606130567371367954905487)
          ·
            refine ⟨2409195851057051932358231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1606130567371367954905487 2409195851057051932358231)
            ·
              refine ⟨3613793776585577898537347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2409195851057051932358231 3613793776585577898537347)
              ·
                refine ⟨5420690664878366847806021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3613793776585577898537347 5420690664878366847806021)
                ·
                  refine ⟨1016379499664693783963629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5420690664878366847806021 1016379499664693783963629)
                  ·
                    refine ⟨381142312374260168986361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1016379499664693783963629 381142312374260168986361)
                    ·
                      refine ⟨285856734280695126739771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 381142312374260168986361 285856734280695126739771)
                      ·
                        rfl

theorem cell23_556704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_556704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556704 prefixEnd_556704 := by exact prefixLift 556704
  have htrace : WordTrace (prefixWord ++ tailWord_556704) baseStart_556704 baseEnd_556704 := by
    simpa [prefixWord, tailWord_556704, baseEnd_556704] using wordTrace_append hprefix tailTrace_556704
  have hstable : (prefixWord ++ tailWord_556704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556704).length < 2 ^ (prefixWord ++ tailWord_556704).sum := by decide
  have hdescent : baseEnd_556704 < baseStart_556704 := by decide
  rcases family_descends (prefixWord ++ tailWord_556704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556718 : List Nat := [4, 1, 4, 1, 2, 2, 2, 1, 6]
def baseStart_556718 : Nat := 118140960795 + 556718 * 2 ^ 59
def prefixEnd_556718 : Nat := 4983230072969 + 3 ^ 40 * 556718 * 2
def baseEnd_556718 : Nat := 31762658112206452440523

theorem tailTrace_556718 : CollatzResearch.WordTrace tailWord_556718 prefixEnd_556718 31762658112206452440523 := by
  unfold tailWord_556718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2538146699639155088726851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13536782398075493806543205 2538146699639155088726851)
  ·
    refine ⟨3807220049458732633090277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2538146699639155088726851 3807220049458732633090277)
    ·
      refine ⟨713853759273512368704427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3807220049458732633090277 713853759273512368704427)
      ·
        refine ⟨1070780638910268553056641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713853759273512368704427 1070780638910268553056641)
        ·
          refine ⟨803085479182701414792481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1070780638910268553056641 803085479182701414792481)
          ·
            refine ⟨602314109387026061094361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 803085479182701414792481 602314109387026061094361)
            ·
              refine ⟨451735582040269545820771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602314109387026061094361 451735582040269545820771)
              ·
                refine ⟨677603373060404318731157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451735582040269545820771 677603373060404318731157)
                ·
                  refine ⟨31762658112206452440523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 677603373060404318731157 31762658112206452440523)
                  ·
                    rfl

theorem cell23_556718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_556718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556718 prefixEnd_556718 := by exact prefixLift 556718
  have htrace : WordTrace (prefixWord ++ tailWord_556718) baseStart_556718 baseEnd_556718 := by
    simpa [prefixWord, tailWord_556718, baseEnd_556718] using wordTrace_append hprefix tailTrace_556718
  have hstable : (prefixWord ++ tailWord_556718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556718).length < 2 ^ (prefixWord ++ tailWord_556718).sum := by decide
  have hdescent : baseEnd_556718 < baseStart_556718 := by decide
  rcases family_descends (prefixWord ++ tailWord_556718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556734 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_556734 : Nat := 118140960795 + 556734 * 2 ^ 59
def prefixEnd_556734 : Nat := 4983230072969 + 3 ^ 40 * 556734 * 2
def baseEnd_556734 : Nat := 285872138700330009364633

theorem tailTrace_556734 : CollatzResearch.WordTrace tailWord_556734 prefixEnd_556734 285872138700330009364633 := by
  unfold tailWord_556734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2538219645631909430299657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13537171443370183628264837 2538219645631909430299657)
  ·
    refine ⟨1903664734223932072724743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2538219645631909430299657 1903664734223932072724743)
    ·
      refine ⟨2855497101335898109087115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1903664734223932072724743 2855497101335898109087115)
      ·
        refine ⟨4283245652003847163630673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2855497101335898109087115 4283245652003847163630673)
        ·
          refine ⟨3212434239002885372723005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4283245652003847163630673 3212434239002885372723005)
          ·
            refine ⟨1204662839626082014771127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3212434239002885372723005 1204662839626082014771127)
            ·
              refine ⟨1806994259439123022156691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204662839626082014771127 1806994259439123022156691)
              ·
                refine ⟨2710491389158684533235037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806994259439123022156691 2710491389158684533235037)
                ·
                  refine ⟨1016434270934506699963139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2710491389158684533235037 1016434270934506699963139)
                  ·
                    refine ⟨1524651406401760049944709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1016434270934506699963139 1524651406401760049944709)
                    ·
                      refine ⟨285872138700330009364633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1524651406401760049944709 285872138700330009364633)
                      ·
                        rfl

theorem cell23_556734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_556734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556734 prefixEnd_556734 := by exact prefixLift 556734
  have htrace : WordTrace (prefixWord ++ tailWord_556734) baseStart_556734 baseEnd_556734 := by
    simpa [prefixWord, tailWord_556734, baseEnd_556734] using wordTrace_append hprefix tailTrace_556734
  have hstable : (prefixWord ++ tailWord_556734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556734).length < 2 ^ (prefixWord ++ tailWord_556734).sum := by decide
  have hdescent : baseEnd_556734 < baseStart_556734 := by decide
  rcases family_descends (prefixWord ++ tailWord_556734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556754 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_556754 : Nat := 118140960795 + 556754 * 2 ^ 59
def prefixEnd_556754 : Nat := 4983230072969 + 3 ^ 40 * 556754 * 2
def baseEnd_556754 : Nat := 285882408313419931114541

theorem tailTrace_556754 : CollatzResearch.WordTrace tailWord_556754 prefixEnd_556754 285882408313419931114541 := by
  unfold tailWord_556754
  simp only [CollatzResearch.WordTrace]
  refine ⟨5076621656245704714531329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13537657749988545905416877 5076621656245704714531329)
  ·
    refine ⟨3807466242184278535898497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5076621656245704714531329 3807466242184278535898497)
    ·
      refine ⟨2855599681638208901923873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3807466242184278535898497 2855599681638208901923873)
      ·
        refine ⟨2141699761228656676442905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2855599681638208901923873 2141699761228656676442905)
        ·
          refine ⟨1606274820921492507332179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2141699761228656676442905 1606274820921492507332179)
          ·
            refine ⟨2409412231382238760998269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1606274820921492507332179 2409412231382238760998269)
            ·
              refine ⟨903529586768339535374351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2409412231382238760998269 903529586768339535374351)
              ·
                refine ⟨1355294380152509303061527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903529586768339535374351 1355294380152509303061527)
                ·
                  refine ⟨2032941570228763954592291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1355294380152509303061527 2032941570228763954592291)
                  ·
                    refine ⟨3049412355343145931888437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2032941570228763954592291 3049412355343145931888437)
                    ·
                      refine ⟨285882408313419931114541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3049412355343145931888437 285882408313419931114541)
                      ·
                        rfl

theorem cell23_556754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_556754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556754 prefixEnd_556754 := by exact prefixLift 556754
  have htrace : WordTrace (prefixWord ++ tailWord_556754) baseStart_556754 baseEnd_556754 := by
    simpa [prefixWord, tailWord_556754, baseEnd_556754] using wordTrace_append hprefix tailTrace_556754
  have hstable : (prefixWord ++ tailWord_556754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556754).length < 2 ^ (prefixWord ++ tailWord_556754).sum := by decide
  have hdescent : baseEnd_556754 < baseStart_556754 := by decide
  rcases family_descends (prefixWord ++ tailWord_556754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556767 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 3]
def baseStart_556767 : Nat := 118140960795 + 556767 * 2 ^ 59
def prefixEnd_556767 : Nat := 4983230072969 + 3 ^ 40 * 556767 * 2
def baseEnd_556767 : Nat := 285889083561928380251981

theorem tailTrace_556767 : CollatzResearch.WordTrace tailWord_556767 prefixEnd_556767 285889083561928380251981 := by
  unfold tailWord_556767
  simp only [CollatzResearch.WordTrace]
  refine ⟨20306960773935722078348555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13537973849290481385565703 20306960773935722078348555)
  ·
    refine ⟨30460441160903583117522833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20306960773935722078348555 30460441160903583117522833)
    ·
      refine ⟨22845330870677687338142125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30460441160903583117522833 22845330870677687338142125)
      ·
        refine ⟨8566999076504132751803297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22845330870677687338142125 8566999076504132751803297)
        ·
          refine ⟨6425249307378099563852473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8566999076504132751803297 6425249307378099563852473)
          ·
            refine ⟨4818936980533574672889355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6425249307378099563852473 4818936980533574672889355)
            ·
              refine ⟨7228405470800362009334033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4818936980533574672889355 7228405470800362009334033)
              ·
                refine ⟨5421304103100271507000525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7228405470800362009334033 5421304103100271507000525)
                ·
                  refine ⟨2032989038662601815125197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5421304103100271507000525 2032989038662601815125197)
                  ·
                    refine ⟨762370889498475680671949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2032989038662601815125197 762370889498475680671949)
                    ·
                      refine ⟨285889083561928380251981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 762370889498475680671949 285889083561928380251981)
                      ·
                        rfl

theorem cell23_556767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_556767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556767 prefixEnd_556767 := by exact prefixLift 556767
  have htrace : WordTrace (prefixWord ++ tailWord_556767) baseStart_556767 baseEnd_556767 := by
    simpa [prefixWord, tailWord_556767, baseEnd_556767] using wordTrace_append hprefix tailTrace_556767
  have hstable : (prefixWord ++ tailWord_556767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556767).length < 2 ^ (prefixWord ++ tailWord_556767).sum := by decide
  have hdescent : baseEnd_556767 < baseStart_556767 := by decide
  rcases family_descends (prefixWord ++ tailWord_556767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556788 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_556788 : Nat := 118140960795 + 556788 * 2 ^ 59
def prefixEnd_556788 : Nat := 4983230072969 + 3 ^ 40 * 556788 * 2
def baseEnd_556788 : Nat := 285899866655672798089385

theorem tailTrace_556788 : CollatzResearch.WordTrace tailWord_556788 prefixEnd_556788 285899866655672798089385 := by
  unfold tailWord_556788
  simp only [CollatzResearch.WordTrace]
  refine ⟨10153863353429821332431509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13538484471239761776575345 10153863353429821332431509)
  ·
    refine ⟨475962344692022874957727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10153863353429821332431509 475962344692022874957727)
    ·
      refine ⟨713943517038034312436591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 475962344692022874957727 713943517038034312436591)
      ·
        refine ⟨1070915275557051468654887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713943517038034312436591 1070915275557051468654887)
        ·
          refine ⟨1606372913335577202982331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070915275557051468654887 1606372913335577202982331)
          ·
            refine ⟨2409559370003365804473497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1606372913335577202982331 2409559370003365804473497)
            ·
              refine ⟨1807169527502524353355123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2409559370003365804473497 1807169527502524353355123)
              ·
                refine ⟨2710754291253786530032685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807169527502524353355123 2710754291253786530032685)
                ·
                  refine ⟨1016532859220169948762257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2710754291253786530032685 1016532859220169948762257)
                  ·
                    refine ⟨762399644415127461571693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1016532859220169948762257 762399644415127461571693)
                    ·
                      refine ⟨285899866655672798089385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 762399644415127461571693 285899866655672798089385)
                      ·
                        rfl

theorem cell23_556788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_556788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556788 prefixEnd_556788 := by exact prefixLift 556788
  have htrace : WordTrace (prefixWord ++ tailWord_556788) baseStart_556788 baseEnd_556788 := by
    simpa [prefixWord, tailWord_556788, baseEnd_556788] using wordTrace_append hprefix tailTrace_556788
  have hstable : (prefixWord ++ tailWord_556788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556788).length < 2 ^ (prefixWord ++ tailWord_556788).sum := by decide
  have hdescent : baseEnd_556788 < baseStart_556788 := by decide
  rcases family_descends (prefixWord ++ tailWord_556788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556818 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_556818 : Nat := 118140960795 + 556818 * 2 ^ 59
def prefixEnd_556818 : Nat := 4983230072969 + 3 ^ 40 * 556818 * 2
def baseEnd_556818 : Nat := 285915271075307680714247

theorem tailTrace_556818 : CollatzResearch.WordTrace tailWord_556818 prefixEnd_556818 285915271075307680714247 := by
  unfold tailWord_556818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5077205224187739447113777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13539213931167305192303405 5077205224187739447113777)
  ·
    refine ⟨3807903918140804585335333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5077205224187739447113777 3807903918140804585335333)
    ·
      refine ⟨713981984651400859750375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3807903918140804585335333 713981984651400859750375)
      ·
        refine ⟨1070972976977101289625563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713981984651400859750375 1070972976977101289625563)
        ·
          refine ⟨1606459465465651934438345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070972976977101289625563 1606459465465651934438345)
          ·
            refine ⟨1204844599099238950828759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1606459465465651934438345 1204844599099238950828759)
            ·
              refine ⟨1807266898648858426243139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204844599099238950828759 1807266898648858426243139)
              ·
                refine ⟨2710900347973287639364709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807266898648858426243139 2710900347973287639364709)
                ·
                  refine ⟨508293815244991432380883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2710900347973287639364709 508293815244991432380883)
                  ·
                    refine ⟨762440722867487148571325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 508293815244991432380883 762440722867487148571325)
                    ·
                      refine ⟨285915271075307680714247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 762440722867487148571325 285915271075307680714247)
                      ·
                        rfl

theorem cell23_556818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_556818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556818 prefixEnd_556818 := by exact prefixLift 556818
  have htrace : WordTrace (prefixWord ++ tailWord_556818) baseStart_556818 baseEnd_556818 := by
    simpa [prefixWord, tailWord_556818, baseEnd_556818] using wordTrace_append hprefix tailTrace_556818
  have hstable : (prefixWord ++ tailWord_556818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556818).length < 2 ^ (prefixWord ++ tailWord_556818).sum := by decide
  have hdescent : baseEnd_556818 < baseStart_556818 := by decide
  rcases family_descends (prefixWord ++ tailWord_556818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556824 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 3, 4, 2]
def baseStart_556824 : Nat := 118140960795 + 556824 * 2 ^ 59
def prefixEnd_556824 : Nat := 4983230072969 + 3 ^ 40 * 556824 * 2
def baseEnd_556824 : Nat := 285918351959234657239219

theorem tailTrace_556824 : CollatzResearch.WordTrace tailWord_556824 prefixEnd_556824 285918351959234657239219 := by
  unfold tailWord_556824
  simp only [CollatzResearch.WordTrace]
  refine ⟨10154519867364610406586763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13539359823152813875449017 10154519867364610406586763)
  ·
    refine ⟨15231779801046915609880145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10154519867364610406586763 15231779801046915609880145)
    ·
      refine ⟨11423834850785186707410109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15231779801046915609880145 11423834850785186707410109)
      ·
        refine ⟨4283938069044445015278791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11423834850785186707410109 4283938069044445015278791)
        ·
          refine ⟨6425907103566667522918187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4283938069044445015278791 6425907103566667522918187)
          ·
            refine ⟨9638860655350001284377281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6425907103566667522918187 9638860655350001284377281)
            ·
              refine ⟨7229145491512500963282961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9638860655350001284377281 7229145491512500963282961)
              ·
                refine ⟨5421859118634375722462221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7229145491512500963282961 5421859118634375722462221)
                ·
                  refine ⟨2033197169487890895923333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5421859118634375722462221 2033197169487890895923333)
                  ·
                    refine ⟨381224469278979542985625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2033197169487890895923333 381224469278979542985625)
                    ·
                      refine ⟨285918351959234657239219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 381224469278979542985625 285918351959234657239219)
                      ·
                        rfl

theorem cell23_556824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_556824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556824 prefixEnd_556824 := by exact prefixLift 556824
  have htrace : WordTrace (prefixWord ++ tailWord_556824) baseStart_556824 baseEnd_556824 := by
    simpa [prefixWord, tailWord_556824, baseEnd_556824] using wordTrace_append hprefix tailTrace_556824
  have hstable : (prefixWord ++ tailWord_556824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556824).length < 2 ^ (prefixWord ++ tailWord_556824).sum := by decide
  have hdescent : baseEnd_556824 < baseStart_556824 := by decide
  rcases family_descends (prefixWord ++ tailWord_556824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556927 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 6]
def baseStart_556927 : Nat := 118140960795 + 556927 * 2 ^ 59
def prefixEnd_556927 : Nat := 4983230072969 + 3 ^ 40 * 556927 * 2
def baseEnd_556927 : Nat := 285971240466647754251245

theorem tailTrace_556927 : CollatzResearch.WordTrace tailWord_556927 prefixEnd_556927 285971240466647754251245 := by
  unfold tailWord_556927
  simp only [CollatzResearch.WordTrace]
  refine ⟨20312796453356069404173035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13541864302237379602782023 20312796453356069404173035)
  ·
    refine ⟨30469194680034104106259553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20312796453356069404173035 30469194680034104106259553)
    ·
      refine ⟨22851896010025578079694665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30469194680034104106259553 22851896010025578079694665)
      ·
        refine ⟨17138922007519183559770999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22851896010025578079694665 17138922007519183559770999)
        ·
          refine ⟨25708383011278775339656499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17138922007519183559770999 25708383011278775339656499)
          ·
            refine ⟨38562574516918163009484749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25708383011278775339656499 38562574516918163009484749)
            ·
              refine ⟨14460965443844311128556781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38562574516918163009484749 14460965443844311128556781)
              ·
                refine ⟨5422862041441616673208793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14460965443844311128556781 5422862041441616673208793)
                ·
                  refine ⟨4067146531081212504906595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5422862041441616673208793 4067146531081212504906595)
                  ·
                    refine ⟨6100719796621818757359893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4067146531081212504906595 6100719796621818757359893)
                    ·
                      refine ⟨285971240466647754251245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6100719796621818757359893 285971240466647754251245)
                      ·
                        rfl

theorem cell23_556927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_556927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556927 prefixEnd_556927 := by exact prefixLift 556927
  have htrace : WordTrace (prefixWord ++ tailWord_556927) baseStart_556927 baseEnd_556927 := by
    simpa [prefixWord, tailWord_556927, baseEnd_556927] using wordTrace_append hprefix tailTrace_556927
  have hstable : (prefixWord ++ tailWord_556927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556927).length < 2 ^ (prefixWord ++ tailWord_556927).sum := by decide
  have hdescent : baseEnd_556927 < baseStart_556927 := by decide
  rcases family_descends (prefixWord ++ tailWord_556927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556948 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_556948 : Nat := 118140960795 + 556948 * 2 ^ 59
def prefixEnd_556948 : Nat := 4983230072969 + 3 ^ 40 * 556948 * 2
def baseEnd_556948 : Nat := 285982023560392172088649

theorem tailTrace_556948 : CollatzResearch.WordTrace tailWord_556948 prefixEnd_556948 285982023560392172088649 := by
  unfold tailWord_556948
  simp only [CollatzResearch.WordTrace]
  refine ⟨10156781193139994995343749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13542374924186659993791665 10156781193139994995343749)
  ·
    refine ⟨1904396473713749061626953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10156781193139994995343749 1904396473713749061626953)
    ·
      refine ⟨1428297355285311796220215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1904396473713749061626953 1428297355285311796220215)
      ·
        refine ⟨2142446032927967694330323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428297355285311796220215 2142446032927967694330323)
        ·
          refine ⟨3213669049391951541495485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2142446032927967694330323 3213669049391951541495485)
          ·
            refine ⟨1205125893521981828060807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3213669049391951541495485 1205125893521981828060807)
            ·
              refine ⟨1807688840282972742091211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205125893521981828060807 1807688840282972742091211)
              ·
                refine ⟨2711533260424459113136817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807688840282972742091211 2711533260424459113136817)
                ·
                  refine ⟨2033649945318344334852613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2711533260424459113136817 2033649945318344334852613)
                  ·
                    refine ⟨381309364747189562784865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2033649945318344334852613 381309364747189562784865)
                    ·
                      refine ⟨285982023560392172088649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 381309364747189562784865 285982023560392172088649)
                      ·
                        rfl

theorem cell23_556948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_556948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556948 prefixEnd_556948 := by exact prefixLift 556948
  have htrace : WordTrace (prefixWord ++ tailWord_556948) baseStart_556948 baseEnd_556948 := by
    simpa [prefixWord, tailWord_556948, baseEnd_556948] using wordTrace_append hprefix tailTrace_556948
  have hstable : (prefixWord ++ tailWord_556948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556948).length < 2 ^ (prefixWord ++ tailWord_556948).sum := by decide
  have hdescent : baseEnd_556948 < baseStart_556948 := by decide
  rcases family_descends (prefixWord ++ tailWord_556948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556991 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 4, 3, 2]
def baseStart_556991 : Nat := 118140960795 + 556991 * 2 ^ 59
def prefixEnd_556991 : Nat := 4983230072969 + 3 ^ 40 * 556991 * 2
def baseEnd_556991 : Nat := 286004103228535503850951

theorem tailTrace_556991 : CollatzResearch.WordTrace tailWord_556991 prefixEnd_556991 286004103228535503850951 := by
  unfold tailWord_556991
  simp only [CollatzResearch.WordTrace]
  refine ⟨20315130725124208334502827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13543420483416138889668551 20315130725124208334502827)
  ·
    refine ⟨30472696087686312501754241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20315130725124208334502827 30472696087686312501754241)
    ·
      refine ⟨22854522065764734376315681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30472696087686312501754241 22854522065764734376315681)
      ·
        refine ⟨17140891549323550782236761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22854522065764734376315681 17140891549323550782236761)
        ·
          refine ⟨12855668661992663086677571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17140891549323550782236761 12855668661992663086677571)
          ·
            refine ⟨19283502992988994630016357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12855668661992663086677571 19283502992988994630016357)
            ·
              refine ⟨3615656811185436493128067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19283502992988994630016357 3615656811185436493128067)
              ·
                refine ⟨5423485216778154739692101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3615656811185436493128067 5423485216778154739692101)
                ·
                  refine ⟨1016903478145904013692269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5423485216778154739692101 1016903478145904013692269)
                  ·
                    refine ⟨381338804304714005134601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1016903478145904013692269 381338804304714005134601)
                    ·
                      refine ⟨286004103228535503850951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 381338804304714005134601 286004103228535503850951)
                      ·
                        rfl

theorem cell23_556991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 3, 2].length) (baseStart_556991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_556991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_556991 prefixEnd_556991 := by exact prefixLift 556991
  have htrace : WordTrace (prefixWord ++ tailWord_556991) baseStart_556991 baseEnd_556991 := by
    simpa [prefixWord, tailWord_556991, baseEnd_556991] using wordTrace_append hprefix tailTrace_556991
  have hstable : (prefixWord ++ tailWord_556991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556991).length < 2 ^ (prefixWord ++ tailWord_556991).sum := by decide
  have hdescent : baseEnd_556991 < baseStart_556991 := by decide
  rcases family_descends (prefixWord ++ tailWord_556991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557018 : List Nat := [3, 1, 1, 2, 5, 1, 2, 2, 1, 5]
def baseStart_557018 : Nat := 118140960795 + 557018 * 2 ^ 59
def prefixEnd_557018 : Nat := 4983230072969 + 3 ^ 40 * 557018 * 2
def baseEnd_557018 : Nat := 95339322402068966071109

theorem tailTrace_557018 : CollatzResearch.WordTrace tailWord_557018 prefixEnd_557018 95339322402068966071109 := by
  unfold tailWord_557018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5079028874006597986433927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13544076997350927963823805 5079028874006597986433927)
  ·
    refine ⟨7618543311009896979650891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5079028874006597986433927 7618543311009896979650891)
    ·
      refine ⟨11427814966514845469476337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7618543311009896979650891 11427814966514845469476337)
      ·
        refine ⟨8570861224886134102107253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11427814966514845469476337 8570861224886134102107253)
        ·
          refine ⟨803518239833075072072555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8570861224886134102107253 803518239833075072072555)
          ·
            refine ⟨1205277359749612608108833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803518239833075072072555 1205277359749612608108833)
            ·
              refine ⟨903958019812209456081625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1205277359749612608108833 903958019812209456081625)
              ·
                refine ⟨677968514859157092061219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 903958019812209456081625 677968514859157092061219)
                ·
                  refine ⟨1016952772288735638091829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677968514859157092061219 1016952772288735638091829)
                  ·
                    refine ⟨95339322402068966071109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1016952772288735638091829 95339322402068966071109)
                    ·
                      rfl

theorem cell23_557018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_557018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557018 prefixEnd_557018 := by exact prefixLift 557018
  have htrace : WordTrace (prefixWord ++ tailWord_557018) baseStart_557018 baseEnd_557018 := by
    simpa [prefixWord, tailWord_557018, baseEnd_557018] using wordTrace_append hprefix tailTrace_557018
  have hstable : (prefixWord ++ tailWord_557018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557018).length < 2 ^ (prefixWord ++ tailWord_557018).sum := by decide
  have hdescent : baseEnd_557018 < baseStart_557018 := by decide
  rcases family_descends (prefixWord ++ tailWord_557018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557024 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 3]
def baseStart_557024 : Nat := 118140960795 + 557024 * 2 ^ 59
def prefixEnd_557024 : Nat := 4983230072969 + 3 ^ 40 * 557024 * 2
def baseEnd_557024 : Nat := 286021048090133874738299

theorem tailTrace_557024 : CollatzResearch.WordTrace tailWord_557024 prefixEnd_557024 286021048090133874738299 := by
  unfold tailWord_557024
  simp only [CollatzResearch.WordTrace]
  refine ⟨10158167167002327485227063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13544222889336436646969417 10158167167002327485227063)
  ·
    refine ⟨15237250750503491227840595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10158167167002327485227063 15237250750503491227840595)
    ·
      refine ⟨22855876125755236841760893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15237250750503491227840595 22855876125755236841760893)
      ·
        refine ⟨8570953547158213815660335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22855876125755236841760893 8570953547158213815660335)
        ·
          refine ⟨12856430320737320723490503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8570953547158213815660335 12856430320737320723490503)
          ·
            refine ⟨19284645481105981085235755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12856430320737320723490503 19284645481105981085235755)
            ·
              refine ⟨28926968221658971627853633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19284645481105981085235755 28926968221658971627853633)
              ·
                refine ⟨21695226166244228720890225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28926968221658971627853633 21695226166244228720890225)
                ·
                  refine ⟨16271419624683171540667669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21695226166244228720890225 16271419624683171540667669)
                  ·
                    refine ⟨762722794907023665968797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16271419624683171540667669 762722794907023665968797)
                    ·
                      refine ⟨286021048090133874738299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 762722794907023665968797 286021048090133874738299)
                      ·
                        rfl

theorem cell23_557024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_557024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557024 prefixEnd_557024 := by exact prefixLift 557024
  have htrace : WordTrace (prefixWord ++ tailWord_557024) baseStart_557024 baseEnd_557024 := by
    simpa [prefixWord, tailWord_557024, baseEnd_557024] using wordTrace_append hprefix tailTrace_557024
  have hstable : (prefixWord ++ tailWord_557024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557024).length < 2 ^ (prefixWord ++ tailWord_557024).sum := by decide
  have hdescent : baseEnd_557024 < baseStart_557024 := by decide
  rcases family_descends (prefixWord ++ tailWord_557024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557038 : List Nat := [4, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_557038 : Nat := 118140960795 + 557038 * 2 ^ 59
def prefixEnd_557038 : Nat := 4983230072969 + 3 ^ 40 * 557038 * 2
def baseEnd_557038 : Nat := 286028236819296819963235

theorem tailTrace_557038 : CollatzResearch.WordTrace tailWord_557038 prefixEnd_557038 286028236819296819963235 := by
  unfold tailWord_557038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2539605619494241920182971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13544563303969290240975845 2539605619494241920182971)
  ·
    refine ⟨3809408429241362880274457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2539605619494241920182971 3809408429241362880274457)
    ·
      refine ⟨2857056321931022160205843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3809408429241362880274457 2857056321931022160205843)
      ·
        refine ⟨4285584482896533240308765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2857056321931022160205843 4285584482896533240308765)
        ·
          refine ⟨1607094181086199965115787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4285584482896533240308765 1607094181086199965115787)
          ·
            refine ⟨2410641271629299947673681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607094181086199965115787 2410641271629299947673681)
            ·
              refine ⟨1807980953721974960755261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2410641271629299947673681 1807980953721974960755261)
              ·
                refine ⟨677992857645740610283223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1807980953721974960755261 677992857645740610283223)
                ·
                  refine ⟨1016989286468610915424835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677992857645740610283223 1016989286468610915424835)
                  ·
                    refine ⟨1525483929702916373137253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1016989286468610915424835 1525483929702916373137253)
                    ·
                      refine ⟨286028236819296819963235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1525483929702916373137253 286028236819296819963235)
                      ·
                        rfl

theorem cell23_557038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_557038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557038 prefixEnd_557038 := by exact prefixLift 557038
  have htrace : WordTrace (prefixWord ++ tailWord_557038) baseStart_557038 baseEnd_557038 := by
    simpa [prefixWord, tailWord_557038, baseEnd_557038] using wordTrace_append hprefix tailTrace_557038
  have hstable : (prefixWord ++ tailWord_557038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557038).length < 2 ^ (prefixWord ++ tailWord_557038).sum := by decide
  have hdescent : baseEnd_557038 < baseStart_557038 := by decide
  rcases family_descends (prefixWord ++ tailWord_557038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557055 : List Nat := [1, 1, 2, 2, 1, 2, 1, 8, 1, 2, 2]
def baseStart_557055 : Nat := 118140960795 + 557055 * 2 ^ 59
def prefixEnd_557055 : Nat := 4983230072969 + 3 ^ 40 * 557055 * 2
def baseEnd_557055 : Nat := 286036965990423253450657

theorem tailTrace_557055 : CollatzResearch.WordTrace tailWord_557055 prefixEnd_557055 286036965990423253450657 := by
  unfold tailWord_557055
  simp only [CollatzResearch.WordTrace]
  refine ⟨20317464996892347264832619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13544976664594898176555079 20317464996892347264832619)
  ·
    refine ⟨30476197495338520897248929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20317464996892347264832619 30476197495338520897248929)
    ·
      refine ⟨22857148121503890672936697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30476197495338520897248929 22857148121503890672936697)
      ·
        refine ⟨17142861091127918004702523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22857148121503890672936697 17142861091127918004702523)
        ·
          refine ⟨25714291636691877007053785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17142861091127918004702523 25714291636691877007053785)
          ·
            refine ⟨19285718727518907755290339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25714291636691877007053785 19285718727518907755290339)
            ·
              refine ⟨28928578091278361632935509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19285718727518907755290339 28928578091278361632935509)
              ·
                refine ⟨339006774507168300385963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 28928578091278361632935509 339006774507168300385963)
                ·
                  refine ⟨508510161760752450578945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339006774507168300385963 508510161760752450578945)
                  ·
                    refine ⟨381382621320564337934209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 508510161760752450578945 381382621320564337934209)
                    ·
                      refine ⟨286036965990423253450657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 381382621320564337934209 286036965990423253450657)
                      ·
                        rfl

theorem cell23_557055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 1, 2, 2].length) (baseStart_557055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557055 prefixEnd_557055 := by exact prefixLift 557055
  have htrace : WordTrace (prefixWord ++ tailWord_557055) baseStart_557055 baseEnd_557055 := by
    simpa [prefixWord, tailWord_557055, baseEnd_557055] using wordTrace_append hprefix tailTrace_557055
  have hstable : (prefixWord ++ tailWord_557055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557055).length < 2 ^ (prefixWord ++ tailWord_557055).sum := by decide
  have hdescent : baseEnd_557055 < baseStart_557055 := by decide
  rcases family_descends (prefixWord ++ tailWord_557055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557064 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_557064 : Nat := 118140960795 + 557064 * 2 ^ 59
def prefixEnd_557064 : Nat := 4983230072969 + 3 ^ 40 * 557064 * 2
def baseEnd_557064 : Nat := 286041587316313718238115

theorem tailTrace_557064 : CollatzResearch.WordTrace tailWord_557064 prefixEnd_557064 286041587316313718238115 := by
  unfold tailWord_557064
  simp only [CollatzResearch.WordTrace]
  refine ⟨10158896626929870900955123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13545195502573161201273497 10158896626929870900955123)
  ·
    refine ⟨15238344940394806351432685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10158896626929870900955123 15238344940394806351432685)
    ·
      refine ⟨5714379352648052381787257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15238344940394806351432685 5714379352648052381787257)
      ·
        refine ⟨4285784514486039286340443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5714379352648052381787257 4285784514486039286340443)
        ·
          refine ⟨6428676771729058929510665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4285784514486039286340443 6428676771729058929510665)
          ·
            refine ⟨4821507578796794197132999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6428676771729058929510665 4821507578796794197132999)
            ·
              refine ⟨7232261368195191295699499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4821507578796794197132999 7232261368195191295699499)
              ·
                refine ⟨10848392052292786943549249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7232261368195191295699499 10848392052292786943549249)
                ·
                  refine ⟨8136294039219590207661937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10848392052292786943549249 8136294039219590207661937)
                  ·
                    refine ⟨6102220529414692655746453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8136294039219590207661937 6102220529414692655746453)
                    ·
                      refine ⟨286041587316313718238115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6102220529414692655746453 286041587316313718238115)
                      ·
                        rfl

theorem cell23_557064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_557064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557064 prefixEnd_557064 := by exact prefixLift 557064
  have htrace : WordTrace (prefixWord ++ tailWord_557064) baseStart_557064 baseEnd_557064 := by
    simpa [prefixWord, tailWord_557064, baseEnd_557064] using wordTrace_append hprefix tailTrace_557064
  have hstable : (prefixWord ++ tailWord_557064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557064).length < 2 ^ (prefixWord ++ tailWord_557064).sum := by decide
  have hdescent : baseEnd_557064 < baseStart_557064 := by decide
  rcases family_descends (prefixWord ++ tailWord_557064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557069 : List Nat := [1, 7, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_557069 : Nat := 118140960795 + 557069 * 2 ^ 59
def prefixEnd_557069 : Nat := 4983230072969 + 3 ^ 40 * 557069 * 2
def baseEnd_557069 : Nat := 95348051573195399558531

theorem tailTrace_557069 : CollatzResearch.WordTrace tailWord_557069 prefixEnd_557069 95348051573195399558531 := by
  unfold tailWord_557069
  simp only [CollatzResearch.WordTrace]
  refine ⟨20317975618841627655842261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13545317079227751770561507 20317975618841627655842261)
  ·
    refine ⟨476202553566600648183803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 20317975618841627655842261 476202553566600648183803)
    ·
      refine ⟨714303830349900972275705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476202553566600648183803 714303830349900972275705)
      ·
        refine ⟨535727872762425729206779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 714303830349900972275705 535727872762425729206779)
        ·
          refine ⟨803591809143638593810169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535727872762425729206779 803591809143638593810169)
          ·
            refine ⟨602693856857728945357627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 803591809143638593810169 602693856857728945357627)
            ·
              refine ⟨904040785286593418036441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602693856857728945357627 904040785286593418036441)
              ·
                refine ⟨678030588964945063527331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904040785286593418036441 678030588964945063527331)
                ·
                  refine ⟨1017045883447417595290997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678030588964945063527331 1017045883447417595290997)
                  ·
                    refine ⟨95348051573195399558531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1017045883447417595290997 95348051573195399558531)
                    ·
                      rfl

theorem cell23_557069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_557069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557069 prefixEnd_557069 := by exact prefixLift 557069
  have htrace : WordTrace (prefixWord ++ tailWord_557069) baseStart_557069 baseEnd_557069 := by
    simpa [prefixWord, tailWord_557069, baseEnd_557069] using wordTrace_append hprefix tailTrace_557069
  have hstable : (prefixWord ++ tailWord_557069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557069).length < 2 ^ (prefixWord ++ tailWord_557069).sum := by decide
  have hdescent : baseEnd_557069 < baseStart_557069 := by decide
  rcases family_descends (prefixWord ++ tailWord_557069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557092 : List Nat := [2, 3, 1, 4, 2, 1, 3, 1, 1, 2, 3]
def baseStart_557092 : Nat := 118140960795 + 557092 * 2 ^ 59
def prefixEnd_557092 : Nat := 4983230072969 + 3 ^ 40 * 557092 * 2
def baseEnd_557092 : Nat := 286055964774639608687987

theorem tailTrace_557092 : CollatzResearch.WordTrace tailWord_557092 prefixEnd_557092 286055964774639608687987 := by
  unfold tailWord_557092
  simp only [CollatzResearch.WordTrace]
  refine ⟨10159407248879151291964765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13545876331838868389286353 10159407248879151291964765)
  ·
    refine ⟨3809777718329681734486787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10159407248879151291964765 3809777718329681734486787)
    ·
      refine ⟨5714666577494522601730181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3809777718329681734486787 5714666577494522601730181)
      ·
        refine ⟨1071499983280222987824409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5714666577494522601730181 1071499983280222987824409)
        ·
          refine ⟨803624987460167240868307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1071499983280222987824409 803624987460167240868307)
          ·
            refine ⟨1205437481190250861302461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803624987460167240868307 1205437481190250861302461)
            ·
              refine ⟨452039055446344072988423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1205437481190250861302461 452039055446344072988423)
              ·
                refine ⟨678058583169516109482635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452039055446344072988423 678058583169516109482635)
                ·
                  refine ⟨1017087874754274164223953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678058583169516109482635 1017087874754274164223953)
                  ·
                    refine ⟨762815906065705623167965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1017087874754274164223953 762815906065705623167965)
                    ·
                      refine ⟨286055964774639608687987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 762815906065705623167965 286055964774639608687987)
                      ·
                        rfl

theorem cell23_557092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_557092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557092 prefixEnd_557092 := by exact prefixLift 557092
  have htrace : WordTrace (prefixWord ++ tailWord_557092) baseStart_557092 baseEnd_557092 := by
    simpa [prefixWord, tailWord_557092, baseEnd_557092] using wordTrace_append hprefix tailTrace_557092
  have hstable : (prefixWord ++ tailWord_557092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557092).length < 2 ^ (prefixWord ++ tailWord_557092).sum := by decide
  have hdescent : baseEnd_557092 < baseStart_557092 := by decide
  rcases family_descends (prefixWord ++ tailWord_557092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557105 : List Nat := [1, 2, 2, 3, 1, 4, 2, 2, 2, 1, 3]
def baseStart_557105 : Nat := 118140960795 + 557105 * 2 ^ 59
def prefixEnd_557105 : Nat := 4983230072969 + 3 ^ 40 * 557105 * 2
def baseEnd_557105 : Nat := 286062640023148057825427

theorem tailTrace_557105 : CollatzResearch.WordTrace tailWord_557105 prefixEnd_557105 286062640023148057825427 := by
  unfold tailWord_557105
  simp only [CollatzResearch.WordTrace]
  refine ⟨20319288646711205804152769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13546192431140803869435179 20319288646711205804152769)
  ·
    refine ⟨15239466485033404353114577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20319288646711205804152769 15239466485033404353114577)
    ·
      refine ⟨11429599863775053264835933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15239466485033404353114577 11429599863775053264835933)
      ·
        refine ⟨4286099948915644974313475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11429599863775053264835933 4286099948915644974313475)
        ·
          refine ⟨6429149923373467461470213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4286099948915644974313475 6429149923373467461470213)
          ·
            refine ⟨1205465610632525149025665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6429149923373467461470213 1205465610632525149025665)
            ·
              refine ⟨904099207974393861769249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1205465610632525149025665 904099207974393861769249)
              ·
                refine ⟨678074405980795396326937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904099207974393861769249 678074405980795396326937)
                ·
                  refine ⟨508555804485596547245203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 678074405980795396326937 508555804485596547245203)
                  ·
                    refine ⟨762833706728394820867805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 508555804485596547245203 762833706728394820867805)
                    ·
                      refine ⟨286062640023148057825427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 762833706728394820867805 286062640023148057825427)
                      ·
                        rfl

theorem cell23_557105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_557105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557105 prefixEnd_557105 := by exact prefixLift 557105
  have htrace : WordTrace (prefixWord ++ tailWord_557105) baseStart_557105 baseEnd_557105 := by
    simpa [prefixWord, tailWord_557105, baseEnd_557105] using wordTrace_append hprefix tailTrace_557105
  have hstable : (prefixWord ++ tailWord_557105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557105).length < 2 ^ (prefixWord ++ tailWord_557105).sum := by decide
  have hdescent : baseEnd_557105 < baseStart_557105 := by decide
  rcases family_descends (prefixWord ++ tailWord_557105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557121 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 1, 8]
def baseStart_557121 : Nat := 118140960795 + 557121 * 2 ^ 59
def prefixEnd_557121 : Nat := 4983230072969 + 3 ^ 40 * 557121 * 2
def baseEnd_557121 : Nat := 95356951904539998408451

theorem tailTrace_557121 : CollatzResearch.WordTrace tailWord_557121 prefixEnd_557121 95356951904539998408451 := by
  unfold tailWord_557121
  simp only [CollatzResearch.WordTrace]
  refine ⟨20319872214653240536735217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13546581476435493691156811 20319872214653240536735217)
  ·
    refine ⟨15239904160989930402551413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20319872214653240536735217 15239904160989930402551413)
    ·
      refine ⟨1428741015092805975239195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15239904160989930402551413 1428741015092805975239195)
      ·
        refine ⟨2143111522639208962858793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428741015092805975239195 2143111522639208962858793)
        ·
          refine ⟨1607333641979406722144095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2143111522639208962858793 1607333641979406722144095)
          ·
            refine ⟨2411000462969110083216143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607333641979406722144095 2411000462969110083216143)
            ·
              refine ⟨3616500694453665124824215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411000462969110083216143 3616500694453665124824215)
              ·
                refine ⟨5424751041680497687236323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3616500694453665124824215 5424751041680497687236323)
                ·
                  refine ⟨8137126562520746530854485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5424751041680497687236323 8137126562520746530854485)
                  ·
                    refine ⟨95356951904539998408451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8137126562520746530854485 95356951904539998408451)
                    ·
                      rfl

theorem cell23_557121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_557121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557121 prefixEnd_557121 := by exact prefixLift 557121
  have htrace : WordTrace (prefixWord ++ tailWord_557121) baseStart_557121 baseEnd_557121 := by
    simpa [prefixWord, tailWord_557121, baseEnd_557121] using wordTrace_append hprefix tailTrace_557121
  have hstable : (prefixWord ++ tailWord_557121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557121).length < 2 ^ (prefixWord ++ tailWord_557121).sum := by decide
  have hdescent : baseEnd_557121 < baseStart_557121 := by decide
  rcases family_descends (prefixWord ++ tailWord_557121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557149 : List Nat := [1, 4, 4, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_557149 : Nat := 118140960795 + 557149 * 2 ^ 59
def prefixEnd_557149 : Nat := 4983230072969 + 3 ^ 40 * 557149 * 2
def baseEnd_557149 : Nat := 286085233171945885675225

theorem tailTrace_557149 : CollatzResearch.WordTrace tailWord_557149 prefixEnd_557149 286085233171945885675225 := by
  unfold tailWord_557149
  simp only [CollatzResearch.WordTrace]
  refine ⟨20320893458551801318754501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13547262305701200879169667 20320893458551801318754501)
  ·
    refine ⟨3810167523478462747266469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20320893458551801318754501 3810167523478462747266469)
    ·
      refine ⟨714406410652211765112463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3810167523478462747266469 714406410652211765112463)
      ·
        refine ⟨1071609615978317647668695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 714406410652211765112463 1071609615978317647668695)
        ·
          refine ⟨1607414423967476471503043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071609615978317647668695 1607414423967476471503043)
          ·
            refine ⟨2411121635951214707254565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607414423967476471503043 2411121635951214707254565)
            ·
              refine ⟨452085306740852757610231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2411121635951214707254565 452085306740852757610231)
              ·
                refine ⟨678127960111279136415347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452085306740852757610231 678127960111279136415347)
                ·
                  refine ⟨1017191940166918704623021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678127960111279136415347 1017191940166918704623021)
                  ·
                    refine ⟨381446977562594514233633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1017191940166918704623021 381446977562594514233633)
                    ·
                      refine ⟨286085233171945885675225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 381446977562594514233633 286085233171945885675225)
                      ·
                        rfl

theorem cell23_557149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_557149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557149 prefixEnd_557149 := by exact prefixLift 557149
  have htrace : WordTrace (prefixWord ++ tailWord_557149) baseStart_557149 baseEnd_557149 := by
    simpa [prefixWord, tailWord_557149, baseEnd_557149] using wordTrace_append hprefix tailTrace_557149
  have hstable : (prefixWord ++ tailWord_557149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557149).length < 2 ^ (prefixWord ++ tailWord_557149).sum := by decide
  have hdescent : baseEnd_557149 < baseStart_557149 := by decide
  rcases family_descends (prefixWord ++ tailWord_557149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557161 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 4, 3, 3]
def baseStart_557161 : Nat := 118140960795 + 557161 * 2 ^ 59
def prefixEnd_557161 : Nat := 4983230072969 + 3 ^ 40 * 557161 * 2
def baseEnd_557161 : Nat := 286091394939799838725169

theorem tailTrace_557161 : CollatzResearch.WordTrace tailWord_557161 prefixEnd_557161 286091394939799838725169 := by
  unfold tailWord_557161
  simp only [CollatzResearch.WordTrace]
  refine ⟨20321331134508327368191337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13547554089672218245460891 20321331134508327368191337)
  ·
    refine ⟨15240998350881245526143503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20321331134508327368191337 15240998350881245526143503)
    ·
      refine ⟨22861497526321868289215255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15240998350881245526143503 22861497526321868289215255)
      ·
        refine ⟨34292246289482802433822883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22861497526321868289215255 34292246289482802433822883)
        ·
          refine ⟨51438369434224203650734325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34292246289482802433822883 51438369434224203650734325)
          ·
            refine ⟨4822347134458519092256343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51438369434224203650734325 4822347134458519092256343)
            ·
              refine ⟨7233520701687778638384515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4822347134458519092256343 7233520701687778638384515)
              ·
                refine ⟨10850281052531667957576773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7233520701687778638384515 10850281052531667957576773)
                ·
                  refine ⟨2034427697349687742045645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10850281052531667957576773 2034427697349687742045645)
                  ·
                    refine ⟨762910386506132903267117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2034427697349687742045645 762910386506132903267117)
                    ·
                      refine ⟨286091394939799838725169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 762910386506132903267117 286091394939799838725169)
                      ·
                        rfl

theorem cell23_557161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 3, 3].length) (baseStart_557161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557161 prefixEnd_557161 := by exact prefixLift 557161
  have htrace : WordTrace (prefixWord ++ tailWord_557161) baseStart_557161 baseEnd_557161 := by
    simpa [prefixWord, tailWord_557161, baseEnd_557161] using wordTrace_append hprefix tailTrace_557161
  have hstable : (prefixWord ++ tailWord_557161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557161).length < 2 ^ (prefixWord ++ tailWord_557161).sum := by decide
  have hdescent : baseEnd_557161 < baseStart_557161 := by decide
  rcases family_descends (prefixWord ++ tailWord_557161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557162 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_557162 : Nat := 118140960795 + 557162 * 2 ^ 59
def prefixEnd_557162 : Nat := 4983230072969 + 3 ^ 40 * 557162 * 2
def baseEnd_557162 : Nat := 286091908420454334812665

theorem tailTrace_557162 : CollatzResearch.WordTrace tailWord_557162 prefixEnd_557162 286091908420454334812665 := by
  unfold tailWord_557162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5080341901876176134744435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13547578405003136359318493 5080341901876176134744435)
  ·
    refine ⟨7620512852814264202116653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5080341901876176134744435 7620512852814264202116653)
    ·
      refine ⟨2857692319805349075793745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7620512852814264202116653 2857692319805349075793745)
      ·
        refine ⟨2143269239854011806845309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2857692319805349075793745 2143269239854011806845309)
        ·
          refine ⟨803725964945254427566991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2143269239854011806845309 803725964945254427566991)
          ·
            refine ⟨1205588947417881641350487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803725964945254427566991 1205588947417881641350487)
            ·
              refine ⟨1808383421126822462025731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205588947417881641350487 1808383421126822462025731)
              ·
                refine ⟨2712575131690233693038597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1808383421126822462025731 2712575131690233693038597)
                ·
                  refine ⟨508607837191918817444737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2712575131690233693038597 508607837191918817444737)
                  ·
                    refine ⟨381455877893939113083553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 508607837191918817444737 381455877893939113083553)
                    ·
                      refine ⟨286091908420454334812665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 381455877893939113083553 286091908420454334812665)
                      ·
                        rfl

theorem cell23_557162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_557162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557162 prefixEnd_557162 := by exact prefixLift 557162
  have htrace : WordTrace (prefixWord ++ tailWord_557162) baseStart_557162 baseEnd_557162 := by
    simpa [prefixWord, tailWord_557162, baseEnd_557162] using wordTrace_append hprefix tailTrace_557162
  have hstable : (prefixWord ++ tailWord_557162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557162).length < 2 ^ (prefixWord ++ tailWord_557162).sum := by decide
  have hdescent : baseEnd_557162 < baseStart_557162 := by decide
  rcases family_descends (prefixWord ++ tailWord_557162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557168 : List Nat := [2, 1, 1, 1, 5, 2, 2, 4, 5]
def baseStart_557168 : Nat := 118140960795 + 557168 * 2 ^ 59
def prefixEnd_557168 : Nat := 4983230072969 + 3 ^ 40 * 557168 * 2
def baseEnd_557168 : Nat := 31788332144931256815293

theorem tailTrace_557168 : CollatzResearch.WordTrace tailWord_557168 prefixEnd_557168 31788332144931256815293 := by
  unfold tailWord_557168
  simp only [CollatzResearch.WordTrace]
  refine ⟨10160793222741483781848079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13547724296988645042464105 10160793222741483781848079)
  ·
    refine ⟨15241189834112225672772119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10160793222741483781848079 15241189834112225672772119)
    ·
      refine ⟨22861784751168338509158179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15241189834112225672772119 22861784751168338509158179)
      ·
        refine ⟨34292677126752507763737269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22861784751168338509158179 34292677126752507763737269)
        ·
          refine ⟨3214938480633047602850369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34292677126752507763737269 3214938480633047602850369)
          ·
            refine ⟨2411203860474785702137777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3214938480633047602850369 2411203860474785702137777)
            ·
              refine ⟨1808402895356089276603333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2411203860474785702137777 1808402895356089276603333)
              ·
                refine ⟨339075542879266739363125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1808402895356089276603333 339075542879266739363125)
                ·
                  refine ⟨31788332144931256815293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 339075542879266739363125 31788332144931256815293)
                  ·
                    rfl

theorem cell23_557168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 5].length) (baseStart_557168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557168 prefixEnd_557168 := by exact prefixLift 557168
  have htrace : WordTrace (prefixWord ++ tailWord_557168) baseStart_557168 baseEnd_557168 := by
    simpa [prefixWord, tailWord_557168, baseEnd_557168] using wordTrace_append hprefix tailTrace_557168
  have hstable : (prefixWord ++ tailWord_557168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557168).length < 2 ^ (prefixWord ++ tailWord_557168).sum := by decide
  have hdescent : baseEnd_557168 < baseStart_557168 := by decide
  rcases family_descends (prefixWord ++ tailWord_557168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557181 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_557181 : Nat := 118140960795 + 557181 * 2 ^ 59
def prefixEnd_557181 : Nat := 4983230072969 + 3 ^ 40 * 557181 * 2
def baseEnd_557181 : Nat := 95367221517629920158359

theorem tailTrace_557181 : CollatzResearch.WordTrace tailWord_557181 prefixEnd_557181 95367221517629920158359 := by
  unfold tailWord_557181
  simp only [CollatzResearch.WordTrace]
  refine ⟨20322060594435870783919397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13548040396290580522612931 20322060594435870783919397)
  ·
    refine ⟨3810386361456725771984887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20322060594435870783919397 3810386361456725771984887)
    ·
      refine ⟨5715579542185088657977331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3810386361456725771984887 5715579542185088657977331)
      ·
        refine ⟨8573369313277632986965997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5715579542185088657977331 8573369313277632986965997)
        ·
          refine ⟨3215013492479112370112249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8573369313277632986965997 3215013492479112370112249)
          ·
            refine ⟨2411260119359334277584187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3215013492479112370112249 2411260119359334277584187)
            ·
              refine ⟨3616890179039001416376281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411260119359334277584187 3616890179039001416376281)
              ·
                refine ⟨2712667634279251062282211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3616890179039001416376281 2712667634279251062282211)
                ·
                  refine ⟨4069001451418876593423317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2712667634279251062282211 4069001451418876593423317)
                  ·
                    refine ⟨95367221517629920158359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4069001451418876593423317 95367221517629920158359)
                    ·
                      rfl

theorem cell23_557181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_557181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557181 prefixEnd_557181 := by exact prefixLift 557181
  have htrace : WordTrace (prefixWord ++ tailWord_557181) baseStart_557181 baseEnd_557181 := by
    simpa [prefixWord, tailWord_557181, baseEnd_557181] using wordTrace_append hprefix tailTrace_557181
  have hstable : (prefixWord ++ tailWord_557181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557181).length < 2 ^ (prefixWord ++ tailWord_557181).sum := by decide
  have hdescent : baseEnd_557181 < baseStart_557181 := by decide
  rcases family_descends (prefixWord ++ tailWord_557181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557201 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_557201 : Nat := 118140960795 + 557201 * 2 ^ 59
def prefixEnd_557201 : Nat := 4983230072969 + 3 ^ 40 * 557201 * 2
def baseEnd_557201 : Nat := 286111934165979682224985

theorem tailTrace_557201 : CollatzResearch.WordTrace tailWord_557201 prefixEnd_557201 286111934165979682224985 := by
  unfold tailWord_557201
  simp only [CollatzResearch.WordTrace]
  refine ⟨20322790054363414199647457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13548526702908942799764971 20322790054363414199647457)
  ·
    refine ⟨15242092540772560649735593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20322790054363414199647457 15242092540772560649735593)
    ·
      refine ⟨11431569405579420487301695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15242092540772560649735593 11431569405579420487301695)
      ·
        refine ⟨17147354108369130730952543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11431569405579420487301695 17147354108369130730952543)
        ·
          refine ⟨25721031162553696096428815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17147354108369130730952543 25721031162553696096428815)
          ·
            refine ⟨38581546743830544144643223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25721031162553696096428815 38581546743830544144643223)
            ·
              refine ⟨57872320115745816216964835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38581546743830544144643223 57872320115745816216964835)
              ·
                refine ⟨86808480173618724325447253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57872320115745816216964835 86808480173618724325447253)
                ·
                  refine ⟨1017286877034594425688835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 86808480173618724325447253 1017286877034594425688835)
                  ·
                    refine ⟨1525930315551891638533253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1017286877034594425688835 1525930315551891638533253)
                    ·
                      refine ⟨286111934165979682224985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1525930315551891638533253 286111934165979682224985)
                      ·
                        rfl

theorem cell23_557201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_557201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557201 prefixEnd_557201 := by exact prefixLift 557201
  have htrace : WordTrace (prefixWord ++ tailWord_557201) baseStart_557201 baseEnd_557201 := by
    simpa [prefixWord, tailWord_557201, baseEnd_557201] using wordTrace_append hprefix tailTrace_557201
  have hstable : (prefixWord ++ tailWord_557201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557201).length < 2 ^ (prefixWord ++ tailWord_557201).sum := by decide
  have hdescent : baseEnd_557201 < baseStart_557201 := by decide
  rcases family_descends (prefixWord ++ tailWord_557201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557230 : List Nat := [4, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_557230 : Nat := 118140960795 + 557230 * 2 ^ 59
def prefixEnd_557230 : Nat := 4983230072969 + 3 ^ 40 * 557230 * 2
def baseEnd_557230 : Nat := 286126825104960068762353

theorem tailTrace_557230 : CollatzResearch.WordTrace tailWord_557230 prefixEnd_557230 286126825104960068762353 := by
  unfold tailWord_557230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2540480971407294019056643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13549231847505568101635429 2540480971407294019056643)
  ·
    refine ⟨3810721457110941028584965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2540480971407294019056643 3810721457110941028584965)
    ·
      refine ⟨714510273208301442859681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3810721457110941028584965 714510273208301442859681)
      ·
        refine ⟨535882704906226082144761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 714510273208301442859681 535882704906226082144761)
        ·
          refine ⟨401912028679669561608571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 535882704906226082144761 401912028679669561608571)
          ·
            refine ⟨602868043019504342412857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401912028679669561608571 602868043019504342412857)
            ·
              refine ⟨452151032264628256809643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602868043019504342412857 452151032264628256809643)
              ·
                refine ⟨678226548396942385214465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452151032264628256809643 678226548396942385214465)
                ·
                  refine ⟨508669911297706788910849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 678226548396942385214465 508669911297706788910849)
                  ·
                    refine ⟨381502433473280091683137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 508669911297706788910849 381502433473280091683137)
                    ·
                      refine ⟨286126825104960068762353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 381502433473280091683137 286126825104960068762353)
                      ·
                        rfl

theorem cell23_557230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_557230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557230 prefixEnd_557230 := by exact prefixLift 557230
  have htrace : WordTrace (prefixWord ++ tailWord_557230) baseStart_557230 baseEnd_557230 := by
    simpa [prefixWord, tailWord_557230, baseEnd_557230] using wordTrace_append hprefix tailTrace_557230
  have hstable : (prefixWord ++ tailWord_557230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557230).length < 2 ^ (prefixWord ++ tailWord_557230).sum := by decide
  have hdescent : baseEnd_557230 < baseStart_557230 := by decide
  rcases family_descends (prefixWord ++ tailWord_557230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557288 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 3, 5]
def baseStart_557288 : Nat := 118140960795 + 557288 * 2 ^ 59
def prefixEnd_557288 : Nat := 4983230072969 + 3 ^ 40 * 557288 * 2
def baseEnd_557288 : Nat := 95385535660973613945695

theorem tailTrace_557288 : CollatzResearch.WordTrace tailWord_557288 prefixEnd_557288 95385535660973613945695 := by
  unfold tailWord_557288
  simp only [CollatzResearch.WordTrace]
  refine ⟨10162981602524114029032259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13550642136698818705376345 10162981602524114029032259)
  ·
    refine ⟨15244472403786171043548389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10162981602524114029032259 15244472403786171043548389)
    ·
      refine ⟨2858338575709907070665323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15244472403786171043548389 2858338575709907070665323)
      ·
        refine ⟨4287507863564860605997985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2858338575709907070665323 4287507863564860605997985)
        ·
          refine ⟨3215630897673645454498489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4287507863564860605997985 3215630897673645454498489)
          ·
            refine ⟨2411723173255234090873867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3215630897673645454498489 2411723173255234090873867)
            ·
              refine ⟨3617584759882851136310801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411723173255234090873867 3617584759882851136310801)
              ·
                refine ⟨2713188569912138352233101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3617584759882851136310801 2713188569912138352233101)
                ·
                  refine ⟨1017445713717051882087413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2713188569912138352233101 1017445713717051882087413)
                  ·
                    refine ⟨95385535660973613945695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1017445713717051882087413 95385535660973613945695)
                    ·
                      rfl

theorem cell23_557288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_557288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557288 prefixEnd_557288 := by exact prefixLift 557288
  have htrace : WordTrace (prefixWord ++ tailWord_557288) baseStart_557288 baseEnd_557288 := by
    simpa [prefixWord, tailWord_557288, baseEnd_557288] using wordTrace_append hprefix tailTrace_557288
  have hstable : (prefixWord ++ tailWord_557288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557288).length < 2 ^ (prefixWord ++ tailWord_557288).sum := by decide
  have hdescent : baseEnd_557288 < baseStart_557288 := by decide
  rcases family_descends (prefixWord ++ tailWord_557288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557335 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 4, 4]
def baseStart_557335 : Nat := 118140960795 + 557335 * 2 ^ 59
def prefixEnd_557335 : Nat := 4983230072969 + 3 ^ 40 * 557335 * 2
def baseEnd_557335 : Nat := 95393580191227385983123

theorem tailTrace_557335 : CollatzResearch.WordTrace tailWord_557335 prefixEnd_557335 95393580191227385983123 := by
  unfold tailWord_557335
  simp only [CollatzResearch.WordTrace]
  refine ⟨20327677435877955085025459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13551784957251970056683639 20327677435877955085025459)
  ·
    refine ⟨30491516153816932627538189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20327677435877955085025459 30491516153816932627538189)
    ·
      refine ⟨11434318557681349735326821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30491516153816932627538189 11434318557681349735326821)
      ·
        refine ⟨2143934729565253075373779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11434318557681349735326821 2143934729565253075373779)
        ·
          refine ⟨3215902094347879613060669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2143934729565253075373779 3215902094347879613060669)
          ·
            refine ⟨1205963285380454854897751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3215902094347879613060669 1205963285380454854897751)
            ·
              refine ⟨1808944928070682282346627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205963285380454854897751 1808944928070682282346627)
              ·
                refine ⟨2713417392106023423519941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1808944928070682282346627 2713417392106023423519941)
                ·
                  refine ⟨508765761019879391909989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2713417392106023423519941 508765761019879391909989)
                  ·
                    refine ⟨95393580191227385983123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 508765761019879391909989 95393580191227385983123)
                    ·
                      rfl

theorem cell23_557335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_557335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557335 prefixEnd_557335 := by exact prefixLift 557335
  have htrace : WordTrace (prefixWord ++ tailWord_557335) baseStart_557335 baseEnd_557335 := by
    simpa [prefixWord, tailWord_557335, baseEnd_557335] using wordTrace_append hprefix tailTrace_557335
  have hstable : (prefixWord ++ tailWord_557335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557335).length < 2 ^ (prefixWord ++ tailWord_557335).sum := by decide
  have hdescent : baseEnd_557335 < baseStart_557335 := by decide
  rcases family_descends (prefixWord ++ tailWord_557335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557352 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 1, 6]
def baseStart_557352 : Nat := 118140960795 + 557352 * 2 ^ 59
def prefixEnd_557352 : Nat := 4983230072969 + 3 ^ 40 * 557352 * 2
def baseEnd_557352 : Nat := 95396489914936197145597

theorem tailTrace_557352 : CollatzResearch.WordTrace tailWord_557352 prefixEnd_557352 95396489914936197145597 := by
  unfold tailWord_557352
  simp only [CollatzResearch.WordTrace]
  refine ⟨10164148738408183494197155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13552198317877577992262873 10164148738408183494197155)
  ·
    refine ⟨15246223107612275241295733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10164148738408183494197155 15246223107612275241295733)
    ·
      refine ⟨1429333416338650803871475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15246223107612275241295733 1429333416338650803871475)
      ·
        refine ⟨2144000124507976205807213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429333416338650803871475 2144000124507976205807213)
        ·
          refine ⟨804000046690491077177705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2144000124507976205807213 804000046690491077177705)
          ·
            refine ⟨603000035017868307883279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 804000046690491077177705 603000035017868307883279)
            ·
              refine ⟨904500052526802461824919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603000035017868307883279 904500052526802461824919)
              ·
                refine ⟨1356750078790203692737379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904500052526802461824919 1356750078790203692737379)
                ·
                  refine ⟨2035125118185305539106069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356750078790203692737379 2035125118185305539106069)
                  ·
                    refine ⟨95396489914936197145597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2035125118185305539106069 95396489914936197145597)
                    ·
                      rfl

theorem cell23_557352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_557352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557352 prefixEnd_557352 := by exact prefixLift 557352
  have htrace : WordTrace (prefixWord ++ tailWord_557352) baseStart_557352 baseEnd_557352 := by
    simpa [prefixWord, tailWord_557352, baseEnd_557352] using wordTrace_append hprefix tailTrace_557352
  have hstable : (prefixWord ++ tailWord_557352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557352).length < 2 ^ (prefixWord ++ tailWord_557352).sum := by decide
  have hdescent : baseEnd_557352 < baseStart_557352 := by decide
  rcases family_descends (prefixWord ++ tailWord_557352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557375 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 6, 1, 3]
def baseStart_557375 : Nat := 118140960795 + 557375 * 2 ^ 59
def prefixEnd_557375 : Nat := 4983230072969 + 3 ^ 40 * 557375 * 2
def baseEnd_557375 : Nat := 286201279799862001449185

theorem tailTrace_557375 : CollatzResearch.WordTrace tailWord_557375 prefixEnd_557375 286201279799862001449185 := by
  unfold tailWord_557375
  simp only [CollatzResearch.WordTrace]
  refine ⟨20329136355733041916481579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13552757570488694610987719 20329136355733041916481579)
  ·
    refine ⟨30493704533599562874722369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20329136355733041916481579 30493704533599562874722369)
    ·
      refine ⟨22870278400199672156041777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30493704533599562874722369 22870278400199672156041777)
      ·
        refine ⟨17152708800149754117031333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22870278400199672156041777 17152708800149754117031333)
        ·
          refine ⟨3216132900028078896943375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17152708800149754117031333 3216132900028078896943375)
          ·
            refine ⟨4824199350042118345415063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3216132900028078896943375 4824199350042118345415063)
            ·
              refine ⟨7236299025063177518122595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4824199350042118345415063 7236299025063177518122595)
              ·
                refine ⟨10854448537594766277183893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7236299025063177518122595 10854448537594766277183893)
                ·
                  refine ⟨508802275199754669242995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10854448537594766277183893 508802275199754669242995)
                  ·
                    refine ⟨763203412799632003864493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 508802275199754669242995 763203412799632003864493)
                    ·
                      refine ⟨286201279799862001449185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 763203412799632003864493 286201279799862001449185)
                      ·
                        rfl

theorem cell23_557375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_557375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557375 prefixEnd_557375 := by exact prefixLift 557375
  have htrace : WordTrace (prefixWord ++ tailWord_557375) baseStart_557375 baseEnd_557375 := by
    simpa [prefixWord, tailWord_557375, baseEnd_557375] using wordTrace_append hprefix tailTrace_557375
  have hstable : (prefixWord ++ tailWord_557375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557375).length < 2 ^ (prefixWord ++ tailWord_557375).sum := by decide
  have hdescent : baseEnd_557375 < baseStart_557375 := by decide
  rcases family_descends (prefixWord ++ tailWord_557375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557385 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 5, 3, 2]
def baseStart_557385 : Nat := 118140960795 + 557385 * 2 ^ 59
def prefixEnd_557385 : Nat := 4983230072969 + 3 ^ 40 * 557385 * 2
def baseEnd_557385 : Nat := 286206414606406962324139

theorem tailTrace_557385 : CollatzResearch.WordTrace tailWord_557385 prefixEnd_557385 286206414606406962324139 := by
  unfold tailWord_557385
  simp only [CollatzResearch.WordTrace]
  refine ⟨20329501085696813624345609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13553000723797875749563739 20329501085696813624345609)
  ·
    refine ⟨15247125814272610218259207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20329501085696813624345609 15247125814272610218259207)
    ·
      refine ⟨22870688721408915327388811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15247125814272610218259207 22870688721408915327388811)
      ·
        refine ⟨34306033082113372991083217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22870688721408915327388811 34306033082113372991083217)
        ·
          refine ⟨25729524811585029743312413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34306033082113372991083217 25729524811585029743312413)
          ·
            refine ⟨9648571804344386153742155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25729524811585029743312413 9648571804344386153742155)
            ·
              refine ⟨14472857706516579230613233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9648571804344386153742155 14472857706516579230613233)
              ·
                refine ⟨10854643279887434422959925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14472857706516579230613233 10854643279887434422959925)
                ·
                  refine ⟨1017622807489446977152493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10854643279887434422959925 1017622807489446977152493)
                  ·
                    refine ⟨381608552808542616432185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1017622807489446977152493 381608552808542616432185)
                    ·
                      refine ⟨286206414606406962324139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 381608552808542616432185 286206414606406962324139)
                      ·
                        rfl

theorem cell23_557385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 3, 2].length) (baseStart_557385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557385 prefixEnd_557385 := by exact prefixLift 557385
  have htrace : WordTrace (prefixWord ++ tailWord_557385) baseStart_557385 baseEnd_557385 := by
    simpa [prefixWord, tailWord_557385, baseEnd_557385] using wordTrace_append hprefix tailTrace_557385
  have hstable : (prefixWord ++ tailWord_557385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557385).length < 2 ^ (prefixWord ++ tailWord_557385).sum := by decide
  have hdescent : baseEnd_557385 < baseStart_557385 := by decide
  rcases family_descends (prefixWord ++ tailWord_557385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557388 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_557388 : Nat := 118140960795 + 557388 * 2 ^ 59
def prefixEnd_557388 : Nat := 4983230072969 + 3 ^ 40 * 557388 * 2
def baseEnd_557388 : Nat := 286207955048370450586625

theorem tailTrace_557388 : CollatzResearch.WordTrace tailWord_557388 prefixEnd_557388 286207955048370450586625 := by
  unfold tailWord_557388
  simp only [CollatzResearch.WordTrace]
  refine ⟨10164805252342972568352409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13553073669790630091136545 10164805252342972568352409)
  ·
    refine ⟨7623603939257229426264307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10164805252342972568352409 7623603939257229426264307)
    ·
      refine ⟨11435405908885844139396461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7623603939257229426264307 11435405908885844139396461)
      ·
        refine ⟨4288277215832191552273673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11435405908885844139396461 4288277215832191552273673)
        ·
          refine ⟨3216207911874143664205255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4288277215832191552273673 3216207911874143664205255)
          ·
            refine ⟨4824311867811215496307883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3216207911874143664205255 4824311867811215496307883)
            ·
              refine ⟨7236467801716823244461825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4824311867811215496307883 7236467801716823244461825)
              ·
                refine ⟨5427350851287617433346369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7236467801716823244461825 5427350851287617433346369)
                ·
                  refine ⟨4070513138465713075009777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5427350851287617433346369 4070513138465713075009777)
                  ·
                    refine ⟨3052884853849284806257333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4070513138465713075009777 3052884853849284806257333)
                    ·
                      refine ⟨286207955048370450586625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3052884853849284806257333 286207955048370450586625)
                      ·
                        rfl

theorem cell23_557388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_557388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557388 prefixEnd_557388 := by exact prefixLift 557388
  have htrace : WordTrace (prefixWord ++ tailWord_557388) baseStart_557388 baseEnd_557388 := by
    simpa [prefixWord, tailWord_557388, baseEnd_557388] using wordTrace_append hprefix tailTrace_557388
  have hstable : (prefixWord ++ tailWord_557388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557388).length < 2 ^ (prefixWord ++ tailWord_557388).sum := by decide
  have hdescent : baseEnd_557388 < baseStart_557388 := by decide
  rcases family_descends (prefixWord ++ tailWord_557388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557449 : List Nat := [1, 2, 1, 1, 6, 1, 1, 4, 2, 2, 2]
def baseStart_557449 : Nat := 118140960795 + 557449 * 2 ^ 59
def prefixEnd_557449 : Nat := 4983230072969 + 3 ^ 40 * 557449 * 2
def baseEnd_557449 : Nat := 286239277368294711923845

theorem tailTrace_557449 : CollatzResearch.WordTrace tailWord_557449 prefixEnd_557449 286239277368294711923845 := by
  unfold tailWord_557449
  simp only [CollatzResearch.WordTrace]
  refine ⟨20331835357464952554675401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13554556904976635036450267 20331835357464952554675401)
  ·
    refine ⟨15248876518098714416006551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20331835357464952554675401 15248876518098714416006551)
    ·
      refine ⟨22873314777148071624009827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15248876518098714416006551 22873314777148071624009827)
      ·
        refine ⟨34309972165722107436014741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22873314777148071624009827 34309972165722107436014741)
        ·
          refine ⟨1608279945268223786063191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34309972165722107436014741 1608279945268223786063191)
          ·
            refine ⟨2412419917902335679094787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1608279945268223786063191 2412419917902335679094787)
            ·
              refine ⟨3618629876853503518642181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412419917902335679094787 3618629876853503518642181)
              ·
                refine ⟨678493101910031909745409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3618629876853503518642181 678493101910031909745409)
                ·
                  refine ⟨508869826432523932309057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 678493101910031909745409 508869826432523932309057)
                  ·
                    refine ⟨381652369824392949231793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 508869826432523932309057 381652369824392949231793)
                    ·
                      refine ⟨286239277368294711923845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 381652369824392949231793 286239277368294711923845)
                      ·
                        rfl

theorem cell23_557449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 2, 2].length) (baseStart_557449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557449 prefixEnd_557449 := by exact prefixLift 557449
  have htrace : WordTrace (prefixWord ++ tailWord_557449) baseStart_557449 baseEnd_557449 := by
    simpa [prefixWord, tailWord_557449, baseEnd_557449] using wordTrace_append hprefix tailTrace_557449
  have hstable : (prefixWord ++ tailWord_557449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557449).length < 2 ^ (prefixWord ++ tailWord_557449).sum := by decide
  have hdescent : baseEnd_557449 < baseStart_557449 := by decide
  rcases family_descends (prefixWord ++ tailWord_557449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557465 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 2, 3, 3]
def baseStart_557465 : Nat := 118140960795 + 557465 * 2 ^ 59
def prefixEnd_557465 : Nat := 4983230072969 + 3 ^ 40 * 557465 * 2
def baseEnd_557465 : Nat := 286247493058766649323771

theorem tailTrace_557465 : CollatzResearch.WordTrace tailWord_557465 prefixEnd_557465 286247493058766649323771 := by
  unfold tailWord_557465
  simp only [CollatzResearch.WordTrace]
  refine ⟨20332418925406987287257849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13554945950271324858171899 20332418925406987287257849)
  ·
    refine ⟨15249314194055240465443387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20332418925406987287257849 15249314194055240465443387)
    ·
      refine ⟨22873971291082860698165081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15249314194055240465443387 22873971291082860698165081)
      ·
        refine ⟨17155478468312145523623811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22873971291082860698165081 17155478468312145523623811)
        ·
          refine ⟨25733217702468218285435717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17155478468312145523623811 25733217702468218285435717)
          ·
            refine ⟨4824978319212790928519197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25733217702468218285435717 4824978319212790928519197)
            ·
              refine ⟨1809366869704796598194699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4824978319212790928519197 1809366869704796598194699)
              ·
                refine ⟨2714050304557194897292049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1809366869704796598194699 2714050304557194897292049)
                ·
                  refine ⟨2035537728417896172969037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2714050304557194897292049 2035537728417896172969037)
                  ·
                    refine ⟨763326648156711064863389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2035537728417896172969037 763326648156711064863389)
                    ·
                      refine ⟨286247493058766649323771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 763326648156711064863389 286247493058766649323771)
                      ·
                        rfl

theorem cell23_557465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_557465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557465 prefixEnd_557465 := by exact prefixLift 557465
  have htrace : WordTrace (prefixWord ++ tailWord_557465) baseStart_557465 baseEnd_557465 := by
    simpa [prefixWord, tailWord_557465, baseEnd_557465] using wordTrace_append hprefix tailTrace_557465
  have hstable : (prefixWord ++ tailWord_557465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557465).length < 2 ^ (prefixWord ++ tailWord_557465).sum := by decide
  have hdescent : baseEnd_557465 < baseStart_557465 := by decide
  rcases family_descends (prefixWord ++ tailWord_557465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557498 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 1, 10]
def baseStart_557498 : Nat := 118140960795 + 557498 * 2 ^ 59
def prefixEnd_557498 : Nat := 4983230072969 + 3 ^ 40 * 557498 * 2
def baseEnd_557498 : Nat := 95421479306788340070373

theorem tailTrace_557498 : CollatzResearch.WordTrace tailWord_557498 prefixEnd_557498 95421479306788340070373 := by
  unfold tailWord_557498
  simp only [CollatzResearch.WordTrace]
  refine ⟨5083405633571858480802287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13555748356191622615472765 5083405633571858480802287)
  ·
    refine ⟨7625108450357787721203431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5083405633571858480802287 7625108450357787721203431)
    ·
      refine ⟨11437662675536681581805147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7625108450357787721203431 11437662675536681581805147)
      ·
        refine ⟨17156494013305022372707721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11437662675536681581805147 17156494013305022372707721)
        ·
          refine ⟨12867370509978766779530791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17156494013305022372707721 12867370509978766779530791)
          ·
            refine ⟨19301055764968150169296187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12867370509978766779530791 19301055764968150169296187)
            ·
              refine ⟨28951583647452225253944281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19301055764968150169296187 28951583647452225253944281)
              ·
                refine ⟨21713687735589168940458211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28951583647452225253944281 21713687735589168940458211)
                ·
                  refine ⟨32570531603383753410687317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21713687735589168940458211 32570531603383753410687317)
                  ·
                    refine ⟨95421479306788340070373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 32570531603383753410687317 95421479306788340070373)
                    ·
                      rfl

theorem cell23_557498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_557498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557498 prefixEnd_557498 := by exact prefixLift 557498
  have htrace : WordTrace (prefixWord ++ tailWord_557498) baseStart_557498 baseEnd_557498 := by
    simpa [prefixWord, tailWord_557498, baseEnd_557498] using wordTrace_append hprefix tailTrace_557498
  have hstable : (prefixWord ++ tailWord_557498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557498).length < 2 ^ (prefixWord ++ tailWord_557498).sum := by decide
  have hdescent : baseEnd_557498 < baseStart_557498 := by decide
  rcases family_descends (prefixWord ++ tailWord_557498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557579 : List Nat := [1, 1, 1, 1, 7, 3, 2, 1, 6]
def baseStart_557579 : Nat := 118140960795 + 557579 * 2 ^ 59
def prefixEnd_557579 : Nat := 4983230072969 + 3 ^ 40 * 557579 * 2
def baseEnd_557579 : Nat := 31811781094819911477583

theorem tailTrace_557579 : CollatzResearch.WordTrace tailWord_557579 prefixEnd_557579 31811781094819911477583 := by
  unfold tailWord_557579
  simp only [CollatzResearch.WordTrace]
  refine ⟨20336576846993984756907791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13557717897995989837938527 20336576846993984756907791)
  ·
    refine ⟨30504865270490977135361687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20336576846993984756907791 30504865270490977135361687)
    ·
      refine ⟨45757297905736465703042531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30504865270490977135361687 45757297905736465703042531)
      ·
        refine ⟨68635946858604698554563797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45757297905736465703042531 68635946858604698554563797)
        ·
          refine ⟨1608655004498547622372589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 68635946858604698554563797 1608655004498547622372589)
          ·
            refine ⟨603245626686955358389721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1608655004498547622372589 603245626686955358389721)
            ·
              refine ⟨452434220015216518792291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603245626686955358389721 452434220015216518792291)
              ·
                refine ⟨678651330022824778188437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452434220015216518792291 678651330022824778188437)
                ·
                  refine ⟨31811781094819911477583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 678651330022824778188437 31811781094819911477583)
                  ·
                    rfl

theorem cell23_557579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 6].length) (baseStart_557579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557579 prefixEnd_557579 := by exact prefixLift 557579
  have htrace : WordTrace (prefixWord ++ tailWord_557579) baseStart_557579 baseEnd_557579 := by
    simpa [prefixWord, tailWord_557579, baseEnd_557579] using wordTrace_append hprefix tailTrace_557579
  have hstable : (prefixWord ++ tailWord_557579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557579).length < 2 ^ (prefixWord ++ tailWord_557579).sum := by decide
  have hdescent : baseEnd_557579 < baseStart_557579 := by decide
  rcases family_descends (prefixWord ++ tailWord_557579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557592 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 3, 5]
def baseStart_557592 : Nat := 118140960795 + 557592 * 2 ^ 59
def prefixEnd_557592 : Nat := 4983230072969 + 3 ^ 40 * 557592 * 2
def baseEnd_557592 : Nat := 95437568367295884145229

theorem tailTrace_557592 : CollatzResearch.WordTrace tailWord_557592 prefixEnd_557592 95437568367295884145229 := by
  unfold tailWord_557592
  simp only [CollatzResearch.WordTrace]
  refine ⟨10168525497973443988565515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13558033997297925318087353 10168525497973443988565515)
  ·
    refine ⟨15252788246960165982848273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10168525497973443988565515 15252788246960165982848273)
    ·
      refine ⟨11439591185220124487136205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15252788246960165982848273 11439591185220124487136205)
      ·
        refine ⟨4289846694457546682676077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11439591185220124487136205 4289846694457546682676077)
        ·
          refine ⟨1608692510421580006003529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4289846694457546682676077 1608692510421580006003529)
          ·
            refine ⟨1206519382816185004502647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1608692510421580006003529 1206519382816185004502647)
            ·
              refine ⟨1809779074224277506753971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206519382816185004502647 1809779074224277506753971)
              ·
                refine ⟨2714668611336416260130957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1809779074224277506753971 2714668611336416260130957)
                ·
                  refine ⟨1018000729251156097549109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2714668611336416260130957 1018000729251156097549109)
                  ·
                    refine ⟨95437568367295884145229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1018000729251156097549109 95437568367295884145229)
                    ·
                      rfl

theorem cell23_557592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_557592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557592 prefixEnd_557592 := by exact prefixLift 557592
  have htrace : WordTrace (prefixWord ++ tailWord_557592) baseStart_557592 baseEnd_557592 := by
    simpa [prefixWord, tailWord_557592, baseEnd_557592] using wordTrace_append hprefix tailTrace_557592
  have hstable : (prefixWord ++ tailWord_557592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557592).length < 2 ^ (prefixWord ++ tailWord_557592).sum := by decide
  have hdescent : baseEnd_557592 < baseStart_557592 := by decide
  rcases family_descends (prefixWord ++ tailWord_557592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557605 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 3, 6]
def baseStart_557605 : Nat := 118140960795 + 557605 * 2 ^ 59
def prefixEnd_557605 : Nat := 4983230072969 + 3 ^ 40 * 557605 * 2
def baseEnd_557605 : Nat := 95439793450132033857709

theorem tailTrace_557605 : CollatzResearch.WordTrace tailWord_557605 prefixEnd_557605 95439793450132033857709 := by
  unfold tailWord_557605
  simp only [CollatzResearch.WordTrace]
  refine ⟨20337525144899791197354269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13558350096599860798236179 20337525144899791197354269)
  ·
    refine ⟨7626571929337421699007851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20337525144899791197354269 7626571929337421699007851)
    ·
      refine ⟨11439857894006132548511777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7626571929337421699007851 11439857894006132548511777)
      ·
        refine ⟨8579893420504599411383833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11439857894006132548511777 8579893420504599411383833)
        ·
          refine ⟨6434920065378449558537875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8579893420504599411383833 6434920065378449558537875)
          ·
            refine ⟨9652380098067674337806813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6434920065378449558537875 9652380098067674337806813)
            ·
              refine ⟨3619642536775377876677555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9652380098067674337806813 3619642536775377876677555)
              ·
                refine ⟨5429463805163066815016333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619642536775377876677555 5429463805163066815016333)
                ·
                  refine ⟨2036048926936150055631125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5429463805163066815016333 2036048926936150055631125)
                  ·
                    refine ⟨95439793450132033857709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2036048926936150055631125 95439793450132033857709)
                    ·
                      rfl

theorem cell23_557605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_557605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557605 prefixEnd_557605 := by exact prefixLift 557605
  have htrace : WordTrace (prefixWord ++ tailWord_557605) baseStart_557605 baseEnd_557605 := by
    simpa [prefixWord, tailWord_557605, baseEnd_557605] using wordTrace_append hprefix tailTrace_557605
  have hstable : (prefixWord ++ tailWord_557605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557605).length < 2 ^ (prefixWord ++ tailWord_557605).sum := by decide
  have hdescent : baseEnd_557605 < baseStart_557605 := by decide
  rcases family_descends (prefixWord ++ tailWord_557605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557612 : List Nat := [2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 4]
def baseStart_557612 : Nat := 118140960795 + 557612 * 2 ^ 59
def prefixEnd_557612 : Nat := 4983230072969 + 3 ^ 40 * 557612 * 2
def baseEnd_557612 : Nat := 286322974714977574185595

theorem tailTrace_557612 : CollatzResearch.WordTrace tailWord_557612 prefixEnd_557612 286322974714977574185595 := by
  unfold tailWord_557612
  simp only [CollatzResearch.WordTrace]
  refine ⟨10168890227937215696429545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13558520303916287595239393 10168890227937215696429545)
  ·
    refine ⟨7626667670952911772322159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10168890227937215696429545 7626667670952911772322159)
    ·
      refine ⟨11440001506429367658483239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7626667670952911772322159 11440001506429367658483239)
      ·
        refine ⟨17160002259644051487724859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11440001506429367658483239 17160002259644051487724859)
        ·
          refine ⟨25740003389466077231587289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17160002259644051487724859 25740003389466077231587289)
          ·
            refine ⟨19305002542099557923690467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25740003389466077231587289 19305002542099557923690467)
            ·
              refine ⟨28957503813149336885535701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19305002542099557923690467 28957503813149336885535701)
              ·
                refine ⟨678691495620687583254743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28957503813149336885535701 678691495620687583254743)
                ·
                  refine ⟨1018037243431031374882115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678691495620687583254743 1018037243431031374882115)
                  ·
                    refine ⟨1527055865146547062323173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1018037243431031374882115 1527055865146547062323173)
                    ·
                      refine ⟨286322974714977574185595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1527055865146547062323173 286322974714977574185595)
                      ·
                        rfl

theorem cell23_557612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_557612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557612 prefixEnd_557612 := by exact prefixLift 557612
  have htrace : WordTrace (prefixWord ++ tailWord_557612) baseStart_557612 baseEnd_557612 := by
    simpa [prefixWord, tailWord_557612, baseEnd_557612] using wordTrace_append hprefix tailTrace_557612
  have hstable : (prefixWord ++ tailWord_557612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557612).length < 2 ^ (prefixWord ++ tailWord_557612).sum := by decide
  have hdescent : baseEnd_557612 < baseStart_557612 := by decide
  rcases family_descends (prefixWord ++ tailWord_557612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557613 : List Nat := [1, 5, 4, 1, 1, 1, 2, 2, 6]
def baseStart_557613 : Nat := 118140960795 + 557613 * 2 ^ 59
def prefixEnd_557613 : Nat := 4983230072969 + 3 ^ 40 * 557613 * 2
def baseEnd_557613 : Nat := 31813720910625785585899

theorem tailTrace_557613 : CollatzResearch.WordTrace tailWord_557613 prefixEnd_557613 31813720910625785585899 := by
  unfold tailWord_557613
  simp only [CollatzResearch.WordTrace]
  refine ⟨20337816928870808563645493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13558544619247205709096995 20337816928870808563645493)
  ·
    refine ⟨1906670337081638302841765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20337816928870808563645493 1906670337081638302841765)
    ·
      refine ⟨357500688202807181782831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1906670337081638302841765 357500688202807181782831)
      ·
        refine ⟨536251032304210772674247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357500688202807181782831 536251032304210772674247)
        ·
          refine ⟨804376548456316159011371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536251032304210772674247 804376548456316159011371)
          ·
            refine ⟨1206564822684474238517057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804376548456316159011371 1206564822684474238517057)
            ·
              refine ⟨904923617013355678887793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206564822684474238517057 904923617013355678887793)
              ·
                refine ⟨678692712760016759165845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904923617013355678887793 678692712760016759165845)
                ·
                  refine ⟨31813720910625785585899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 678692712760016759165845 31813720910625785585899)
                  ·
                    rfl

theorem cell23_557613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_557613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557613 prefixEnd_557613 := by exact prefixLift 557613
  have htrace : WordTrace (prefixWord ++ tailWord_557613) baseStart_557613 baseEnd_557613 := by
    simpa [prefixWord, tailWord_557613, baseEnd_557613] using wordTrace_append hprefix tailTrace_557613
  have hstable : (prefixWord ++ tailWord_557613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557613).length < 2 ^ (prefixWord ++ tailWord_557613).sum := by decide
  have hdescent : baseEnd_557613 < baseStart_557613 := by decide
  rcases family_descends (prefixWord ++ tailWord_557613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557632 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 3]
def baseStart_557632 : Nat := 118140960795 + 557632 * 2 ^ 59
def prefixEnd_557632 : Nat := 4983230072969 + 3 ^ 40 * 557632 * 2
def baseEnd_557632 : Nat := 286333244328067495935503

theorem tailTrace_557632 : CollatzResearch.WordTrace tailWord_557632 prefixEnd_557632 286333244328067495935503 := by
  unfold tailWord_557632
  simp only [CollatzResearch.WordTrace]
  refine ⟨10169254957900987404293575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13559006610534649872391433 10169254957900987404293575)
  ·
    refine ⟨15253882436851481106440363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10169254957900987404293575 15253882436851481106440363)
    ·
      refine ⟨22880823655277221659660545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15253882436851481106440363 22880823655277221659660545)
      ·
        refine ⟨17160617741457916244745409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22880823655277221659660545 17160617741457916244745409)
        ·
          refine ⟨12870463306093437183559057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17160617741457916244745409 12870463306093437183559057)
          ·
            refine ⟨9652847479570077887669293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12870463306093437183559057 9652847479570077887669293)
            ·
              refine ⟨3619817804838779207875985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9652847479570077887669293 3619817804838779207875985)
              ·
                refine ⟨2714863353629084405906989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3619817804838779207875985 2714863353629084405906989)
                ·
                  refine ⟨1018073757610906652215121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2714863353629084405906989 1018073757610906652215121)
                  ·
                    refine ⟨763555318208179989161341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1018073757610906652215121 763555318208179989161341)
                    ·
                      refine ⟨286333244328067495935503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 763555318208179989161341 286333244328067495935503)
                      ·
                        rfl

theorem cell23_557632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_557632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557632 prefixEnd_557632 := by exact prefixLift 557632
  have htrace : WordTrace (prefixWord ++ tailWord_557632) baseStart_557632 baseEnd_557632 := by
    simpa [prefixWord, tailWord_557632, baseEnd_557632] using wordTrace_append hprefix tailTrace_557632
  have hstable : (prefixWord ++ tailWord_557632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557632).length < 2 ^ (prefixWord ++ tailWord_557632).sum := by decide
  have hdescent : baseEnd_557632 < baseStart_557632 := by decide
  rcases family_descends (prefixWord ++ tailWord_557632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557639 : List Nat := [1, 1, 4, 1, 4, 1, 2, 3, 2, 4]
def baseStart_557639 : Nat := 118140960795 + 557639 * 2 ^ 59
def prefixEnd_557639 : Nat := 4983230072969 + 3 ^ 40 * 557639 * 2
def baseEnd_557639 : Nat := 95445612897549656182657

theorem tailTrace_557639 : CollatzResearch.WordTrace tailWord_557639 prefixEnd_557639 95445612897549656182657 := by
  unfold tailWord_557639
  simp only [CollatzResearch.WordTrace]
  refine ⟨20338765226776615004091971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13559176817851076669394647 20338765226776615004091971)
  ·
    refine ⟨30508147840164922506137957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20338765226776615004091971 30508147840164922506137957)
    ·
      refine ⟨5720277720030922969900867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30508147840164922506137957 5720277720030922969900867)
      ·
        refine ⟨8580416580046384454851301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5720277720030922969900867 8580416580046384454851301)
        ·
          refine ⟨1608828108758697085284619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8580416580046384454851301 1608828108758697085284619)
          ·
            refine ⟨2413242163138045627926929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1608828108758697085284619 2413242163138045627926929)
            ·
              refine ⟨1809931622353534220945197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2413242163138045627926929 1809931622353534220945197)
              ·
                refine ⟨678724358382575332854449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1809931622353534220945197 678724358382575332854449)
                ·
                  refine ⟨509043268786931499640837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 678724358382575332854449 509043268786931499640837)
                  ·
                    refine ⟨95445612897549656182657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 509043268786931499640837 95445612897549656182657)
                    ·
                      rfl

theorem cell23_557639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_557639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_557639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_557639 prefixEnd_557639 := by exact prefixLift 557639
  have htrace : WordTrace (prefixWord ++ tailWord_557639) baseStart_557639 baseEnd_557639 := by
    simpa [prefixWord, tailWord_557639, baseEnd_557639] using wordTrace_append hprefix tailTrace_557639
  have hstable : (prefixWord ++ tailWord_557639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557639).length < 2 ^ (prefixWord ++ tailWord_557639).sum := by decide
  have hdescent : baseEnd_557639 < baseStart_557639 := by decide
  rcases family_descends (prefixWord ++ tailWord_557639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
