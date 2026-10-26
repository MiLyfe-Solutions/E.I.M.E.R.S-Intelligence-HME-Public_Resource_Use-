import V185TrunkScan22Chunk147

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1323560 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1323560 : Nat := 118140960795 + 1323560 * 2 ^ 59
def prefixEnd_1323560 : Nat := 4983230072969 + 3 ^ 40 * 1323560 * 2
def baseEnd_1323560 : Nat := 453081636709964532742043

theorem tailTrace_1323560 : CollatzResearch.WordTrace tailWord_1323560 prefixEnd_1323560 453081636709964532742043 := by
  unfold tailWord_1323560
  simp only [CollatzResearch.WordTrace]
  refine ⟨24137099542487820448332067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32182799389983760597776089 24137099542487820448332067)
  ·
    refine ⟨36205649313731730672498101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24137099542487820448332067 36205649313731730672498101)
    ·
      refine ⟨3394279623162349750546697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36205649313731730672498101 3394279623162349750546697)
      ·
        refine ⟨2545709717371762312910023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3394279623162349750546697 2545709717371762312910023)
        ·
          refine ⟨3818564576057643469365035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2545709717371762312910023 3818564576057643469365035)
          ·
            refine ⟨5727846864086465204047553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818564576057643469365035 5727846864086465204047553)
            ·
              refine ⟨4295885148064848903035665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5727846864086465204047553 4295885148064848903035665)
              ·
                refine ⟨3221913861048636677276749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4295885148064848903035665 3221913861048636677276749)
                ·
                  refine ⟨1208217697893238753978781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3221913861048636677276749 1208217697893238753978781)
                  ·
                    refine ⟨453081636709964532742043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1208217697893238753978781 453081636709964532742043)
                    ·
                      rfl

theorem cell22_1323560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1323560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323560 prefixEnd_1323560 := by exact prefixLift 1323560
  have htrace : WordTrace (prefixWord ++ tailWord_1323560) baseStart_1323560 baseEnd_1323560 := by
    simpa [prefixWord, tailWord_1323560, baseEnd_1323560] using wordTrace_append hprefix tailTrace_1323560
  have hstable : (prefixWord ++ tailWord_1323560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323560).length < 2 ^ (prefixWord ++ tailWord_1323560).sum := by decide
  have hdescent : baseEnd_1323560 < baseStart_1323560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323590 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_1323590 : Nat := 118140960795 + 1323590 * 2 ^ 59
def prefixEnd_1323590 : Nat := 4983230072969 + 3 ^ 40 * 1323590 * 2
def baseEnd_1323590 : Nat := 151030635441018151497317

theorem tailTrace_1323590 : CollatzResearch.WordTrace tailWord_1323590 prefixEnd_1323590 151030635441018151497317 := by
  unfold tailWord_1323590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1508602914839592375633007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32183528849911304013504149 1508602914839592375633007)
  ·
    refine ⟨2262904372259388563449511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1508602914839592375633007 2262904372259388563449511)
    ·
      refine ⟨3394356558389082845174267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2262904372259388563449511 3394356558389082845174267)
      ·
        refine ⟨5091534837583624267761401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3394356558389082845174267 5091534837583624267761401)
        ·
          refine ⟨3818651128187718200821051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5091534837583624267761401 3818651128187718200821051)
          ·
            refine ⟨5727976692281577301231577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818651128187718200821051 5727976692281577301231577)
            ·
              refine ⟨4295982519211182975923683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5727976692281577301231577 4295982519211182975923683)
              ·
                refine ⟨6443973778816774463885525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4295982519211182975923683 6443973778816774463885525)
                ·
                  refine ⟨151030635441018151497317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6443973778816774463885525 151030635441018151497317)
                  ·
                    rfl

theorem cell22_1323590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_1323590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323590 prefixEnd_1323590 := by exact prefixLift 1323590
  have htrace : WordTrace (prefixWord ++ tailWord_1323590) baseStart_1323590 baseEnd_1323590 := by
    simpa [prefixWord, tailWord_1323590, baseEnd_1323590] using wordTrace_append hprefix tailTrace_1323590
  have hstable : (prefixWord ++ tailWord_1323590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323590).length < 2 ^ (prefixWord ++ tailWord_1323590).sum := by decide
  have hdescent : baseEnd_1323590 < baseStart_1323590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323631 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 1, 6]
def baseStart_1323631 : Nat := 118140960795 + 1323631 * 2 ^ 59
def prefixEnd_1323631 : Nat := 4983230072969 + 3 ^ 40 * 1323631 * 2
def baseEnd_1323631 : Nat := 453105941460944014216825

theorem tailTrace_1323631 : CollatzResearch.WordTrace tailWord_1323631 prefixEnd_1323631 453105941460944014216825 := by
  unfold tailWord_1323631
  simp only [CollatzResearch.WordTrace]
  refine ⟨48276788667718420022498747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32184525778478946681665831 48276788667718420022498747)
  ·
    refine ⟨72415183001577630033748121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48276788667718420022498747 72415183001577630033748121)
    ·
      refine ⟨54311387251183222525311091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72415183001577630033748121 54311387251183222525311091)
      ·
        refine ⟨81467080876774833787966637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54311387251183222525311091 81467080876774833787966637)
        ·
          refine ⟨30550155328790562670487489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81467080876774833787966637 30550155328790562670487489)
          ·
            refine ⟨22912616496592922002865617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30550155328790562670487489 22912616496592922002865617)
            ·
              refine ⟨17184462372444691502149213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22912616496592922002865617 17184462372444691502149213)
              ·
                refine ⟨6444173389666759313305955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17184462372444691502149213 6444173389666759313305955)
                ·
                  refine ⟨9666260084500138969958933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6444173389666759313305955 9666260084500138969958933)
                  ·
                    refine ⟨453105941460944014216825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9666260084500138969958933 453105941460944014216825)
                    ·
                      rfl

theorem cell22_1323631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_1323631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323631 prefixEnd_1323631 := by exact prefixLift 1323631
  have htrace : WordTrace (prefixWord ++ tailWord_1323631) baseStart_1323631 baseEnd_1323631 := by
    simpa [prefixWord, tailWord_1323631, baseEnd_1323631] using wordTrace_append hprefix tailTrace_1323631
  have hstable : (prefixWord ++ tailWord_1323631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323631).length < 2 ^ (prefixWord ++ tailWord_1323631).sum := by decide
  have hdescent : baseEnd_1323631 < baseStart_1323631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323646 : List Nat := [4, 2, 16]
def baseStart_1323646 : Nat := 118140960795 + 1323646 * 2 ^ 59
def prefixEnd_1323646 : Nat := 4983230072969 + 3 ^ 40 * 1323646 * 2
def baseEnd_1323646 : Nat := 207183848316181515817

theorem tailTrace_1323646 : CollatzResearch.WordTrace tailWord_1323646 prefixEnd_1323646 207183848316181515817 := by
  unfold tailWord_1323646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6034666970333009698036849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32184890508442718389529861 6034666970333009698036849)
  ·
    refine ⟨4526000227749757273527637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6034666970333009698036849 4526000227749757273527637)
    ·
      refine ⟨207183848316181515817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 4526000227749757273527637 207183848316181515817)
      ·
        rfl

theorem cell22_1323646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 16].length) (baseStart_1323646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323646 prefixEnd_1323646 := by exact prefixLift 1323646
  have htrace : WordTrace (prefixWord ++ tailWord_1323646) baseStart_1323646 baseEnd_1323646 := by
    simpa [prefixWord, tailWord_1323646, baseEnd_1323646] using wordTrace_append hprefix tailTrace_1323646
  have hstable : (prefixWord ++ tailWord_1323646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323646).length < 2 ^ (prefixWord ++ tailWord_1323646).sum := by decide
  have hdescent : baseEnd_1323646 < baseStart_1323646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323648 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 2, 4]
def baseStart_1323648 : Nat := 118140960795 + 1323648 * 2 ^ 59
def prefixEnd_1323648 : Nat := 4983230072969 + 3 ^ 40 * 1323648 * 2
def baseEnd_1323648 : Nat := 453111760908361636541773

theorem tailTrace_1323648 : CollatzResearch.WordTrace tailWord_1323648 prefixEnd_1323648 453111760908361636541773 := by
  unfold tailWord_1323648
  simp only [CollatzResearch.WordTrace]
  refine ⟨24138704354328415962933799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32184939139104554617245065 24138704354328415962933799)
  ·
    refine ⟨36208056531492623944400699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24138704354328415962933799 36208056531492623944400699)
    ·
      refine ⟨54312084797238935916601049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36208056531492623944400699 54312084797238935916601049)
      ·
        refine ⟨40734063597929201937450787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54312084797238935916601049 40734063597929201937450787)
        ·
          refine ⟨61101095396893802906176181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40734063597929201937450787 61101095396893802906176181)
          ·
            refine ⟨5728227693458794022454017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61101095396893802906176181 5728227693458794022454017)
            ·
              refine ⟨4296170770094095516840513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5728227693458794022454017 4296170770094095516840513)
              ·
                refine ⟨3222128077570571637630385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4296170770094095516840513 3222128077570571637630385)
                ·
                  refine ⟨2416596058177928728222789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3222128077570571637630385 2416596058177928728222789)
                  ·
                    refine ⟨453111760908361636541773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2416596058177928728222789 453111760908361636541773)
                    ·
                      rfl

theorem cell22_1323648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_1323648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323648 prefixEnd_1323648 := by exact prefixLift 1323648
  have htrace : WordTrace (prefixWord ++ tailWord_1323648) baseStart_1323648 baseEnd_1323648 := by
    simpa [prefixWord, tailWord_1323648, baseEnd_1323648] using wordTrace_append hprefix tailTrace_1323648
  have hstable : (prefixWord ++ tailWord_1323648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323648).length < 2 ^ (prefixWord ++ tailWord_1323648).sum := by decide
  have hdescent : baseEnd_1323648 < baseStart_1323648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323652 : List Nat := [2, 3, 2, 1, 3, 1, 4, 2, 4]
def baseStart_1323652 : Nat := 118140960795 + 1323652 * 2 ^ 59
def prefixEnd_1323652 : Nat := 4983230072969 + 3 ^ 40 * 1323652 * 2
def baseEnd_1323652 : Nat := 151037710063368986480587

theorem tailTrace_1323652 : CollatzResearch.WordTrace tailWord_1323652 prefixEnd_1323652 151037710063368986480587 := by
  unfold tailWord_1323652
  simp only [CollatzResearch.WordTrace]
  refine ⟨24138777300321170304506605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32185036400428227072675473 24138777300321170304506605)
  ·
    refine ⟨9052041487620438864189977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24138777300321170304506605 9052041487620438864189977)
    ·
      refine ⟨6789031115715329148142483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9052041487620438864189977 6789031115715329148142483)
      ·
        refine ⟨10183546673572993722213725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6789031115715329148142483 10183546673572993722213725)
        ·
          refine ⟨3818830002589872645830147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10183546673572993722213725 3818830002589872645830147)
          ·
            refine ⟨5728245003884808968745221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818830002589872645830147 5728245003884808968745221)
            ·
              refine ⟨1074045938228401681639729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5728245003884808968745221 1074045938228401681639729)
              ·
                refine ⟨805534453671301261229797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074045938228401681639729 805534453671301261229797)
                ·
                  refine ⟨151037710063368986480587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805534453671301261229797 151037710063368986480587)
                  ·
                    rfl

theorem cell22_1323652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_1323652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323652 prefixEnd_1323652 := by exact prefixLift 1323652
  have htrace : WordTrace (prefixWord ++ tailWord_1323652) baseStart_1323652 baseEnd_1323652 := by
    simpa [prefixWord, tailWord_1323652, baseEnd_1323652] using wordTrace_append hprefix tailTrace_1323652
  have hstable : (prefixWord ++ tailWord_1323652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323652).length < 2 ^ (prefixWord ++ tailWord_1323652).sum := by decide
  have hdescent : baseEnd_1323652 < baseStart_1323652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323680 : List Nat := [2, 1, 1, 4, 4, 1, 3, 6]
def baseStart_1323680 : Nat := 118140960795 + 1323680 * 2 ^ 59
def prefixEnd_1323680 : Nat := 4983230072969 + 3 ^ 40 * 1323680 * 2
def baseEnd_1323680 : Nat := 50346968351369357749075

theorem tailTrace_1323680 : CollatzResearch.WordTrace tailWord_1323680 prefixEnd_1323680 50346968351369357749075 := by
  unfold tailWord_1323680
  simp only [CollatzResearch.WordTrace]
  refine ⟨24139287922270450695516247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32185717229693934260688329 24139287922270450695516247)
  ·
    refine ⟨36208931883405676043274371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24139287922270450695516247 36208931883405676043274371)
    ·
      refine ⟨54313397825108514064911557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36208931883405676043274371 54313397825108514064911557)
      ·
        refine ⟨10183762092207846387170917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54313397825108514064911557 10183762092207846387170917)
        ·
          refine ⟨1909455392288971197594547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10183762092207846387170917 1909455392288971197594547)
          ·
            refine ⟨2864183088433456796391821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909455392288971197594547 2864183088433456796391821)
            ·
              refine ⟨1074068658162546298646933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2864183088433456796391821 1074068658162546298646933)
              ·
                refine ⟨50346968351369357749075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1074068658162546298646933 50346968351369357749075)
                ·
                  rfl

theorem cell22_1323680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 6].length) (baseStart_1323680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323680 prefixEnd_1323680 := by exact prefixLift 1323680
  have htrace : WordTrace (prefixWord ++ tailWord_1323680) baseStart_1323680 baseEnd_1323680 := by
    simpa [prefixWord, tailWord_1323680, baseEnd_1323680] using wordTrace_append hprefix tailTrace_1323680
  have hstable : (prefixWord ++ tailWord_1323680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323680).length < 2 ^ (prefixWord ++ tailWord_1323680).sum := by decide
  have hdescent : baseEnd_1323680 < baseStart_1323680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323708 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 7]
def baseStart_1323708 : Nat := 118140960795 + 1323708 * 2 ^ 59
def prefixEnd_1323708 : Nat := 4983230072969 + 3 ^ 40 * 1323708 * 2
def baseEnd_1323708 : Nat := 151044100044847160013863

theorem tailTrace_1323708 : CollatzResearch.WordTrace tailWord_1323708 prefixEnd_1323708 151044100044847160013863 := by
  unfold tailWord_1323708
  simp only [CollatzResearch.WordTrace]
  refine ⟨24139798544219731086525889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32186398058959641448701185 24139798544219731086525889)
  ·
    refine ⟨18104848908164798314894417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24139798544219731086525889 18104848908164798314894417)
    ·
      refine ⟨13578636681123598736170813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18104848908164798314894417 13578636681123598736170813)
      ·
        refine ⟨5091988755421349526064055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13578636681123598736170813 5091988755421349526064055)
        ·
          refine ⟨7637983133132024289096083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5091988755421349526064055 7637983133132024289096083)
          ·
            refine ⟨11456974699698036433644125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7637983133132024289096083 11456974699698036433644125)
            ·
              refine ⟨4296365512386763662616547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11456974699698036433644125 4296365512386763662616547)
              ·
                refine ⟨6444548268580145493924821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4296365512386763662616547 6444548268580145493924821)
                ·
                  refine ⟨151044100044847160013863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6444548268580145493924821 151044100044847160013863)
                  ·
                    rfl

theorem cell22_1323708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_1323708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323708 prefixEnd_1323708 := by exact prefixLift 1323708
  have htrace : WordTrace (prefixWord ++ tailWord_1323708) baseStart_1323708 baseEnd_1323708 := by
    simpa [prefixWord, tailWord_1323708, baseEnd_1323708] using wordTrace_append hprefix tailTrace_1323708
  have hstable : (prefixWord ++ tailWord_1323708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323708).length < 2 ^ (prefixWord ++ tailWord_1323708).sum := by decide
  have hdescent : baseEnd_1323708 < baseStart_1323708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323712 : List Nat := [2, 1, 1, 2, 4, 2, 2, 4, 1, 3]
def baseStart_1323712 : Nat := 118140960795 + 1323712 * 2 ^ 59
def prefixEnd_1323712 : Nat := 4983230072969 + 3 ^ 40 * 1323712 * 2
def baseEnd_1323712 : Nat := 453133669416286802941577

theorem tailTrace_1323712 : CollatzResearch.WordTrace tailWord_1323712 prefixEnd_1323712 453133669416286802941577 := by
  unfold tailWord_1323712
  simp only [CollatzResearch.WordTrace]
  refine ⟨24139871490212485428098695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32186495320283313904131593 24139871490212485428098695)
  ·
    refine ⟨36209807235318728142148043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24139871490212485428098695 36209807235318728142148043)
    ·
      refine ⟨54314710852978092213222065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36209807235318728142148043 54314710852978092213222065)
      ·
        refine ⟨40736033139733569159916549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54314710852978092213222065 40736033139733569159916549)
        ·
          refine ⟨7638006213700044217484353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40736033139733569159916549 7638006213700044217484353)
          ·
            refine ⟨5728504660275033163113265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7638006213700044217484353 5728504660275033163113265)
            ·
              refine ⟨4296378495206274872334949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5728504660275033163113265 4296378495206274872334949)
              ·
                refine ⟨805570967851176538562803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4296378495206274872334949 805570967851176538562803)
                ·
                  refine ⟨1208356451776764807844205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805570967851176538562803 1208356451776764807844205)
                  ·
                    refine ⟨453133669416286802941577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1208356451776764807844205 453133669416286802941577)
                    ·
                      rfl

theorem cell22_1323712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 1, 3].length) (baseStart_1323712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323712 prefixEnd_1323712 := by exact prefixLift 1323712
  have htrace : WordTrace (prefixWord ++ tailWord_1323712) baseStart_1323712 baseEnd_1323712 := by
    simpa [prefixWord, tailWord_1323712, baseEnd_1323712] using wordTrace_append hprefix tailTrace_1323712
  have hstable : (prefixWord ++ tailWord_1323712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323712).length < 2 ^ (prefixWord ++ tailWord_1323712).sum := by decide
  have hdescent : baseEnd_1323712 < baseStart_1323712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323718 : List Nat := [6, 1, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1323718 : Nat := 118140960795 + 1323718 * 2 ^ 59
def prefixEnd_1323718 : Nat := 4983230072969 + 3 ^ 40 * 1323718 * 2
def baseEnd_1323718 : Nat := 453135723338904787291559

theorem tailTrace_1323718 : CollatzResearch.WordTrace tailWord_1323718 prefixEnd_1323718 453135723338904787291559 := by
  unfold tailWord_1323718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1508748806825101058778619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32186641212268822587277205 1508748806825101058778619)
  ·
    refine ⟨2263123210237651588167929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1508748806825101058778619 2263123210237651588167929)
    ·
      refine ⟨1697342407678238691125947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2263123210237651588167929 1697342407678238691125947)
      ·
        refine ⟨2546013611517358036688921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1697342407678238691125947 2546013611517358036688921)
        ·
          refine ⟨1909510208638018527516691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2546013611517358036688921 1909510208638018527516691)
          ·
            refine ⟨2864265312957027791275037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909510208638018527516691 2864265312957027791275037)
            ·
              refine ⟨1074099492358885421728139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2864265312957027791275037 1074099492358885421728139)
              ·
                refine ⟨1611149238538328132592209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074099492358885421728139 1611149238538328132592209)
                ·
                  refine ⟨1208361928903746099444157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1611149238538328132592209 1208361928903746099444157)
                  ·
                    refine ⟨453135723338904787291559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1208361928903746099444157 453135723338904787291559)
                    ·
                      rfl

theorem cell22_1323718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1323718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323718 prefixEnd_1323718 := by exact prefixLift 1323718
  have htrace : WordTrace (prefixWord ++ tailWord_1323718) baseStart_1323718 baseEnd_1323718 := by
    simpa [prefixWord, tailWord_1323718, baseEnd_1323718] using wordTrace_append hprefix tailTrace_1323718
  have hstable : (prefixWord ++ tailWord_1323718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323718).length < 2 ^ (prefixWord ++ tailWord_1323718).sum := by decide
  have hdescent : baseEnd_1323718 < baseStart_1323718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323770 : List Nat := [3, 1, 1, 1, 1, 3, 2, 6, 4]
def baseStart_1323770 : Nat := 118140960795 + 1323770 * 2 ^ 59
def prefixEnd_1323770 : Nat := 4983230072969 + 3 ^ 40 * 1323770 * 2
def baseEnd_1323770 : Nat := 151051174667197994997133

theorem tailTrace_1323770 : CollatzResearch.WordTrace tailWord_1323770 prefixEnd_1323770 151051174667197994997133 := by
  unfold tailWord_1323770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12070464603553711690452191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32187905609476564507872509 12070464603553711690452191)
  ·
    refine ⟨18105696905330567535678287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12070464603553711690452191 18105696905330567535678287)
    ·
      refine ⟨27158545357995851303517431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18105696905330567535678287 27158545357995851303517431)
      ·
        refine ⟨40737818036993776955276147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27158545357995851303517431 40737818036993776955276147)
        ·
          refine ⟨61106727055490665432914221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40737818036993776955276147 61106727055490665432914221)
          ·
            refine ⟨22915022645808999537342833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61106727055490665432914221 22915022645808999537342833)
            ·
              refine ⟨17186266984356749653007125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22915022645808999537342833 17186266984356749653007125)
              ·
                refine ⟨805606264891722639984709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17186266984356749653007125 805606264891722639984709)
                ·
                  refine ⟨151051174667197994997133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805606264891722639984709 151051174667197994997133)
                  ·
                    rfl

theorem cell22_1323770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_1323770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323770 prefixEnd_1323770 := by exact prefixLift 1323770
  have htrace : WordTrace (prefixWord ++ tailWord_1323770) baseStart_1323770 baseEnd_1323770 := by
    simpa [prefixWord, tailWord_1323770, baseEnd_1323770] using wordTrace_append hprefix tailTrace_1323770
  have hstable : (prefixWord ++ tailWord_1323770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323770).length < 2 ^ (prefixWord ++ tailWord_1323770).sum := by decide
  have hdescent : baseEnd_1323770 < baseStart_1323770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323821 : List Nat := [1, 5, 3, 2, 1, 1, 1, 4, 4]
def baseStart_1323821 : Nat := 118140960795 + 1323821 * 2 ^ 59
def prefixEnd_1323821 : Nat := 4983230072969 + 3 ^ 40 * 1323821 * 2
def baseEnd_1323821 : Nat := 151056994114615617322081

theorem tailTrace_1323821 : CollatzResearch.WordTrace tailWord_1323821 prefixEnd_1323821 151056994114615617322081 := by
  unfold tailWord_1323821
  simp only [CollatzResearch.WordTrace]
  refine ⟨48283718537030082471915317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32189145691353388314610211 48283718537030082471915317)
  ·
    refine ⟨4526598612846570231742061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48283718537030082471915317 4526598612846570231742061)
    ·
      refine ⟨1697474479817463836903273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4526598612846570231742061 1697474479817463836903273)
      ·
        refine ⟨1273105859863097877677455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1697474479817463836903273 1273105859863097877677455)
        ·
          refine ⟨1909658789794646816516183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1273105859863097877677455 1909658789794646816516183)
          ·
            refine ⟨2864488184691970224774275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909658789794646816516183 2864488184691970224774275)
            ·
              refine ⟨4296732277037955337161413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2864488184691970224774275 4296732277037955337161413)
              ·
                refine ⟨805637301944616625717765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4296732277037955337161413 805637301944616625717765)
                ·
                  refine ⟨151056994114615617322081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805637301944616625717765 151056994114615617322081)
                  ·
                    rfl

theorem cell22_1323821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_1323821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323821 prefixEnd_1323821 := by exact prefixLift 1323821
  have htrace : WordTrace (prefixWord ++ tailWord_1323821) baseStart_1323821 baseEnd_1323821 := by
    simpa [prefixWord, tailWord_1323821, baseEnd_1323821] using wordTrace_append hprefix tailTrace_1323821
  have hstable : (prefixWord ++ tailWord_1323821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323821).length < 2 ^ (prefixWord ++ tailWord_1323821).sum := by decide
  have hdescent : baseEnd_1323821 < baseStart_1323821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323875 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 2, 5]
def baseStart_1323875 : Nat := 118140960795 + 1323875 * 2 ^ 59
def prefixEnd_1323875 : Nat := 4983230072969 + 3 ^ 40 * 1323875 * 2
def baseEnd_1323875 : Nat := 453189467647408711116077

theorem tailTrace_1323875 : CollatzResearch.WordTrace tailWord_1323875 prefixEnd_1323875 453189467647408711116077 := by
  unfold tailWord_1323875
  simp only [CollatzResearch.WordTrace]
  refine ⟨48285688078834449694381079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32190458719222966462920719 48285688078834449694381079)
  ·
    refine ⟨72428532118251674541571619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48285688078834449694381079 72428532118251674541571619)
    ·
      refine ⟨108642798177377511812357429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72428532118251674541571619 108642798177377511812357429)
      ·
        refine ⟨10185262329129141732408509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108642798177377511812357429 10185262329129141732408509)
        ·
          refine ⟨3819473373423428149653191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10185262329129141732408509 3819473373423428149653191)
          ·
            refine ⟨5729210060135142224479787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3819473373423428149653191 5729210060135142224479787)
            ·
              refine ⟨8593815090202713336719681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5729210060135142224479787 8593815090202713336719681)
              ·
                refine ⟨6445361317652035002539761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8593815090202713336719681 6445361317652035002539761)
                ·
                  refine ⟨4834020988239026251904821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6445361317652035002539761 4834020988239026251904821)
                  ·
                    refine ⟨453189467647408711116077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4834020988239026251904821 453189467647408711116077)
                    ·
                      rfl

theorem cell22_1323875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 5].length) (baseStart_1323875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323875 prefixEnd_1323875 := by exact prefixLift 1323875
  have htrace : WordTrace (prefixWord ++ tailWord_1323875) baseStart_1323875 baseEnd_1323875 := by
    simpa [prefixWord, tailWord_1323875, baseEnd_1323875] using wordTrace_append hprefix tailTrace_1323875
  have hstable : (prefixWord ++ tailWord_1323875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323875).length < 2 ^ (prefixWord ++ tailWord_1323875).sum := by decide
  have hdescent : baseEnd_1323875 < baseStart_1323875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323890 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_1323890 : Nat := 118140960795 + 1323890 * 2 ^ 59
def prefixEnd_1323890 : Nat := 4983230072969 + 3 ^ 40 * 1323890 * 2
def baseEnd_1323890 : Nat := 453194602453953671991031

theorem tailTrace_1323890 : CollatzResearch.WordTrace tailWord_1323890 prefixEnd_1323890 453194602453953671991031 := by
  unfold tailWord_1323890
  simp only [CollatzResearch.WordTrace]
  refine ⟨12071558793445026814044281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32190823449186738170784749 12071558793445026814044281)
  ·
    refine ⟨9053669095083770110533211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12071558793445026814044281 9053669095083770110533211)
    ·
      refine ⟨13580503642625655165799817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9053669095083770110533211 13580503642625655165799817)
      ·
        refine ⟨10185377731969241374349863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13580503642625655165799817 10185377731969241374349863)
        ·
          refine ⟨15278066597953862061524795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10185377731969241374349863 15278066597953862061524795)
          ·
            refine ⟨22917099896930793092287193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15278066597953862061524795 22917099896930793092287193)
            ·
              refine ⟨17187824922698094819215395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22917099896930793092287193 17187824922698094819215395)
              ·
                refine ⟨25781737384047142228823093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17187824922698094819215395 25781737384047142228823093)
                ·
                  refine ⟨2417037879754419583952165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25781737384047142228823093 2417037879754419583952165)
                  ·
                    refine ⟨453194602453953671991031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2417037879754419583952165 453194602453953671991031)
                    ·
                      rfl

theorem cell22_1323890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_1323890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323890 prefixEnd_1323890 := by exact prefixLift 1323890
  have htrace : WordTrace (prefixWord ++ tailWord_1323890) baseStart_1323890 baseEnd_1323890 := by
    simpa [prefixWord, tailWord_1323890, baseEnd_1323890] using wordTrace_append hprefix tailTrace_1323890
  have hstable : (prefixWord ++ tailWord_1323890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323890).length < 2 ^ (prefixWord ++ tailWord_1323890).sum := by decide
  have hdescent : baseEnd_1323890 < baseStart_1323890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323907 : List Nat := [1, 1, 1, 3, 4, 1, 4, 2, 1, 4]
def baseStart_1323907 : Nat := 118140960795 + 1323907 * 2 ^ 59
def prefixEnd_1323907 : Nat := 4983230072969 + 3 ^ 40 * 1323907 * 2
def baseEnd_1323907 : Nat := 453200421901371294315979

theorem tailTrace_1323907 : CollatzResearch.WordTrace tailWord_1323907 prefixEnd_1323907 453200421901371294315979 := by
  unfold tailWord_1323907
  simp only [CollatzResearch.WordTrace]
  refine ⟨48286855214718519159545975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32191236809812346106363983 48286855214718519159545975)
  ·
    refine ⟨72430282822077778739318963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48286855214718519159545975 72430282822077778739318963)
    ·
      refine ⟨108645424233116668108978445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72430282822077778739318963 108645424233116668108978445)
      ·
        refine ⟨40742034087418750540866917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108645424233116668108978445 40742034087418750540866917)
        ·
          refine ⟨7639131391391015726412547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40742034087418750540866917 7639131391391015726412547)
          ·
            refine ⟨11458697087086523589618821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7639131391391015726412547 11458697087086523589618821)
            ·
              refine ⟨2148505703828723173053529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11458697087086523589618821 2148505703828723173053529)
              ·
                refine ⟨1611379277871542379790147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2148505703828723173053529 1611379277871542379790147)
                ·
                  refine ⟨2417068916807313569685221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611379277871542379790147 2417068916807313569685221)
                  ·
                    refine ⟨453200421901371294315979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2417068916807313569685221 453200421901371294315979)
                    ·
                      rfl

theorem cell22_1323907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 4].length) (baseStart_1323907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323907 prefixEnd_1323907 := by exact prefixLift 1323907
  have htrace : WordTrace (prefixWord ++ tailWord_1323907) baseStart_1323907 baseEnd_1323907 := by
    simpa [prefixWord, tailWord_1323907, baseEnd_1323907] using wordTrace_append hprefix tailTrace_1323907
  have hstable : (prefixWord ++ tailWord_1323907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323907).length < 2 ^ (prefixWord ++ tailWord_1323907).sum := by decide
  have hdescent : baseEnd_1323907 < baseStart_1323907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323958 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1323958 : Nat := 118140960795 + 1323958 * 2 ^ 59
def prefixEnd_1323958 : Nat := 4983230072969 + 3 ^ 40 * 1323958 * 2
def baseEnd_1323958 : Nat := 453217880243624161290823

theorem tailTrace_1323958 : CollatzResearch.WordTrace tailWord_1323958 prefixEnd_1323958 453217880243624161290823 := by
  unfold tailWord_1323958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3018044708595859679353283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32192476891689169913101685 3018044708595859679353283)
  ·
    refine ⟨4527067062893789519029925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3018044708595859679353283 4527067062893789519029925)
    ·
      refine ⟨848825074292585534818111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4527067062893789519029925 848825074292585534818111)
      ·
        refine ⟨1273237611438878302227167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848825074292585534818111 1273237611438878302227167)
        ·
          refine ⟨1909856417158317453340751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1273237611438878302227167 1909856417158317453340751)
          ·
            refine ⟨2864784625737476180011127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909856417158317453340751 2864784625737476180011127)
            ·
              refine ⟨4297176938606214270016691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2864784625737476180011127 4297176938606214270016691)
              ·
                refine ⟨6445765407909321405025037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4297176938606214270016691 6445765407909321405025037)
                ·
                  refine ⟨2417162027965995526884389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6445765407909321405025037 2417162027965995526884389)
                  ·
                    refine ⟨453217880243624161290823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2417162027965995526884389 453217880243624161290823)
                    ·
                      rfl

theorem cell22_1323958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1323958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323958 prefixEnd_1323958 := by exact prefixLift 1323958
  have htrace : WordTrace (prefixWord ++ tailWord_1323958) baseStart_1323958 baseEnd_1323958 := by
    simpa [prefixWord, tailWord_1323958, baseEnd_1323958] using wordTrace_append hprefix tailTrace_1323958
  have hstable : (prefixWord ++ tailWord_1323958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323958).length < 2 ^ (prefixWord ++ tailWord_1323958).sum := by decide
  have hdescent : baseEnd_1323958 < baseStart_1323958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323997 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1323997 : Nat := 118140960795 + 1323997 * 2 ^ 59
def prefixEnd_1323997 : Nat := 4983230072969 + 3 ^ 40 * 1323997 * 2
def baseEnd_1323997 : Nat := 453231230740641059565703

theorem tailTrace_1323997 : CollatzResearch.WordTrace tailWord_1323997 prefixEnd_1323997 453231230740641059565703 := by
  unfold tailWord_1323997
  simp only [CollatzResearch.WordTrace]
  refine ⟨48290137784392464530322245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32193425189594976353548163 48290137784392464530322245)
  ·
    refine ⟨9054400834573587099435421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48290137784392464530322245 9054400834573587099435421)
    ·
      refine ⟨3395400312965095162288283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9054400834573587099435421 3395400312965095162288283)
      ·
        refine ⟨5093100469447642743432425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3395400312965095162288283 5093100469447642743432425)
        ·
          refine ⟨3819825352085732057574319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5093100469447642743432425 3819825352085732057574319)
          ·
            refine ⟨5729738028128598086361479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3819825352085732057574319 5729738028128598086361479)
            ·
              refine ⟨8594607042192897129542219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5729738028128598086361479 8594607042192897129542219)
              ·
                refine ⟨12891910563289345694313329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8594607042192897129542219 12891910563289345694313329)
                ·
                  refine ⟨9668932922467009270734997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12891910563289345694313329 9668932922467009270734997)
                  ·
                    refine ⟨453231230740641059565703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9668932922467009270734997 453231230740641059565703)
                    ·
                      rfl

theorem cell22_1323997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1323997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323997 prefixEnd_1323997 := by exact prefixLift 1323997
  have htrace : WordTrace (prefixWord ++ tailWord_1323997) baseStart_1323997 baseEnd_1323997 := by
    simpa [prefixWord, tailWord_1323997, baseEnd_1323997] using wordTrace_append hprefix tailTrace_1323997
  have hstable : (prefixWord ++ tailWord_1323997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323997).length < 2 ^ (prefixWord ++ tailWord_1323997).sum := by decide
  have hdescent : baseEnd_1323997 < baseStart_1323997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324050 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1324050 : Nat := 118140960795 + 1324050 * 2 ^ 59
def prefixEnd_1324050 : Nat := 4983230072969 + 3 ^ 40 * 1324050 * 2
def baseEnd_1324050 : Nat := 453249373723766587990541

theorem tailTrace_1324050 : CollatzResearch.WordTrace tailWord_1324050 prefixEnd_1324050 453249373723766587990541 := by
  unfold tailWord_1324050
  simp only [CollatzResearch.WordTrace]
  refine ⟨12073017713300113645500401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32194713902133636388001069 12073017713300113645500401)
  ·
    refine ⟨9054763284975085234125301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12073017713300113645500401 9054763284975085234125301)
    ·
      refine ⟨848884057966414240699247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9054763284975085234125301 848884057966414240699247)
      ·
        refine ⟨1273326086949621361048871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848884057966414240699247 1273326086949621361048871)
        ·
          refine ⟨1909989130424432041573307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1273326086949621361048871 1909989130424432041573307)
          ·
            refine ⟨2864983695636648062359961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909989130424432041573307 2864983695636648062359961)
            ·
              refine ⟨2148737771727486046769971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2864983695636648062359961 2148737771727486046769971)
              ·
                refine ⟨3223106657591229070154957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2148737771727486046769971 3223106657591229070154957)
                ·
                  refine ⟨1208664996596710901308109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3223106657591229070154957 1208664996596710901308109)
                  ·
                    refine ⟨453249373723766587990541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1208664996596710901308109 453249373723766587990541)
                    ·
                      rfl

theorem cell22_1324050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1324050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324050 prefixEnd_1324050 := by exact prefixLift 1324050
  have htrace : WordTrace (prefixWord ++ tailWord_1324050) baseStart_1324050 baseEnd_1324050 := by
    simpa [prefixWord, tailWord_1324050, baseEnd_1324050] using wordTrace_append hprefix tailTrace_1324050
  have hstable : (prefixWord ++ tailWord_1324050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324050).length < 2 ^ (prefixWord ++ tailWord_1324050).sum := by decide
  have hdescent : baseEnd_1324050 < baseStart_1324050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324087 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 2, 4]
def baseStart_1324087 : Nat := 118140960795 + 1324087 * 2 ^ 59
def prefixEnd_1324087 : Nat := 4983230072969 + 3 ^ 40 * 1324087 * 2
def baseEnd_1324087 : Nat := 453262039579910824815427

theorem tailTrace_1324087 : CollatzResearch.WordTrace tailWord_1324087 prefixEnd_1324087 453262039579910824815427 := by
  unfold tailWord_1324087
  simp only [CollatzResearch.WordTrace]
  refine ⟨48293420354066409901098515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32195613569377606600732343 48293420354066409901098515)
  ·
    refine ⟨72440130531099614851647773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48293420354066409901098515 72440130531099614851647773)
    ·
      refine ⟨27165048949162355569367915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72440130531099614851647773 27165048949162355569367915)
      ·
        refine ⟨40747573423743533354051873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27165048949162355569367915 40747573423743533354051873)
        ·
          refine ⟨30560680067807650015538905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40747573423743533354051873 30560680067807650015538905)
          ·
            refine ⟨22920510050855737511654179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30560680067807650015538905 22920510050855737511654179)
            ·
              refine ⟨34380765076283606267481269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22920510050855737511654179 34380765076283606267481269)
              ·
                refine ⟨3223196725901588087576369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34380765076283606267481269 3223196725901588087576369)
                ·
                  refine ⟨2417397544426191065682277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3223196725901588087576369 2417397544426191065682277)
                  ·
                    refine ⟨453262039579910824815427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2417397544426191065682277 453262039579910824815427)
                    ·
                      rfl

theorem cell22_1324087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_1324087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324087 prefixEnd_1324087 := by exact prefixLift 1324087
  have htrace : WordTrace (prefixWord ++ tailWord_1324087) baseStart_1324087 baseEnd_1324087 := by
    simpa [prefixWord, tailWord_1324087, baseEnd_1324087] using wordTrace_append hprefix tailTrace_1324087
  have hstable : (prefixWord ++ tailWord_1324087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324087).length < 2 ^ (prefixWord ++ tailWord_1324087).sum := by decide
  have hdescent : baseEnd_1324087 < baseStart_1324087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324089 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 4, 3]
def baseStart_1324089 : Nat := 118140960795 + 1324089 * 2 ^ 59
def prefixEnd_1324089 : Nat := 4983230072969 + 3 ^ 40 * 1324089 * 2
def baseEnd_1324089 : Nat := 453262724220783486265421

theorem tailTrace_1324089 : CollatzResearch.WordTrace tailWord_1324089 prefixEnd_1324089 453262724220783486265421 := by
  unfold tailWord_1324089
  simp only [CollatzResearch.WordTrace]
  refine ⟨48293493300059164242671321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32195662200039442828447547 48293493300059164242671321)
  ·
    refine ⟨36220119975044373182003491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48293493300059164242671321 36220119975044373182003491)
    ·
      refine ⟨54330179962566559773005237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36220119975044373182003491 54330179962566559773005237)
      ·
        refine ⟨5093454371490614978719241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54330179962566559773005237 5093454371490614978719241)
        ·
          refine ⟨3820090778617961234039431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5093454371490614978719241 3820090778617961234039431)
          ·
            refine ⟨5730136167926941851059147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3820090778617961234039431 5730136167926941851059147)
            ·
              refine ⟨8595204251890412776588721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5730136167926941851059147 8595204251890412776588721)
              ·
                refine ⟨6446403188917809582441541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8595204251890412776588721 6446403188917809582441541)
                ·
                  refine ⟨1208700597922089296707789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6446403188917809582441541 1208700597922089296707789)
                  ·
                    refine ⟨453262724220783486265421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1208700597922089296707789 453262724220783486265421)
                    ·
                      rfl

theorem cell22_1324089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 3].length) (baseStart_1324089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324089 prefixEnd_1324089 := by exact prefixLift 1324089
  have htrace : WordTrace (prefixWord ++ tailWord_1324089) baseStart_1324089 baseEnd_1324089 := by
    simpa [prefixWord, tailWord_1324089, baseEnd_1324089] using wordTrace_append hprefix tailTrace_1324089
  have hstable : (prefixWord ++ tailWord_1324089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324089).length < 2 ^ (prefixWord ++ tailWord_1324089).sum := by decide
  have hdescent : baseEnd_1324089 < baseStart_1324089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324151 : List Nat := [1, 1, 3, 1, 1, 4, 2, 5, 1, 3]
def baseStart_1324151 : Nat := 118140960795 + 1324151 * 2 ^ 59
def prefixEnd_1324151 : Nat := 4983230072969 + 3 ^ 40 * 1324151 * 2
def baseEnd_1324151 : Nat := 453283948087835991215231

theorem tailTrace_1324151 : CollatzResearch.WordTrace tailWord_1324151 prefixEnd_1324151 453283948087835991215231 := by
  unfold tailWord_1324151
  simp only [CollatzResearch.WordTrace]
  refine ⟨48295754625834548831428307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32197169750556365887618871 48295754625834548831428307)
  ·
    refine ⟨72443631938751823247142461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48295754625834548831428307 72443631938751823247142461)
    ·
      refine ⟨27166361977031933717678423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72443631938751823247142461 27166361977031933717678423)
      ·
        refine ⟨40749542965547900576517635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27166361977031933717678423 40749542965547900576517635)
        ·
          refine ⟨61124314448321850864776453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40749542965547900576517635 61124314448321850864776453)
          ·
            refine ⟨11460808959060347037145585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61124314448321850864776453 11460808959060347037145585)
            ·
              refine ⟨8595606719295260277859189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11460808959060347037145585 8595606719295260277859189)
              ·
                refine ⟨805838129933930651049299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8595606719295260277859189 805838129933930651049299)
                ·
                  refine ⟨1208757194900895976573949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805838129933930651049299 1208757194900895976573949)
                  ·
                    refine ⟨453283948087835991215231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1208757194900895976573949 453283948087835991215231)
                    ·
                      rfl

theorem cell22_1324151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_1324151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324151 prefixEnd_1324151 := by exact prefixLift 1324151
  have htrace : WordTrace (prefixWord ++ tailWord_1324151) baseStart_1324151 baseEnd_1324151 := by
    simpa [prefixWord, tailWord_1324151, baseEnd_1324151] using wordTrace_append hprefix tailTrace_1324151
  have hstable : (prefixWord ++ tailWord_1324151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324151).length < 2 ^ (prefixWord ++ tailWord_1324151).sum := by decide
  have hdescent : baseEnd_1324151 < baseStart_1324151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324164 : List Nat := [2, 3, 2, 1, 2, 2, 1, 4, 5]
def baseStart_1324164 : Nat := 118140960795 + 1324164 * 2 ^ 59
def prefixEnd_1324164 : Nat := 4983230072969 + 3 ^ 40 * 1324164 * 2
def baseEnd_1324164 : Nat := 151096132751169430213397

theorem tailTrace_1324164 : CollatzResearch.WordTrace tailWord_1324164 prefixEnd_1324164 151096132751169430213397 := by
  unfold tailWord_1324164
  simp only [CollatzResearch.WordTrace]
  refine ⟨24148114387393726025825773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32197485849858301367767697 24148114387393726025825773)
  ·
    refine ⟨9055542895272647259684665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24148114387393726025825773 9055542895272647259684665)
    ·
      refine ⟨6791657171454485444763499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9055542895272647259684665 6791657171454485444763499)
      ·
        refine ⟨10187485757181728167145249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6791657171454485444763499 10187485757181728167145249)
        ·
          refine ⟨7640614317886296125358937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10187485757181728167145249 7640614317886296125358937)
          ·
            refine ⟨5730460738414722094019203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7640614317886296125358937 5730460738414722094019203)
            ·
              refine ⟨8595691107622083141028805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5730460738414722094019203 8595691107622083141028805)
              ·
                refine ⟨1611692082679140588942901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8595691107622083141028805 1611692082679140588942901)
                ·
                  refine ⟨151096132751169430213397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1611692082679140588942901 151096132751169430213397)
                  ·
                    rfl

theorem cell22_1324164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_1324164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324164 prefixEnd_1324164 := by exact prefixLift 1324164
  have htrace : WordTrace (prefixWord ++ tailWord_1324164) baseStart_1324164 baseEnd_1324164 := by
    simpa [prefixWord, tailWord_1324164, baseEnd_1324164] using wordTrace_append hprefix tailTrace_1324164
  have hstable : (prefixWord ++ tailWord_1324164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324164).length < 2 ^ (prefixWord ++ tailWord_1324164).sum := by decide
  have hdescent : baseEnd_1324164 < baseStart_1324164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324211 : List Nat := [1, 1, 1, 2, 3, 2, 6, 1, 1, 4]
def baseStart_1324211 : Nat := 118140960795 + 1324211 * 2 ^ 59
def prefixEnd_1324211 : Nat := 4983230072969 + 3 ^ 40 * 1324211 * 2
def baseEnd_1324211 : Nat := 453304487314015834715047

theorem tailTrace_1324211 : CollatzResearch.WordTrace tailWord_1324211 prefixEnd_1324211 453304487314015834715047 := by
  unfold tailWord_1324211
  simp only [CollatzResearch.WordTrace]
  refine ⟨48297943005617179078612487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32198628670411452719074991 48297943005617179078612487)
  ·
    refine ⟨72446914508425768617918731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48297943005617179078612487 72446914508425768617918731)
    ·
      refine ⟨108670371762638652926878097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72446914508425768617918731 108670371762638652926878097)
      ·
        refine ⟨81502778821978989695158573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108670371762638652926878097 81502778821978989695158573)
        ·
          refine ⟨30563542058242121135684465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81502778821978989695158573 30563542058242121135684465)
          ·
            refine ⟨22922656543681590851763349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30563542058242121135684465 22922656543681590851763349)
            ·
              refine ⟨1074499525485074571176407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22922656543681590851763349 1074499525485074571176407)
              ·
                refine ⟨1611749288227611856764611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074499525485074571176407 1611749288227611856764611)
                ·
                  refine ⟨2417623932341417785146917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611749288227611856764611 2417623932341417785146917)
                  ·
                    refine ⟨453304487314015834715047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2417623932341417785146917 453304487314015834715047)
                    ·
                      rfl

theorem cell22_1324211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 1, 4].length) (baseStart_1324211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324211 prefixEnd_1324211 := by exact prefixLift 1324211
  have htrace : WordTrace (prefixWord ++ tailWord_1324211) baseStart_1324211 baseEnd_1324211 := by
    simpa [prefixWord, tailWord_1324211, baseEnd_1324211] using wordTrace_append hprefix tailTrace_1324211
  have hstable : (prefixWord ++ tailWord_1324211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324211).length < 2 ^ (prefixWord ++ tailWord_1324211).sum := by decide
  have hdescent : baseEnd_1324211 < baseStart_1324211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324271 : List Nat := [1, 1, 2, 1, 8, 1, 8]
def baseStart_1324271 : Nat := 118140960795 + 1324271 * 2 ^ 59
def prefixEnd_1324271 : Nat := 4983230072969 + 3 ^ 40 * 1324271 * 2
def baseEnd_1324271 : Nat := 16789815797785025119069

theorem tailTrace_1324271 : CollatzResearch.WordTrace tailWord_1324271 prefixEnd_1324271 16789815797785025119069 := by
  unfold tailWord_1324271
  simp only [CollatzResearch.WordTrace]
  refine ⟨48300131385399809325796667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32200087590266539550531111 48300131385399809325796667)
  ·
    refine ⟨72450197078099713988695001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48300131385399809325796667 72450197078099713988695001)
    ·
      refine ⟨54337647808574785491521251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72450197078099713988695001 54337647808574785491521251)
      ·
        refine ⟨81506471712862178237281877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54337647808574785491521251 81506471712862178237281877)
        ·
          refine ⟨955153965385103651218147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 81506471712862178237281877 955153965385103651218147)
          ·
            refine ⟨1432730948077655476827221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955153965385103651218147 1432730948077655476827221)
            ·
              refine ⟨16789815797785025119069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1432730948077655476827221 16789815797785025119069)
              ·
                rfl

theorem cell22_1324271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 8].length) (baseStart_1324271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324271 prefixEnd_1324271 := by exact prefixLift 1324271
  have htrace : WordTrace (prefixWord ++ tailWord_1324271) baseStart_1324271 baseEnd_1324271 := by
    simpa [prefixWord, tailWord_1324271, baseEnd_1324271] using wordTrace_append hprefix tailTrace_1324271
  have hstable : (prefixWord ++ tailWord_1324271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324271).length < 2 ^ (prefixWord ++ tailWord_1324271).sum := by decide
  have hdescent : baseEnd_1324271 < baseStart_1324271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324333 : List Nat := [1, 5, 3, 1, 1, 1, 1, 4, 5]
def baseStart_1324333 : Nat := 118140960795 + 1324333 * 2 ^ 59
def prefixEnd_1324333 : Nat := 4983230072969 + 3 ^ 40 * 1324333 * 2
def baseEnd_1324333 : Nat := 151115416802416061054891

theorem tailTrace_1324333 : CollatzResearch.WordTrace tailWord_1324333 prefixEnd_1324333 151115416802416061054891 := by
  unfold tailWord_1324333
  simp only [CollatzResearch.WordTrace]
  refine ⟨48302392711175193914553653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32201595140783462609702435 48302392711175193914553653)
  ·
    refine ⟨4528349316672674429489405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48302392711175193914553653 4528349316672674429489405)
    ·
      refine ⟨1698130993752252911058527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4528349316672674429489405 1698130993752252911058527)
      ·
        refine ⟨2547196490628379366587791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1698130993752252911058527 2547196490628379366587791)
        ·
          refine ⟨3820794735942569049881687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547196490628379366587791 3820794735942569049881687)
          ·
            refine ⟨5731192103913853574822531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3820794735942569049881687 5731192103913853574822531)
            ·
              refine ⟨8596788155870780362233797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5731192103913853574822531 8596788155870780362233797)
              ·
                refine ⟨1611897779225771317918837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8596788155870780362233797 1611897779225771317918837)
                ·
                  refine ⟨151115416802416061054891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1611897779225771317918837 151115416802416061054891)
                  ·
                    rfl

theorem cell22_1324333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_1324333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324333 prefixEnd_1324333 := by exact prefixLift 1324333
  have htrace : WordTrace (prefixWord ++ tailWord_1324333) baseStart_1324333 baseEnd_1324333 := by
    simpa [prefixWord, tailWord_1324333, baseEnd_1324333] using wordTrace_append hprefix tailTrace_1324333
  have hstable : (prefixWord ++ tailWord_1324333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324333).length < 2 ^ (prefixWord ++ tailWord_1324333).sum := by decide
  have hdescent : baseEnd_1324333 < baseStart_1324333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324337 : List Nat := [1, 2, 2, 3, 3, 3, 2, 2, 1, 3]
def baseStart_1324337 : Nat := 118140960795 + 1324337 * 2 ^ 59
def prefixEnd_1324337 : Nat := 4983230072969 + 3 ^ 40 * 1324337 * 2
def baseEnd_1324337 : Nat := 453347619688993506064661

theorem tailTrace_1324337 : CollatzResearch.WordTrace tailWord_1324337 prefixEnd_1324337 453347619688993506064661 := by
  unfold tailWord_1324337
  simp only [CollatzResearch.WordTrace]
  refine ⟨48302538603160702597699265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32201692402107135065132843 48302538603160702597699265)
  ·
    refine ⟨36226903952370526948274449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48302538603160702597699265 36226903952370526948274449)
    ·
      refine ⟨27170177964277895211205837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36226903952370526948274449 27170177964277895211205837)
      ·
        refine ⟨10188816736604210704202189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27170177964277895211205837 10188816736604210704202189)
        ·
          refine ⟨3820806276226579014075821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10188816736604210704202189 3820806276226579014075821)
          ·
            refine ⟨1432802353584967130278433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3820806276226579014075821 1432802353584967130278433)
            ·
              refine ⟨1074601765188725347708825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1432802353584967130278433 1074601765188725347708825)
              ·
                refine ⟨805951323891544010781619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074601765188725347708825 805951323891544010781619)
                ·
                  refine ⟨1208926985837316016172429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805951323891544010781619 1208926985837316016172429)
                  ·
                    refine ⟨453347619688993506064661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1208926985837316016172429 453347619688993506064661)
                    ·
                      rfl

theorem cell22_1324337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_1324337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324337 prefixEnd_1324337 := by exact prefixLift 1324337
  have htrace : WordTrace (prefixWord ++ tailWord_1324337) baseStart_1324337 baseEnd_1324337 := by
    simpa [prefixWord, tailWord_1324337, baseEnd_1324337] using wordTrace_append hprefix tailTrace_1324337
  have hstable : (prefixWord ++ tailWord_1324337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324337).length < 2 ^ (prefixWord ++ tailWord_1324337).sum := by decide
  have hdescent : baseEnd_1324337 < baseStart_1324337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324344 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 6]
def baseStart_1324344 : Nat := 118140960795 + 1324344 * 2 ^ 59
def prefixEnd_1324344 : Nat := 4983230072969 + 3 ^ 40 * 1324344 * 2
def baseEnd_1324344 : Nat := 151116671977349273713213

theorem tailTrace_1324344 : CollatzResearch.WordTrace tailWord_1324344 prefixEnd_1324344 151116671977349273713213 := by
  unfold tailWord_1324344
  simp only [CollatzResearch.WordTrace]
  refine ⟨24151396957067671396602043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32201862609423561862136057 24151396957067671396602043)
  ·
    refine ⟨36227095435601507094903065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24151396957067671396602043 36227095435601507094903065)
    ·
      refine ⟨27170321576701130321177299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36227095435601507094903065 27170321576701130321177299)
      ·
        refine ⟨40755482365051695481765949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27170321576701130321177299 40755482365051695481765949)
        ·
          refine ⟨15283305886894385805662231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40755482365051695481765949 15283305886894385805662231)
          ·
            refine ⟨22924958830341578708493347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15283305886894385805662231 22924958830341578708493347)
            ·
              refine ⟨34387438245512368062740021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22924958830341578708493347 34387438245512368062740021)
              ·
                refine ⟨3223822335516784505881877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34387438245512368062740021 3223822335516784505881877)
                ·
                  refine ⟨151116671977349273713213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3223822335516784505881877 151116671977349273713213)
                  ·
                    rfl

theorem cell22_1324344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_1324344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324344 prefixEnd_1324344 := by exact prefixLift 1324344
  have htrace : WordTrace (prefixWord ++ tailWord_1324344) baseStart_1324344 baseEnd_1324344 := by
    simpa [prefixWord, tailWord_1324344, baseEnd_1324344] using wordTrace_append hprefix tailTrace_1324344
  have hstable : (prefixWord ++ tailWord_1324344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324344).length < 2 ^ (prefixWord ++ tailWord_1324344).sum := by decide
  have hdescent : baseEnd_1324344 < baseStart_1324344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324376 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 4, 3]
def baseStart_1324376 : Nat := 118140960795 + 1324376 * 2 ^ 59
def prefixEnd_1324376 : Nat := 4983230072969 + 3 ^ 40 * 1324376 * 2
def baseEnd_1324376 : Nat := 453360970186010404339541

theorem tailTrace_1324376 : CollatzResearch.WordTrace tailWord_1324376 prefixEnd_1324376 453360970186010404339541 := by
  unfold tailWord_1324376
  simp only [CollatzResearch.WordTrace]
  refine ⟨24151980525009706129184491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32202640700012941505579321 24151980525009706129184491)
  ·
    refine ⟨36227970787514559193776737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24151980525009706129184491 36227970787514559193776737)
    ·
      refine ⟨27170978090635919395332553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36227970787514559193776737 27170978090635919395332553)
      ·
        refine ⟨20378233567976939546499415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27170978090635919395332553 20378233567976939546499415)
        ·
          refine ⟨30567350351965409319749123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20378233567976939546499415 30567350351965409319749123)
          ·
            refine ⟨45851025527948113979623685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30567350351965409319749123 45851025527948113979623685)
            ·
              refine ⟨8597067286490271371179441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45851025527948113979623685 8597067286490271371179441)
              ·
                refine ⟨6447800464867703528384581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8597067286490271371179441 6447800464867703528384581)
                ·
                  refine ⟨1208962587162694411572109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6447800464867703528384581 1208962587162694411572109)
                  ·
                    refine ⟨453360970186010404339541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1208962587162694411572109 453360970186010404339541)
                    ·
                      rfl

theorem cell22_1324376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_1324376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324376 prefixEnd_1324376 := by exact prefixLift 1324376
  have htrace : WordTrace (prefixWord ++ tailWord_1324376) baseStart_1324376 baseEnd_1324376 := by
    simpa [prefixWord, tailWord_1324376, baseEnd_1324376] using wordTrace_append hprefix tailTrace_1324376
  have hstable : (prefixWord ++ tailWord_1324376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324376).length < 2 ^ (prefixWord ++ tailWord_1324376).sum := by decide
  have hdescent : baseEnd_1324376 < baseStart_1324376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324389 : List Nat := [1, 3, 1, 3, 1, 2, 11]
def baseStart_1324389 : Nat := 118140960795 + 1324389 * 2 ^ 59
def prefixEnd_1324389 : Nat := 4983230072969 + 3 ^ 40 * 1324389 * 2
def baseEnd_1324389 : Nat := 16791311864877137176463

theorem tailTrace_1324389 : CollatzResearch.WordTrace tailWord_1324389 prefixEnd_1324389 16791311864877137176463 := by
  unfold tailWord_1324389
  simp only [CollatzResearch.WordTrace]
  refine ⟨48304435198972315478592221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32202956799314876985728147 48304435198972315478592221)
  ·
    refine ⟨18114163199614618304472083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48304435198972315478592221 18114163199614618304472083)
    ·
      refine ⟨27171244799421927456708125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18114163199614618304472083 27171244799421927456708125)
      ·
        refine ⟨10189216799783222796265547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27171244799421927456708125 10189216799783222796265547)
        ·
          refine ⟨15283825199674834194398321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10189216799783222796265547 15283825199674834194398321)
          ·
            refine ⟨11462868899756125645798741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15283825199674834194398321 11462868899756125645798741)
            ·
              refine ⟨16791311864877137176463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11462868899756125645798741 16791311864877137176463)
              ·
                rfl

theorem cell22_1324389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 11].length) (baseStart_1324389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324389 prefixEnd_1324389 := by exact prefixLift 1324389
  have htrace : WordTrace (prefixWord ++ tailWord_1324389) baseStart_1324389 baseEnd_1324389 := by
    simpa [prefixWord, tailWord_1324389, baseEnd_1324389] using wordTrace_append hprefix tailTrace_1324389
  have hstable : (prefixWord ++ tailWord_1324389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324389).length < 2 ^ (prefixWord ++ tailWord_1324389).sum := by decide
  have hdescent : baseEnd_1324389 < baseStart_1324389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324423 : List Nat := [1, 1, 4, 2, 2, 4, 2, 6]
def baseStart_1324423 : Nat := 118140960795 + 1324423 * 2 ^ 59
def prefixEnd_1324423 : Nat := 4983230072969 + 3 ^ 40 * 1324423 * 2
def baseEnd_1324423 : Nat := 50375228805168660934933

theorem tailTrace_1324423 : CollatzResearch.WordTrace tailWord_1324423 prefixEnd_1324423 50375228805168660934933 := by
  unfold tailWord_1324423
  simp only [CollatzResearch.WordTrace]
  refine ⟨48305675280849139285329923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32203783520566092856886615 48305675280849139285329923)
  ·
    refine ⟨72458512921273708927994885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48305675280849139285329923 72458512921273708927994885)
    ·
      refine ⟨13585971172738820423999041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72458512921273708927994885 13585971172738820423999041)
      ·
        refine ⟨10189478379554115317999281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13585971172738820423999041 10189478379554115317999281)
        ·
          refine ⟨7642108784665586488499461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10189478379554115317999281 7642108784665586488499461)
          ·
            refine ⟨1432895397124797466593649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7642108784665586488499461 1432895397124797466593649)
            ·
              refine ⟨1074671547843598099945237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1432895397124797466593649 1074671547843598099945237)
              ·
                refine ⟨50375228805168660934933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1074671547843598099945237 50375228805168660934933)
                ·
                  rfl

theorem cell22_1324423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 6].length) (baseStart_1324423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324423 prefixEnd_1324423 := by exact prefixLift 1324423
  have htrace : WordTrace (prefixWord ++ tailWord_1324423) baseStart_1324423 baseEnd_1324423 := by
    simpa [prefixWord, tailWord_1324423, baseEnd_1324423] using wordTrace_append hprefix tailTrace_1324423
  have hstable : (prefixWord ++ tailWord_1324423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324423).length < 2 ^ (prefixWord ++ tailWord_1324423).sum := by decide
  have hdescent : baseEnd_1324423 < baseStart_1324423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324451 : List Nat := [1, 1, 1, 4, 1, 3, 2, 4, 5]
def baseStart_1324451 : Nat := 118140960795 + 1324451 * 2 ^ 59
def prefixEnd_1324451 : Nat := 4983230072969 + 3 ^ 40 * 1324451 * 2
def baseEnd_1324451 : Nat := 151128881406245069571437

theorem tailTrace_1324451 : CollatzResearch.WordTrace tailWord_1324451 prefixEnd_1324451 151128881406245069571437 := by
  unfold tailWord_1324451
  simp only [CollatzResearch.WordTrace]
  refine ⟨48306696524747700067349207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32204464349831800044899471 48306696524747700067349207)
  ·
    refine ⟨72460044787121550101023811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48306696524747700067349207 72460044787121550101023811)
    ·
      refine ⟨108690067180682325151535717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72460044787121550101023811 108690067180682325151535717)
      ·
        refine ⟨20379387596377935965912947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108690067180682325151535717 20379387596377935965912947)
        ·
          refine ⟨30569081394566903948869421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20379387596377935965912947 30569081394566903948869421)
          ·
            refine ⟨11463405522962588980826033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30569081394566903948869421 11463405522962588980826033)
            ·
              refine ⟨8597554142221941735619525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11463405522962588980826033 8597554142221941735619525)
              ·
                refine ⟨1612041401666614075428661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8597554142221941735619525 1612041401666614075428661)
                ·
                  refine ⟨151128881406245069571437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1612041401666614075428661 151128881406245069571437)
                  ·
                    rfl

theorem cell22_1324451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 5].length) (baseStart_1324451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324451 prefixEnd_1324451 := by exact prefixLift 1324451
  have htrace : WordTrace (prefixWord ++ tailWord_1324451) baseStart_1324451 baseEnd_1324451 := by
    simpa [prefixWord, tailWord_1324451, baseEnd_1324451] using wordTrace_append hprefix tailTrace_1324451
  have hstable : (prefixWord ++ tailWord_1324451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324451).length < 2 ^ (prefixWord ++ tailWord_1324451).sum := by decide
  have hdescent : baseEnd_1324451 < baseStart_1324451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324511 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 3, 5]
def baseStart_1324511 : Nat := 118140960795 + 1324511 * 2 ^ 59
def prefixEnd_1324511 : Nat := 4983230072969 + 3 ^ 40 * 1324511 * 2
def baseEnd_1324511 : Nat := 453407183444915052214127

theorem tailTrace_1324511 : CollatzResearch.WordTrace tailWord_1324511 prefixEnd_1324511 453407183444915052214127 := by
  unfold tailWord_1324511
  simp only [CollatzResearch.WordTrace]
  refine ⟨48308884904530330314533387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32205923269686886876355591 48308884904530330314533387)
  ·
    refine ⟨72463327356795495471800081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48308884904530330314533387 72463327356795495471800081)
    ·
      refine ⟨54347495517596621603850061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72463327356795495471800081 54347495517596621603850061)
      ·
        refine ⟨20380310819098733101443773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54347495517596621603850061 20380310819098733101443773)
        ·
          refine ⟨7642616557162024913041415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20380310819098733101443773 7642616557162024913041415)
          ·
            refine ⟨11463924835743037369562123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7642616557162024913041415 11463924835743037369562123)
            ·
              refine ⟨17195887253614556054343185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11463924835743037369562123 17195887253614556054343185)
              ·
                refine ⟨12896915440210917040757389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17195887253614556054343185 12896915440210917040757389)
                ·
                  refine ⟨4836343290079093890284021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12896915440210917040757389 4836343290079093890284021)
                  ·
                    refine ⟨453407183444915052214127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4836343290079093890284021 453407183444915052214127)
                    ·
                      rfl

theorem cell22_1324511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_1324511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324511 prefixEnd_1324511 := by exact prefixLift 1324511
  have htrace : WordTrace (prefixWord ++ tailWord_1324511) baseStart_1324511 baseEnd_1324511 := by
    simpa [prefixWord, tailWord_1324511, baseEnd_1324511] using wordTrace_append hprefix tailTrace_1324511
  have hstable : (prefixWord ++ tailWord_1324511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324511).length < 2 ^ (prefixWord ++ tailWord_1324511).sum := by decide
  have hdescent : baseEnd_1324511 < baseStart_1324511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324528 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 1, 5]
def baseStart_1324528 : Nat := 118140960795 + 1324528 * 2 ^ 59
def prefixEnd_1324528 : Nat := 4983230072969 + 3 ^ 40 * 1324528 * 2
def baseEnd_1324528 : Nat := 453413002892332674539075

theorem tailTrace_1324528 : CollatzResearch.WordTrace tailWord_1324528 prefixEnd_1324528 453413002892332674539075 := by
  unfold tailWord_1324528
  simp only [CollatzResearch.WordTrace]
  refine ⟨24154752472734371108951119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32206336630312494811934825 24154752472734371108951119)
  ·
    refine ⟨36232128709101556663426679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24154752472734371108951119 36232128709101556663426679)
    ·
      refine ⟨54348193063652334995140019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36232128709101556663426679 54348193063652334995140019)
      ·
        refine ⟨81522289595478502492710029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54348193063652334995140019 81522289595478502492710029)
        ·
          refine ⟨30570858598304438434766261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81522289595478502492710029 30570858598304438434766261)
          ·
            refine ⟨2866017993591041103259337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30570858598304438434766261 2866017993591041103259337)
            ·
              refine ⟨2149513495193280827444503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2866017993591041103259337 2149513495193280827444503)
              ·
                refine ⟨3224270242789921241166755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2149513495193280827444503 3224270242789921241166755)
                ·
                  refine ⟨4836405364184881861750133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3224270242789921241166755 4836405364184881861750133)
                  ·
                    refine ⟨453413002892332674539075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4836405364184881861750133 453413002892332674539075)
                    ·
                      rfl

theorem cell22_1324528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_1324528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324528 prefixEnd_1324528 := by exact prefixLift 1324528
  have htrace : WordTrace (prefixWord ++ tailWord_1324528) baseStart_1324528 baseEnd_1324528 := by
    simpa [prefixWord, tailWord_1324528, baseEnd_1324528] using wordTrace_append hprefix tailTrace_1324528
  have hstable : (prefixWord ++ tailWord_1324528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324528).length < 2 ^ (prefixWord ++ tailWord_1324528).sum := by decide
  have hdescent : baseEnd_1324528 < baseStart_1324528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324558 : List Nat := [4, 1, 1, 2, 4, 1, 9]
def baseStart_1324558 : Nat := 118140960795 + 1324558 * 2 ^ 59
def prefixEnd_1324558 : Nat := 4983230072969 + 3 ^ 40 * 1324558 * 2
def baseEnd_1324558 : Nat := 16793454537237873936629

theorem tailTrace_1324558 : CollatzResearch.WordTrace tailWord_1324558 prefixEnd_1324558 16793454537237873936629 := by
  unfold tailWord_1324558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6038824891920007167686791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32207066090240038227662885 6038824891920007167686791)
  ·
    refine ⟨9058237337880010751530187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6038824891920007167686791 9058237337880010751530187)
    ·
      refine ⟨13587356006820016127295281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9058237337880010751530187 13587356006820016127295281)
      ·
        refine ⟨10190517005115012095471461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13587356006820016127295281 10190517005115012095471461)
        ·
          refine ⟨1910721938459064767900899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10190517005115012095471461 1910721938459064767900899)
          ·
            refine ⟨2866082907688597151851349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1910721938459064767900899 2866082907688597151851349)
            ·
              refine ⟨16793454537237873936629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2866082907688597151851349 16793454537237873936629)
              ·
                rfl

theorem cell22_1324558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 9].length) (baseStart_1324558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324558 prefixEnd_1324558 := by exact prefixLift 1324558
  have htrace : WordTrace (prefixWord ++ tailWord_1324558) baseStart_1324558 baseEnd_1324558 := by
    simpa [prefixWord, tailWord_1324558, baseEnd_1324558] using wordTrace_append hprefix tailTrace_1324558
  have hstable : (prefixWord ++ tailWord_1324558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324558).length < 2 ^ (prefixWord ++ tailWord_1324558).sum := by decide
  have hdescent : baseEnd_1324558 < baseStart_1324558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324607 : List Nat := [1, 1, 2, 2, 3, 3, 3, 3, 1, 3]
def baseStart_1324607 : Nat := 118140960795 + 1324607 * 2 ^ 59
def prefixEnd_1324607 : Nat := 4983230072969 + 3 ^ 40 * 1324607 * 2
def baseEnd_1324607 : Nat := 453440046206802801813833

theorem tailTrace_1324607 : CollatzResearch.WordTrace tailWord_1324607 prefixEnd_1324607 453440046206802801813833 := by
  unfold tailWord_1324607
  simp only [CollatzResearch.WordTrace]
  refine ⟨48312386312182538710028075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32208257541455025806685383 48312386312182538710028075)
  ·
    refine ⟨72468579468273808065042113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48312386312182538710028075 72468579468273808065042113)
    ·
      refine ⟨54351434601205356048781585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72468579468273808065042113 54351434601205356048781585)
      ·
        refine ⟨40763575950904017036586189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54351434601205356048781585 40763575950904017036586189)
        ·
          refine ⟨15286340981589006388719821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40763575950904017036586189 15286340981589006388719821)
          ·
            refine ⟨5732377868095877395769933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15286340981589006388719821 5732377868095877395769933)
            ·
              refine ⟨2149641700535954023413725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5732377868095877395769933 2149641700535954023413725)
              ·
                refine ⟨806115637700982758780147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2149641700535954023413725 806115637700982758780147)
                ·
                  refine ⟨1209173456551474138170221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806115637700982758780147 1209173456551474138170221)
                  ·
                    refine ⟨453440046206802801813833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1209173456551474138170221 453440046206802801813833)
                    ·
                      rfl

theorem cell22_1324607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 1, 3].length) (baseStart_1324607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324607 prefixEnd_1324607 := by exact prefixLift 1324607
  have htrace : WordTrace (prefixWord ++ tailWord_1324607) baseStart_1324607 baseEnd_1324607 := by
    simpa [prefixWord, tailWord_1324607, baseEnd_1324607] using wordTrace_append hprefix tailTrace_1324607
  have hstable : (prefixWord ++ tailWord_1324607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324607).length < 2 ^ (prefixWord ++ tailWord_1324607).sum := by decide
  have hdescent : baseEnd_1324607 < baseStart_1324607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324630 : List Nat := [5, 2, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1324630 : Nat := 118140960795 + 1324630 * 2 ^ 59
def prefixEnd_1324630 : Nat := 4983230072969 + 3 ^ 40 * 1324630 * 2
def baseEnd_1324630 : Nat := 453447919576838408488763

theorem tailTrace_1324630 : CollatzResearch.WordTrace tailWord_1324630 prefixEnd_1324630 453447919576838408488763 := by
  unfold tailWord_1324630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3019576574443700852382209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32208816794066142425410229 3019576574443700852382209)
  ·
    refine ⟨2264682430832775639286657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3019576574443700852382209 2264682430832775639286657)
    ·
      refine ⟨1698511823124581729464993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2264682430832775639286657 1698511823124581729464993)
      ·
        refine ⟨1273883867343436297098745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1698511823124581729464993 1273883867343436297098745)
        ·
          refine ⟨955412900507577222824059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1273883867343436297098745 955412900507577222824059)
          ·
            refine ⟨1433119350761365834236089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955412900507577222824059 1433119350761365834236089)
            ·
              refine ⟨1074839513071024375677067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1433119350761365834236089 1074839513071024375677067)
              ·
                refine ⟨1612259269606536563515601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074839513071024375677067 1612259269606536563515601)
                ·
                  refine ⟨1209194452204902422636701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1612259269606536563515601 1209194452204902422636701)
                  ·
                    refine ⟨453447919576838408488763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1209194452204902422636701 453447919576838408488763)
                    ·
                      rfl

theorem cell22_1324630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1324630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324630 prefixEnd_1324630 := by exact prefixLift 1324630
  have htrace : WordTrace (prefixWord ++ tailWord_1324630) baseStart_1324630 baseEnd_1324630 := by
    simpa [prefixWord, tailWord_1324630, baseEnd_1324630] using wordTrace_append hprefix tailTrace_1324630
  have hstable : (prefixWord ++ tailWord_1324630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324630).length < 2 ^ (prefixWord ++ tailWord_1324630).sum := by decide
  have hdescent : baseEnd_1324630 < baseStart_1324630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324650 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_1324650 : Nat := 118140960795 + 1324650 * 2 ^ 59
def prefixEnd_1324650 : Nat := 4983230072969 + 3 ^ 40 * 1324650 * 2
def baseEnd_1324650 : Nat := 453454765985565022988701

theorem tailTrace_1324650 : CollatzResearch.WordTrace tailWord_1324650 prefixEnd_1324650 453454765985565022988701 := by
  unfold tailWord_1324650
  simp only [CollatzResearch.WordTrace]
  refine ⟨12078488662756689263460851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32209303100684504702562269 12078488662756689263460851)
  ·
    refine ⟨18117732994135033895191277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12078488662756689263460851 18117732994135033895191277)
    ·
      refine ⟨6794149872800637710696729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18117732994135033895191277 6794149872800637710696729)
      ·
        refine ⟨5095612404600478283022547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6794149872800637710696729 5095612404600478283022547)
        ·
          refine ⟨7643418606900717424533821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5095612404600478283022547 7643418606900717424533821)
          ·
            refine ⟨2866281977587769034200183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7643418606900717424533821 2866281977587769034200183)
            ·
              refine ⟨4299422966381653551300275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866281977587769034200183 4299422966381653551300275)
              ·
                refine ⟨6449134449572480326950413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299422966381653551300275 6449134449572480326950413)
                ·
                  refine ⟨2418425418589680122606405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6449134449572480326950413 2418425418589680122606405)
                  ·
                    refine ⟨453454765985565022988701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2418425418589680122606405 453454765985565022988701)
                    ·
                      rfl

theorem cell22_1324650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_1324650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324650 prefixEnd_1324650 := by exact prefixLift 1324650
  have htrace : WordTrace (prefixWord ++ tailWord_1324650) baseStart_1324650 baseEnd_1324650 := by
    simpa [prefixWord, tailWord_1324650, baseEnd_1324650] using wordTrace_append hprefix tailTrace_1324650
  have hstable : (prefixWord ++ tailWord_1324650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324650).length < 2 ^ (prefixWord ++ tailWord_1324650).sum := by decide
  have hdescent : baseEnd_1324650 < baseStart_1324650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324665 : List Nat := [1, 2, 1, 3, 3, 1, 2, 5, 4]
def baseStart_1324665 : Nat := 118140960795 + 1324665 * 2 ^ 59
def prefixEnd_1324665 : Nat := 4983230072969 + 3 ^ 40 * 1324665 * 2
def baseEnd_1324665 : Nat := 151153300264036661287885

theorem tailTrace_1324665 : CollatzResearch.WordTrace tailWord_1324665 prefixEnd_1324665 151153300264036661287885 := by
  unfold tailWord_1324665
  simp only [CollatzResearch.WordTrace]
  refine ⟨48314501745972414615639449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32209667830648276410426299 48314501745972414615639449)
  ·
    refine ⟨36235876309479310961729587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48314501745972414615639449 36235876309479310961729587)
    ·
      refine ⟨54353814464218966442594381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36235876309479310961729587 54353814464218966442594381)
      ·
        refine ⟨20382680424082112415972893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54353814464218966442594381 20382680424082112415972893)
        ·
          refine ⟨7643505159030792155989835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20382680424082112415972893 7643505159030792155989835)
          ·
            refine ⟨11465257738546188233984753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7643505159030792155989835 11465257738546188233984753)
            ·
              refine ⟨8598943303909641175488565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11465257738546188233984753 8598943303909641175488565)
              ·
                refine ⟨806150934741528860202053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8598943303909641175488565 806150934741528860202053)
                ·
                  refine ⟨151153300264036661287885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 806150934741528860202053 151153300264036661287885)
                  ·
                    rfl

theorem cell22_1324665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 4].length) (baseStart_1324665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324665 prefixEnd_1324665 := by exact prefixLift 1324665
  have htrace : WordTrace (prefixWord ++ tailWord_1324665) baseStart_1324665 baseEnd_1324665 := by
    simpa [prefixWord, tailWord_1324665, baseEnd_1324665] using wordTrace_append hprefix tailTrace_1324665
  have hstable : (prefixWord ++ tailWord_1324665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324665).length < 2 ^ (prefixWord ++ tailWord_1324665).sum := by decide
  have hdescent : baseEnd_1324665 < baseStart_1324665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324682 : List Nat := [3, 1, 2, 3, 2, 2, 1, 4, 4]
def baseStart_1324682 : Nat := 118140960795 + 1324682 * 2 ^ 59
def prefixEnd_1324682 : Nat := 4983230072969 + 3 ^ 40 * 1324682 * 2
def baseEnd_1324682 : Nat := 151155240079842535396201

theorem tailTrace_1324682 : CollatzResearch.WordTrace tailWord_1324682 prefixEnd_1324682 151155240079842535396201 := by
  unfold tailWord_1324682
  simp only [CollatzResearch.WordTrace]
  refine ⟨12078780446727706629752075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32210081191273884346005533 12078780446727706629752075)
  ·
    refine ⟨18118170670091559944628113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12078780446727706629752075 18118170670091559944628113)
    ·
      refine ⟨13588628002568669958471085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18118170670091559944628113 13588628002568669958471085)
      ·
        refine ⟨5095735500963251234426657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13588628002568669958471085 5095735500963251234426657)
        ·
          refine ⟨3821801625722438425819993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5095735500963251234426657 3821801625722438425819993)
          ·
            refine ⟨2866351219291828819364995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3821801625722438425819993 2866351219291828819364995)
            ·
              refine ⟨4299526828937743229047493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866351219291828819364995 4299526828937743229047493)
              ·
                refine ⟨806161280425826855446405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4299526828937743229047493 806161280425826855446405)
                ·
                  refine ⟨151155240079842535396201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 806161280425826855446405 151155240079842535396201)
                  ·
                    rfl

theorem cell22_1324682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_1324682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324682 prefixEnd_1324682 := by exact prefixLift 1324682
  have htrace : WordTrace (prefixWord ++ tailWord_1324682) baseStart_1324682 baseEnd_1324682 := by
    simpa [prefixWord, tailWord_1324682, baseEnd_1324682] using wordTrace_append hprefix tailTrace_1324682
  have hstable : (prefixWord ++ tailWord_1324682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324682).length < 2 ^ (prefixWord ++ tailWord_1324682).sum := by decide
  have hdescent : baseEnd_1324682 < baseStart_1324682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324718 : List Nat := [4, 1, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1324718 : Nat := 118140960795 + 1324718 * 2 ^ 59
def prefixEnd_1324718 : Nat := 4983230072969 + 3 ^ 40 * 1324718 * 2
def baseEnd_1324718 : Nat := 453478043775235512288493

theorem tailTrace_1324718 : CollatzResearch.WordTrace tailWord_1324718 prefixEnd_1324718 453478043775235512288493 := by
  unfold tailWord_1324718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6039554351847550583414851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32210956543186936444879205 6039554351847550583414851)
  ·
    refine ⟨9059331527771325875122277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6039554351847550583414851 9059331527771325875122277)
    ·
      refine ⟨1698624661457123601585427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9059331527771325875122277 1698624661457123601585427)
      ·
        refine ⟨2547936992185685402378141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1698624661457123601585427 2547936992185685402378141)
        ·
          refine ⟨955476372069632025891803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2547936992185685402378141 955476372069632025891803)
          ·
            refine ⟨1433214558104448038837705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955476372069632025891803 1433214558104448038837705)
            ·
              refine ⟨1074910918578336029128279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1433214558104448038837705 1074910918578336029128279)
              ·
                refine ⟨1612366377867504043692419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074910918578336029128279 1612366377867504043692419)
                ·
                  refine ⟨2418549566801256065538629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612366377867504043692419 2418549566801256065538629)
                  ·
                    refine ⟨453478043775235512288493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2418549566801256065538629 453478043775235512288493)
                    ·
                      rfl

theorem cell22_1324718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1324718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324718 prefixEnd_1324718 := by exact prefixLift 1324718
  have htrace : WordTrace (prefixWord ++ tailWord_1324718) baseStart_1324718 baseEnd_1324718 := by
    simpa [prefixWord, tailWord_1324718, baseEnd_1324718] using wordTrace_append hprefix tailTrace_1324718
  have hstable : (prefixWord ++ tailWord_1324718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324718).length < 2 ^ (prefixWord ++ tailWord_1324718).sum := by decide
  have hdescent : baseEnd_1324718 < baseStart_1324718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324776 : List Nat := [2, 1, 4, 1, 3, 3, 1, 3, 1, 3]
def baseStart_1324776 : Nat := 118140960795 + 1324776 * 2 ^ 59
def prefixEnd_1324776 : Nat := 4983230072969 + 3 ^ 40 * 1324776 * 2
def baseEnd_1324776 : Nat := 453497898360542694338315

theorem tailTrace_1324776 : CollatzResearch.WordTrace tailWord_1324776 prefixEnd_1324776 453497898360542694338315 := by
  unfold tailWord_1324776
  simp only [CollatzResearch.WordTrace]
  refine ⟨24159275124285140286465091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32212366832380187048620121 24159275124285140286465091)
  ·
    refine ⟨36238912686427710429697637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24159275124285140286465091 36238912686427710429697637)
    ·
      refine ⟨6794796128705195705568307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36238912686427710429697637 6794796128705195705568307)
      ·
        refine ⟨10192194193057793558352461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6794796128705195705568307 10192194193057793558352461)
        ·
          refine ⟨3822072822396672584382173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10192194193057793558352461 3822072822396672584382173)
          ·
            refine ⟨1433277308398752219143315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3822072822396672584382173 1433277308398752219143315)
            ·
              refine ⟨2149915962598128328714973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433277308398752219143315 2149915962598128328714973)
              ·
                refine ⟨806218485974298123268115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2149915962598128328714973 806218485974298123268115)
                ·
                  refine ⟨1209327728961447184902173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806218485974298123268115 1209327728961447184902173)
                  ·
                    refine ⟨453497898360542694338315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1209327728961447184902173 453497898360542694338315)
                    ·
                      rfl

theorem cell22_1324776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_1324776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324776 prefixEnd_1324776 := by exact prefixLift 1324776
  have htrace : WordTrace (prefixWord ++ tailWord_1324776) baseStart_1324776 baseEnd_1324776 := by
    simpa [prefixWord, tailWord_1324776, baseEnd_1324776] using wordTrace_append hprefix tailTrace_1324776
  have hstable : (prefixWord ++ tailWord_1324776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324776).length < 2 ^ (prefixWord ++ tailWord_1324776).sum := by decide
  have hdescent : baseEnd_1324776 < baseStart_1324776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324802 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_1324802 : Nat := 118140960795 + 1324802 * 2 ^ 59
def prefixEnd_1324802 : Nat := 4983230072969 + 3 ^ 40 * 1324802 * 2
def baseEnd_1324802 : Nat := 453506798691887293188235

theorem tailTrace_1324802 : CollatzResearch.WordTrace tailWord_1324802 prefixEnd_1324802 453506798691887293188235 := by
  unfold tailWord_1324802
  simp only [CollatzResearch.WordTrace]
  refine ⟨12079874636619021753344165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32212999030984058008917773 12079874636619021753344165)
  ·
    refine ⟨2264976494366066578752031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12079874636619021753344165 2264976494366066578752031)
    ·
      refine ⟨3397464741549099868128047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2264976494366066578752031 3397464741549099868128047)
      ·
        refine ⟨5096197112323649802192071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3397464741549099868128047 5096197112323649802192071)
        ·
          refine ⟨7644295668485474703288107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5096197112323649802192071 7644295668485474703288107)
          ·
            refine ⟨11466443502728212054932161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7644295668485474703288107 11466443502728212054932161)
            ·
              refine ⟨8599832627046159041199121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11466443502728212054932161 8599832627046159041199121)
              ·
                refine ⟨6449874470284619280899341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8599832627046159041199121 6449874470284619280899341)
                ·
                  refine ⟨2418702926356732230337253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6449874470284619280899341 2418702926356732230337253)
                  ·
                    refine ⟨453506798691887293188235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2418702926356732230337253 453506798691887293188235)
                    ·
                      rfl

theorem cell22_1324802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_1324802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324802 prefixEnd_1324802 := by exact prefixLift 1324802
  have htrace : WordTrace (prefixWord ++ tailWord_1324802) baseStart_1324802 baseEnd_1324802 := by
    simpa [prefixWord, tailWord_1324802, baseEnd_1324802] using wordTrace_append hprefix tailTrace_1324802
  have hstable : (prefixWord ++ tailWord_1324802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324802).length < 2 ^ (prefixWord ++ tailWord_1324802).sum := by decide
  have hdescent : baseEnd_1324802 < baseStart_1324802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324815 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 6, 3]
def baseStart_1324815 : Nat := 118140960795 + 1324815 * 2 ^ 59
def prefixEnd_1324815 : Nat := 4983230072969 + 3 ^ 40 * 1324815 * 2
def baseEnd_1324815 : Nat := 453511248857559592613195

theorem tailTrace_1324815 : CollatzResearch.WordTrace tailWord_1324815 prefixEnd_1324815 453511248857559592613195 := by
  unfold tailWord_1324815
  simp only [CollatzResearch.WordTrace]
  refine ⟨48319972695428990233599899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32213315130285993489066599 48319972695428990233599899)
  ·
    refine ⟨72479959043143485350399849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48319972695428990233599899 72479959043143485350399849)
    ·
      refine ⟨54359969282357614012799887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72479959043143485350399849 54359969282357614012799887)
      ·
        refine ⟨81539953923536421019199831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54359969282357614012799887 81539953923536421019199831)
        ·
          refine ⟨122309930885304631528799747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81539953923536421019199831 122309930885304631528799747)
          ·
            refine ⟨183464896327956947293199621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122309930885304631528799747 183464896327956947293199621)
            ·
              refine ⟨34399668061491927617474929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183464896327956947293199621 34399668061491927617474929)
              ·
                refine ⟨25799751046118945713106197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34399668061491927617474929 25799751046118945713106197)
                ·
                  refine ⟨1209363330286825580301853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25799751046118945713106197 1209363330286825580301853)
                  ·
                    refine ⟨453511248857559592613195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1209363330286825580301853 453511248857559592613195)
                    ·
                      rfl

theorem cell22_1324815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 3].length) (baseStart_1324815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324815 prefixEnd_1324815 := by exact prefixLift 1324815
  have htrace : WordTrace (prefixWord ++ tailWord_1324815) baseStart_1324815 baseEnd_1324815 := by
    simpa [prefixWord, tailWord_1324815, baseEnd_1324815] using wordTrace_append hprefix tailTrace_1324815
  have hstable : (prefixWord ++ tailWord_1324815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324815).length < 2 ^ (prefixWord ++ tailWord_1324815).sum := by decide
  have hdescent : baseEnd_1324815 < baseStart_1324815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324845 : List Nat := [1, 5, 3, 13]
def baseStart_1324845 : Nat := 118140960795 + 1324845 * 2 ^ 59
def prefixEnd_1324845 : Nat := 4983230072969 + 3 ^ 40 * 1324845 * 2
def baseEnd_1324845 : Nat := 622114565803360102007

theorem tailTrace_1324845 : CollatzResearch.WordTrace tailWord_1324845 prefixEnd_1324845 622114565803360102007 := by
  unfold tailWord_1324845
  simp only [CollatzResearch.WordTrace]
  refine ⟨48321066885320305357191989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32214044590213536904794659 48321066885320305357191989)
  ·
    refine ⟨4530100020498778627236749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48321066885320305357191989 4530100020498778627236749)
    ·
      refine ⟨1698787507687041985213781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4530100020498778627236749 1698787507687041985213781)
      ·
        refine ⟨622114565803360102007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1698787507687041985213781 622114565803360102007)
        ·
          rfl

theorem cell22_1324845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 13].length) (baseStart_1324845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324845 prefixEnd_1324845 := by exact prefixLift 1324845
  have htrace : WordTrace (prefixWord ++ tailWord_1324845) baseStart_1324845 baseEnd_1324845 := by
    simpa [prefixWord, tailWord_1324845, baseEnd_1324845] using wordTrace_append hprefix tailTrace_1324845
  have hstable : (prefixWord ++ tailWord_1324845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324845).length < 2 ^ (prefixWord ++ tailWord_1324845).sum := by decide
  have hdescent : baseEnd_1324845 < baseStart_1324845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324849 : List Nat := [1, 2, 2, 3, 2, 3, 2, 2, 2, 3]
def baseStart_1324849 : Nat := 118140960795 + 1324849 * 2 ^ 59
def prefixEnd_1324849 : Nat := 4983230072969 + 3 ^ 40 * 1324849 * 2
def baseEnd_1324849 : Nat := 453522887752394837263091

theorem tailTrace_1324849 : CollatzResearch.WordTrace tailWord_1324849 prefixEnd_1324849 453522887752394837263091 := by
  unfold tailWord_1324849
  simp only [CollatzResearch.WordTrace]
  refine ⟨48321212777305814040337601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32214141851537209360225067 48321212777305814040337601)
  ·
    refine ⟨36240909582979360530253201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48321212777305814040337601 36240909582979360530253201)
    ·
      refine ⟨27180682187234520397689901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36240909582979360530253201 27180682187234520397689901)
      ·
        refine ⟨10192755820212945149133713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27180682187234520397689901 10192755820212945149133713)
        ·
          refine ⟨7644566865159708861850285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10192755820212945149133713 7644566865159708861850285)
          ·
            refine ⟨2866712574434890823193857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7644566865159708861850285 2866712574434890823193857)
            ·
              refine ⟨2150034430826168117395393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2866712574434890823193857 2150034430826168117395393)
              ·
                refine ⟨1612525823119626088046545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2150034430826168117395393 1612525823119626088046545)
                ·
                  refine ⟨1209394367339719566034909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1612525823119626088046545 1209394367339719566034909)
                  ·
                    refine ⟨453522887752394837263091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1209394367339719566034909 453522887752394837263091)
                    ·
                      rfl

theorem cell22_1324849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_1324849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324849 prefixEnd_1324849 := by exact prefixLift 1324849
  have htrace : WordTrace (prefixWord ++ tailWord_1324849) baseStart_1324849 baseEnd_1324849 := by
    simpa [prefixWord, tailWord_1324849, baseEnd_1324849] using wordTrace_append hprefix tailTrace_1324849
  have hstable : (prefixWord ++ tailWord_1324849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324849).length < 2 ^ (prefixWord ++ tailWord_1324849).sum := by decide
  have hdescent : baseEnd_1324849 < baseStart_1324849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324851 : List Nat := [1, 1, 1, 2, 7, 2, 2, 2, 4]
def baseStart_1324851 : Nat := 118140960795 + 1324851 * 2 ^ 59
def prefixEnd_1324851 : Nat := 4983230072969 + 3 ^ 40 * 1324851 * 2
def baseEnd_1324851 : Nat := 151174524131089166237695

theorem tailTrace_1324851 : CollatzResearch.WordTrace tailWord_1324851 prefixEnd_1324851 151174524131089166237695 := by
  unfold tailWord_1324851
  simp only [CollatzResearch.WordTrace]
  refine ⟨48321285723298568381910407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32214190482199045587940271 48321285723298568381910407)
  ·
    refine ⟨72481928584947852572865611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48321285723298568381910407 72481928584947852572865611)
    ·
      refine ⟨108722892877421778859298417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72481928584947852572865611 108722892877421778859298417)
      ·
        refine ⟨81542169658066334144473813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108722892877421778859298417 81542169658066334144473813)
        ·
          refine ⟨1911144601360929706511105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 81542169658066334144473813 1911144601360929706511105)
          ·
            refine ⟨1433358451020697279883329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1911144601360929706511105 1433358451020697279883329)
            ·
              refine ⟨1075018838265522959912497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1433358451020697279883329 1075018838265522959912497)
              ·
                refine ⟨806264128699142219934373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075018838265522959912497 806264128699142219934373)
                ·
                  refine ⟨151174524131089166237695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 806264128699142219934373 151174524131089166237695)
                  ·
                    rfl

theorem cell22_1324851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 4].length) (baseStart_1324851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324851 prefixEnd_1324851 := by exact prefixLift 1324851
  have htrace : WordTrace (prefixWord ++ tailWord_1324851) baseStart_1324851 baseEnd_1324851 := by
    simpa [prefixWord, tailWord_1324851, baseEnd_1324851] using wordTrace_append hprefix tailTrace_1324851
  have hstable : (prefixWord ++ tailWord_1324851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324851).length < 2 ^ (prefixWord ++ tailWord_1324851).sum := by decide
  have hdescent : baseEnd_1324851 < baseStart_1324851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324862 : List Nat := [4, 2, 1, 2, 2, 1, 3, 7]
def baseStart_1324862 : Nat := 118140960795 + 1324862 * 2 ^ 59
def prefixEnd_1324862 : Nat := 4983230072969 + 3 ^ 40 * 1324862 * 2
def baseEnd_1324862 : Nat := 50391926435340792965339

theorem tailTrace_1324862 : CollatzResearch.WordTrace tailWord_1324862 prefixEnd_1324862 50391926435340792965339 := by
  unfold tailWord_1324862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6040210865782339657570105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32214457950839144840373893 6040210865782339657570105)
  ·
    refine ⟨4530158149336754743177579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6040210865782339657570105 4530158149336754743177579)
    ·
      refine ⟨6795237224005132114766369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4530158149336754743177579 6795237224005132114766369)
      ·
        refine ⟨5096427918003849086074777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6795237224005132114766369 5096427918003849086074777)
        ·
          refine ⟨3822320938502886814556083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5096427918003849086074777 3822320938502886814556083)
          ·
            refine ⟨5733481407754330221834125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822320938502886814556083 5733481407754330221834125)
            ·
              refine ⟨2150055527907873833187797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5733481407754330221834125 2150055527907873833187797)
              ·
                refine ⟨50391926435340792965339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2150055527907873833187797 50391926435340792965339)
                ·
                  rfl

theorem cell22_1324862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_1324862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324862 prefixEnd_1324862 := by exact prefixLift 1324862
  have htrace : WordTrace (prefixWord ++ tailWord_1324862) baseStart_1324862 baseEnd_1324862 := by
    simpa [prefixWord, tailWord_1324862, baseEnd_1324862] using wordTrace_append hprefix tailTrace_1324862
  have hstable : (prefixWord ++ tailWord_1324862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324862).length < 2 ^ (prefixWord ++ tailWord_1324862).sum := by decide
  have hdescent : baseEnd_1324862 < baseStart_1324862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324890 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 7]
def baseStart_1324890 : Nat := 118140960795 + 1324890 * 2 ^ 59
def prefixEnd_1324890 : Nat := 4983230072969 + 3 ^ 40 * 1324890 * 2
def baseEnd_1324890 : Nat := 151178974296761465662655

theorem tailTrace_1324890 : CollatzResearch.WordTrace tailWord_1324890 prefixEnd_1324890 151178974296761465662655 := by
  unfold tailWord_1324890
  simp only [CollatzResearch.WordTrace]
  refine ⟨12080677042539319510645031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32215138780104852028386749 12080677042539319510645031)
  ·
    refine ⟨18121015563808979265967547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12080677042539319510645031 18121015563808979265967547)
    ·
      refine ⟨27181523345713468898951321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18121015563808979265967547 27181523345713468898951321)
      ·
        refine ⟨20386142509285101674213491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27181523345713468898951321 20386142509285101674213491)
        ·
          refine ⟨30579213763927652511320237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20386142509285101674213491 30579213763927652511320237)
          ·
            refine ⟨11467205161472869691745089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30579213763927652511320237 11467205161472869691745089)
            ·
              refine ⟨8600403871104652268808817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11467205161472869691745089 8600403871104652268808817)
              ·
                refine ⟨6450302903328489201606613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8600403871104652268808817 6450302903328489201606613)
                ·
                  refine ⟨151178974296761465662655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6450302903328489201606613 151178974296761465662655)
                  ·
                    rfl

theorem cell22_1324890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_1324890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324890 prefixEnd_1324890 := by exact prefixLift 1324890
  have htrace : WordTrace (prefixWord ++ tailWord_1324890) baseStart_1324890 baseEnd_1324890 := by
    simpa [prefixWord, tailWord_1324890, baseEnd_1324890] using wordTrace_append hprefix tailTrace_1324890
  have hstable : (prefixWord ++ tailWord_1324890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324890).length < 2 ^ (prefixWord ++ tailWord_1324890).sum := by decide
  have hdescent : baseEnd_1324890 < baseStart_1324890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324954 : List Nat := [3, 1, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_1324954 : Nat := 118140960795 + 1324954 * 2 ^ 59
def prefixEnd_1324954 : Nat := 4983230072969 + 3 ^ 40 * 1324954 * 2
def baseEnd_1324954 : Nat := 453558831398209563387769

theorem tailTrace_1324954 : CollatzResearch.WordTrace tailWord_1324954 prefixEnd_1324954 453558831398209563387769 := by
  unfold tailWord_1324954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12081260610481354243227479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32216694961283611315273277 12081260610481354243227479)
  ·
    refine ⟨18121890915722031364841219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12081260610481354243227479 18121890915722031364841219)
    ·
      refine ⟨27182836373583047047261829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18121890915722031364841219 27182836373583047047261829)
      ·
        refine ⟨5096781820046821321361593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27182836373583047047261829 5096781820046821321361593)
        ·
          refine ⟨3822586365035115991021195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5096781820046821321361593 3822586365035115991021195)
          ·
            refine ⟨5733879547552673986531793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822586365035115991021195 5733879547552673986531793)
            ·
              refine ⟨4300409660664505489898845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5733879547552673986531793 4300409660664505489898845)
              ·
                refine ⟨1612653622749189558712067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4300409660664505489898845 1612653622749189558712067)
                ·
                  refine ⟨2418980434123784338068101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612653622749189558712067 2418980434123784338068101)
                  ·
                    refine ⟨453558831398209563387769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2418980434123784338068101 453558831398209563387769)
                    ·
                      rfl

theorem cell22_1324954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_1324954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324954 prefixEnd_1324954 := by exact prefixLift 1324954
  have htrace : WordTrace (prefixWord ++ tailWord_1324954) baseStart_1324954 baseEnd_1324954 := by
    simpa [prefixWord, tailWord_1324954, baseEnd_1324954] using wordTrace_append hprefix tailTrace_1324954
  have hstable : (prefixWord ++ tailWord_1324954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324954).length < 2 ^ (prefixWord ++ tailWord_1324954).sum := by decide
  have hdescent : baseEnd_1324954 < baseStart_1324954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324984 : List Nat := [2, 1, 2, 1, 2, 3, 3, 3, 2, 3]
def baseStart_1324984 : Nat := 118140960795 + 1324984 * 2 ^ 59
def prefixEnd_1324984 : Nat := 4983230072969 + 3 ^ 40 * 1324984 * 2
def baseEnd_1324984 : Nat := 453569101011299485137677

theorem tailTrace_1324984 : CollatzResearch.WordTrace tailWord_1324984 prefixEnd_1324984 453569101011299485137677 := by
  unfold tailWord_1324984
  simp only [CollatzResearch.WordTrace]
  refine ⟨24163068315908366048251003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32217424421211154731001337 24163068315908366048251003)
  ·
    refine ⟨36244602473862549072376505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24163068315908366048251003 36244602473862549072376505)
    ·
      refine ⟨27183451855396911804282379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36244602473862549072376505 27183451855396911804282379)
      ·
        refine ⟨40775177783095367706423569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27183451855396911804282379 40775177783095367706423569)
        ·
          refine ⟨30581383337321525779817677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40775177783095367706423569 30581383337321525779817677)
          ·
            refine ⟨11468018751495572167431629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30581383337321525779817677 11468018751495572167431629)
            ·
              refine ⟨4300507031810839562786861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11468018751495572167431629 4300507031810839562786861)
              ·
                refine ⟨1612690136929064836045073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4300507031810839562786861 1612690136929064836045073)
                ·
                  refine ⟨1209517602696798627033805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1612690136929064836045073 1209517602696798627033805)
                  ·
                    refine ⟨453569101011299485137677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1209517602696798627033805 453569101011299485137677)
                    ·
                      rfl

theorem cell22_1324984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_1324984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324984 prefixEnd_1324984 := by exact prefixLift 1324984
  have htrace : WordTrace (prefixWord ++ tailWord_1324984) baseStart_1324984 baseEnd_1324984 := by
    simpa [prefixWord, tailWord_1324984, baseEnd_1324984] using wordTrace_append hprefix tailTrace_1324984
  have hstable : (prefixWord ++ tailWord_1324984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324984).length < 2 ^ (prefixWord ++ tailWord_1324984).sum := by decide
  have hdescent : baseEnd_1324984 < baseStart_1324984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324988 : List Nat := [2, 2, 2, 5, 1, 2, 1, 2, 1, 4]
def baseStart_1324988 : Nat := 118140960795 + 1324988 * 2 ^ 59
def prefixEnd_1324988 : Nat := 4983230072969 + 3 ^ 40 * 1324988 * 2
def baseEnd_1324988 : Nat := 453570470293044808037665

theorem tailTrace_1324988 : CollatzResearch.WordTrace tailWord_1324988 prefixEnd_1324988 453570470293044808037665 := by
  unfold tailWord_1324988
  simp only [CollatzResearch.WordTrace]
  refine ⟨24163141261901120389823809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32217521682534827186431745 24163141261901120389823809)
  ·
    refine ⟨18122355946425840292367857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24163141261901120389823809 18122355946425840292367857)
    ·
      refine ⟨13591766959819380219275893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18122355946425840292367857 13591766959819380219275893)
      ·
        refine ⟨1274228152483066895557115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13591766959819380219275893 1274228152483066895557115)
        ·
          refine ⟨1911342228724600343335673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274228152483066895557115 1911342228724600343335673)
          ·
            refine ⟨1433506671543450257501755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1911342228724600343335673 1433506671543450257501755)
            ·
              refine ⟨2150260007315175386252633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433506671543450257501755 2150260007315175386252633)
              ·
                refine ⟨1612695005486381539689475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2150260007315175386252633 1612695005486381539689475)
                ·
                  refine ⟨2419042508229572309534213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612695005486381539689475 2419042508229572309534213)
                  ·
                    refine ⟨453570470293044808037665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2419042508229572309534213 453570470293044808037665)
                    ·
                      rfl

theorem cell22_1324988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_1324988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1324988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1324988 prefixEnd_1324988 := by exact prefixLift 1324988
  have htrace : WordTrace (prefixWord ++ tailWord_1324988) baseStart_1324988 baseEnd_1324988 := by
    simpa [prefixWord, tailWord_1324988, baseEnd_1324988] using wordTrace_append hprefix tailTrace_1324988
  have hstable : (prefixWord ++ tailWord_1324988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324988).length < 2 ^ (prefixWord ++ tailWord_1324988).sum := by decide
  have hdescent : baseEnd_1324988 < baseStart_1324988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325014 : List Nat := [5, 2, 1, 1, 3, 10]
def baseStart_1325014 : Nat := 118140960795 + 1325014 * 2 ^ 59
def prefixEnd_1325014 : Nat := 4983230072969 + 3 ^ 40 * 1325014 * 2
def baseEnd_1325014 : Nat := 5599745316350486504785

theorem tailTrace_1325014 : CollatzResearch.WordTrace tailWord_1325014 prefixEnd_1325014 5599745316350486504785 := by
  unfold tailWord_1325014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3020451926356752951255881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32218153881138698146729397 3020451926356752951255881)
  ·
    refine ⟨2265338944767564713441911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3020451926356752951255881 2265338944767564713441911)
    ·
      refine ⟨3398008417151347070162867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2265338944767564713441911 3398008417151347070162867)
      ·
        refine ⟨5097012625727020605244301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3398008417151347070162867 5097012625727020605244301)
        ·
          refine ⟨1911379734647632726966613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5097012625727020605244301 1911379734647632726966613)
          ·
            refine ⟨5599745316350486504785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1911379734647632726966613 5599745316350486504785)
            ·
              rfl

theorem cell22_1325014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 10].length) (baseStart_1325014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325014 prefixEnd_1325014 := by exact prefixLift 1325014
  have htrace : WordTrace (prefixWord ++ tailWord_1325014) baseStart_1325014 baseEnd_1325014 := by
    simpa [prefixWord, tailWord_1325014, baseEnd_1325014] using wordTrace_append hprefix tailTrace_1325014
  have hstable : (prefixWord ++ tailWord_1325014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325014).length < 2 ^ (prefixWord ++ tailWord_1325014).sum := by decide
  have hdescent : baseEnd_1325014 < baseStart_1325014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325020 : List Nat := [2, 2, 6, 1, 1, 1, 1, 4, 4]
def baseStart_1325020 : Nat := 118140960795 + 1325020 * 2 ^ 59
def prefixEnd_1325020 : Nat := 4983230072969 + 3 ^ 40 * 1325020 * 2
def baseEnd_1325020 : Nat := 151193808182335797079189

theorem tailTrace_1325020 : CollatzResearch.WordTrace tailWord_1325020 prefixEnd_1325020 151193808182335797079189 := by
  unfold tailWord_1325020
  simp only [CollatzResearch.WordTrace]
  refine ⟨24163724829843155122406257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32218299773124206829875009 24163724829843155122406257)
  ·
    refine ⟨18122793622382366341804693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24163724829843155122406257 18122793622382366341804693)
    ·
      refine ⟨849505951049173422272095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18122793622382366341804693 849505951049173422272095)
      ·
        refine ⟨1274258926573760133408143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 849505951049173422272095 1274258926573760133408143)
        ·
          refine ⟨1911388389860640200112215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274258926573760133408143 1911388389860640200112215)
          ·
            refine ⟨2867082584790960300168323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911388389860640200112215 2867082584790960300168323)
            ·
              refine ⟨4300623877186440450252485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2867082584790960300168323 4300623877186440450252485)
              ·
                refine ⟨806366976972457584422341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4300623877186440450252485 806366976972457584422341)
                ·
                  refine ⟨151193808182335797079189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 806366976972457584422341 151193808182335797079189)
                  ·
                    rfl

theorem cell22_1325020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_1325020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325020 prefixEnd_1325020 := by exact prefixLift 1325020
  have htrace : WordTrace (prefixWord ++ tailWord_1325020) baseStart_1325020 baseEnd_1325020 := by
    simpa [prefixWord, tailWord_1325020, baseEnd_1325020] using wordTrace_append hprefix tailTrace_1325020
  have hstable : (prefixWord ++ tailWord_1325020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325020).length < 2 ^ (prefixWord ++ tailWord_1325020).sum := by decide
  have hdescent : baseEnd_1325020 < baseStart_1325020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325027 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 2, 6]
def baseStart_1325027 : Nat := 118140960795 + 1325027 * 2 ^ 59
def prefixEnd_1325027 : Nat := 4983230072969 + 3 ^ 40 * 1325027 * 2
def baseEnd_1325027 : Nat := 453583820790061706312545

theorem tailTrace_1325027 : CollatzResearch.WordTrace tailWord_1325027 prefixEnd_1325027 453583820790061706312545 := by
  unfold tailWord_1325027
  simp only [CollatzResearch.WordTrace]
  refine ⟨48327704970660950440317335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32218469980440633626878223 48327704970660950440317335)
  ·
    refine ⟨72491557455991425660476003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48327704970660950440317335 72491557455991425660476003)
    ·
      refine ⟨108737336183987138490714005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72491557455991425660476003 108737336183987138490714005)
      ·
        refine ⟨5097062633624397116752219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108737336183987138490714005 5097062633624397116752219)
        ·
          refine ⟨7645593950436595675128329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5097062633624397116752219 7645593950436595675128329)
          ·
            refine ⟨5734195462827446756346247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7645593950436595675128329 5734195462827446756346247)
            ·
              refine ⟨8601293194241170134519371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5734195462827446756346247 8601293194241170134519371)
              ·
                refine ⟨12901939791361755201779057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8601293194241170134519371 12901939791361755201779057)
                ·
                  refine ⟨9676454843521316401334293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12901939791361755201779057 9676454843521316401334293)
                  ·
                    refine ⟨453583820790061706312545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9676454843521316401334293 453583820790061706312545)
                    ·
                      rfl

theorem cell22_1325027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 6].length) (baseStart_1325027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325027 prefixEnd_1325027 := by exact prefixLift 1325027
  have htrace : WordTrace (prefixWord ++ tailWord_1325027) baseStart_1325027 baseEnd_1325027 := by
    simpa [prefixWord, tailWord_1325027, baseEnd_1325027] using wordTrace_append hprefix tailTrace_1325027
  have hstable : (prefixWord ++ tailWord_1325027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325027).length < 2 ^ (prefixWord ++ tailWord_1325027).sum := by decide
  have hdescent : baseEnd_1325027 < baseStart_1325027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325031 : List Nat := [1, 1, 5, 2, 4, 1, 1, 7]
def baseStart_1325031 : Nat := 118140960795 + 1325031 * 2 ^ 59
def prefixEnd_1325031 : Nat := 4983230072969 + 3 ^ 40 * 1325031 * 2
def baseEnd_1325031 : Nat := 50398354452423003245837

theorem tailTrace_1325031 : CollatzResearch.WordTrace tailWord_1325031 prefixEnd_1325031 50398354452423003245837 := by
  unfold tailWord_1325031
  simp only [CollatzResearch.WordTrace]
  refine ⟨48327850862646459123462947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32218567241764306082308631 48327850862646459123462947)
  ·
    refine ⟨72491776293969688685194421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48327850862646459123462947 72491776293969688685194421)
    ·
      refine ⟨6796104027559658314236977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72491776293969688685194421 6796104027559658314236977)
      ·
        refine ⟨5097078020669743735677733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6796104027559658314236977 5097078020669743735677733)
        ·
          refine ⟨955702128875576950439575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5097078020669743735677733 955702128875576950439575)
          ·
            refine ⟨1433553193313365425659363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955702128875576950439575 1433553193313365425659363)
            ·
              refine ⟨2150329789970048138489045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433553193313365425659363 2150329789970048138489045)
              ·
                refine ⟨50398354452423003245837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2150329789970048138489045 50398354452423003245837)
                ·
                  rfl

theorem cell22_1325031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 7].length) (baseStart_1325031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325031 prefixEnd_1325031 := by exact prefixLift 1325031
  have htrace : WordTrace (prefixWord ++ tailWord_1325031) baseStart_1325031 baseEnd_1325031 := by
    simpa [prefixWord, tailWord_1325031, baseEnd_1325031] using wordTrace_append hprefix tailTrace_1325031
  have hstable : (prefixWord ++ tailWord_1325031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325031).length < 2 ^ (prefixWord ++ tailWord_1325031).sum := by decide
  have hdescent : baseEnd_1325031 < baseStart_1325031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325057 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1325057 : Nat := 118140960795 + 1325057 * 2 ^ 59
def prefixEnd_1325057 : Nat := 4983230072969 + 3 ^ 40 * 1325057 * 2
def baseEnd_1325057 : Nat := 453594090403151628062453

theorem tailTrace_1325057 : CollatzResearch.WordTrace tailWord_1325057 prefixEnd_1325057 453594090403151628062453 := by
  unfold tailWord_1325057
  simp only [CollatzResearch.WordTrace]
  refine ⟨48328799160552265563909425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32219199440368177042606283 48328799160552265563909425)
  ·
    refine ⟨36246599370414199172932069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48328799160552265563909425 36246599370414199172932069)
    ·
      refine ⟨6796237381952662344924763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36246599370414199172932069 6796237381952662344924763)
      ·
        refine ⟨10194356072928993517387145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6796237381952662344924763 10194356072928993517387145)
        ·
          refine ⟨7645767054696745138040359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10194356072928993517387145 7645767054696745138040359)
          ·
            refine ⟨11468650582045117707060539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7645767054696745138040359 11468650582045117707060539)
            ·
              refine ⟨17202975873067676560590809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11468650582045117707060539 17202975873067676560590809)
              ·
                refine ⟨12902231904800757420443107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17202975873067676560590809 12902231904800757420443107)
                ·
                  refine ⟨19353347857201136130664661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12902231904800757420443107 19353347857201136130664661)
                  ·
                    refine ⟨453594090403151628062453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19353347857201136130664661 453594090403151628062453)
                    ·
                      rfl

theorem cell22_1325057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1325057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325057 prefixEnd_1325057 := by exact prefixLift 1325057
  have htrace : WordTrace (prefixWord ++ tailWord_1325057) baseStart_1325057 baseEnd_1325057 := by
    simpa [prefixWord, tailWord_1325057, baseEnd_1325057] using wordTrace_append hprefix tailTrace_1325057
  have hstable : (prefixWord ++ tailWord_1325057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325057).length < 2 ^ (prefixWord ++ tailWord_1325057).sum := by decide
  have hdescent : baseEnd_1325057 < baseStart_1325057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325063 : List Nat := [1, 1, 4, 3, 1, 3, 2, 3, 1, 3]
def baseStart_1325063 : Nat := 118140960795 + 1325063 * 2 ^ 59
def prefixEnd_1325063 : Nat := 4983230072969 + 3 ^ 40 * 1325063 * 2
def baseEnd_1325063 : Nat := 453596144325769612412435

theorem tailTrace_1325063 : CollatzResearch.WordTrace tailWord_1325063 prefixEnd_1325063 453596144325769612412435 := by
  unfold tailWord_1325063
  simp only [CollatzResearch.WordTrace]
  refine ⟨48329017998530528588627843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32219345332353685725751895 48329017998530528588627843)
  ·
    refine ⟨72493526997795792882941765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48329017998530528588627843 72493526997795792882941765)
    ·
      refine ⟨13592536312086711165551581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72493526997795792882941765 13592536312086711165551581)
      ·
        refine ⟨5097201117032516687081843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13592536312086711165551581 5097201117032516687081843)
        ·
          refine ⟨7645801675548775030622765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5097201117032516687081843 7645801675548775030622765)
          ·
            refine ⟨2867175628330790636483537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7645801675548775030622765 2867175628330790636483537)
            ·
              refine ⟨2150381721248092977362653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2867175628330790636483537 2150381721248092977362653)
              ·
                refine ⟨806393145468034866510995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2150381721248092977362653 806393145468034866510995)
                ·
                  refine ⟨1209589718202052299766493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806393145468034866510995 1209589718202052299766493)
                  ·
                    refine ⟨453596144325769612412435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1209589718202052299766493 453596144325769612412435)
                    ·
                      rfl

theorem cell22_1325063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_1325063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325063 prefixEnd_1325063 := by exact prefixLift 1325063
  have htrace : WordTrace (prefixWord ++ tailWord_1325063) baseStart_1325063 baseEnd_1325063 := by
    simpa [prefixWord, tailWord_1325063, baseEnd_1325063] using wordTrace_append hprefix tailTrace_1325063
  have hstable : (prefixWord ++ tailWord_1325063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325063).length < 2 ^ (prefixWord ++ tailWord_1325063).sum := by decide
  have hdescent : baseEnd_1325063 < baseStart_1325063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325069 : List Nat := [1, 7, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_1325069 : Nat := 118140960795 + 1325069 * 2 ^ 59
def prefixEnd_1325069 : Nat := 4983230072969 + 3 ^ 40 * 1325069 * 2
def baseEnd_1325069 : Nat := 453598198248387596762417

theorem tailTrace_1325069 : CollatzResearch.WordTrace tailWord_1325069 prefixEnd_1325069 453598198248387596762417 := by
  unfold tailWord_1325069
  simp only [CollatzResearch.WordTrace]
  refine ⟨48329236836508791613346261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32219491224339194408897507 48329236836508791613346261)
  ·
    refine ⟨1132716488355674803437803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 48329236836508791613346261 1132716488355674803437803)
    ·
      refine ⟨1699074732533512205156705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1132716488355674803437803 1699074732533512205156705)
      ·
        refine ⟨1274306049400134153867529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1699074732533512205156705 1274306049400134153867529)
        ·
          refine ⟨955729537050100615400647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1274306049400134153867529 955729537050100615400647)
          ·
            refine ⟨1433594305575150923100971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955729537050100615400647 1433594305575150923100971)
            ·
              refine ⟨2150391458362726384651457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433594305575150923100971 2150391458362726384651457)
              ·
                refine ⟨1612793593772044788488593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2150391458362726384651457 1612793593772044788488593)
                ·
                  refine ⟨1209595195329033591366445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1612793593772044788488593 1209595195329033591366445)
                  ·
                    refine ⟨453598198248387596762417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1209595195329033591366445 453598198248387596762417)
                    ·
                      rfl

theorem cell22_1325069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_1325069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325069 prefixEnd_1325069 := by exact prefixLift 1325069
  have htrace : WordTrace (prefixWord ++ tailWord_1325069) baseStart_1325069 baseEnd_1325069 := by
    simpa [prefixWord, tailWord_1325069, baseEnd_1325069] using wordTrace_append hprefix tailTrace_1325069
  have hstable : (prefixWord ++ tailWord_1325069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325069).length < 2 ^ (prefixWord ++ tailWord_1325069).sum := by decide
  have hdescent : baseEnd_1325069 < baseStart_1325069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325106 : List Nat := [3, 2, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_1325106 : Nat := 118140960795 + 1325106 * 2 ^ 59
def prefixEnd_1325106 : Nat := 4983230072969 + 3 ^ 40 * 1325106 * 2
def baseEnd_1325106 : Nat := 453610864104531833587303

theorem tailTrace_1325106 : CollatzResearch.WordTrace tailWord_1325106 prefixEnd_1325106 453610864104531833587303 := by
  unfold tailWord_1325106
  simp only [CollatzResearch.WordTrace]
  refine ⟨12082646584343686733110793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32220390891583164621628781 12082646584343686733110793)
  ·
    refine ⟨9061984938257765049833095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12082646584343686733110793 9061984938257765049833095)
    ·
      refine ⟨13592977407386647574749643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9061984938257765049833095 13592977407386647574749643)
      ·
        refine ⟨20389466111079971362124465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13592977407386647574749643 20389466111079971362124465)
        ·
          refine ⟨15292099583309978521593349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20389466111079971362124465 15292099583309978521593349)
          ·
            refine ⟨2867268671870620972798753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15292099583309978521593349 2867268671870620972798753)
            ·
              refine ⟨2150451503902965729599065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2867268671870620972798753 2150451503902965729599065)
              ·
                refine ⟨1612838627927224297199299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2150451503902965729599065 1612838627927224297199299)
                ·
                  refine ⟨2419257941890836445798949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612838627927224297199299 2419257941890836445798949)
                  ·
                    refine ⟨453610864104531833587303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2419257941890836445798949 453610864104531833587303)
                    ·
                      rfl

theorem cell22_1325106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_1325106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325106 prefixEnd_1325106 := by exact prefixLift 1325106
  have htrace : WordTrace (prefixWord ++ tailWord_1325106) baseStart_1325106 baseEnd_1325106 := by
    simpa [prefixWord, tailWord_1325106, baseEnd_1325106] using wordTrace_append hprefix tailTrace_1325106
  have hstable : (prefixWord ++ tailWord_1325106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325106).length < 2 ^ (prefixWord ++ tailWord_1325106).sum := by decide
  have hdescent : baseEnd_1325106 < baseStart_1325106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325119 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 4, 3]
def baseStart_1325119 : Nat := 118140960795 + 1325119 * 2 ^ 59
def prefixEnd_1325119 : Nat := 4983230072969 + 3 ^ 40 * 1325119 * 2
def baseEnd_1325119 : Nat := 453615314270204133012263

theorem tailTrace_1325119 : CollatzResearch.WordTrace tailWord_1325119 prefixEnd_1325119 453615314270204133012263 := by
  unfold tailWord_1325119
  simp only [CollatzResearch.WordTrace]
  refine ⟨48331060486327650152666411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32220706990885100101777607 48331060486327650152666411)
  ·
    refine ⟨72496590729491475228999617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48331060486327650152666411 72496590729491475228999617)
    ·
      refine ⟨54372443047118606421749713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72496590729491475228999617 54372443047118606421749713)
      ·
        refine ⟨40779332285338954816312285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54372443047118606421749713 40779332285338954816312285)
        ·
          refine ⟨15292249607002108056117107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40779332285338954816312285 15292249607002108056117107)
          ·
            refine ⟨22938374410503162084175661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15292249607002108056117107 22938374410503162084175661)
            ·
              refine ⟨8601890403938685781565873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22938374410503162084175661 8601890403938685781565873)
              ·
                refine ⟨6451417802954014336174405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8601890403938685781565873 6451417802954014336174405)
                ·
                  refine ⟨1209640838053877688032701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6451417802954014336174405 1209640838053877688032701)
                  ·
                    refine ⟨453615314270204133012263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1209640838053877688032701 453615314270204133012263)
                    ·
                      rfl

theorem cell22_1325119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 3].length) (baseStart_1325119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325119 prefixEnd_1325119 := by exact prefixLift 1325119
  have htrace : WordTrace (prefixWord ++ tailWord_1325119) baseStart_1325119 baseEnd_1325119 := by
    simpa [prefixWord, tailWord_1325119, baseEnd_1325119] using wordTrace_append hprefix tailTrace_1325119
  have hstable : (prefixWord ++ tailWord_1325119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325119).length < 2 ^ (prefixWord ++ tailWord_1325119).sum := by decide
  have hdescent : baseEnd_1325119 < baseStart_1325119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325132 : List Nat := [2, 2, 1, 3, 1, 1, 12]
def baseStart_1325132 : Nat := 118140960795 + 1325132 * 2 ^ 59
def prefixEnd_1325132 : Nat := 4983230072969 + 3 ^ 40 * 1325132 * 2
def baseEnd_1325132 : Nat := 16800732016143571571749

theorem tailTrace_1325132 : CollatzResearch.WordTrace tailWord_1325132 prefixEnd_1325132 16800732016143571571749 := by
  unfold tailWord_1325132
  simp only [CollatzResearch.WordTrace]
  refine ⟨24165767317640276686444825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32221023090187035581926433 24165767317640276686444825)
  ·
    refine ⟨18124325488230207514833619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24165767317640276686444825 18124325488230207514833619)
    ·
      refine ⟨27186488232345311272250429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18124325488230207514833619 27186488232345311272250429)
      ·
        refine ⟨10194933087129491727093911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27186488232345311272250429 10194933087129491727093911)
        ·
          refine ⟨15292399630694237590640867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10194933087129491727093911 15292399630694237590640867)
          ·
            refine ⟨22938599446041356385961301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15292399630694237590640867 22938599446041356385961301)
            ·
              refine ⟨16800732016143571571749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 22938599446041356385961301 16800732016143571571749)
              ·
                rfl

theorem cell22_1325132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 12].length) (baseStart_1325132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325132 prefixEnd_1325132 := by exact prefixLift 1325132
  have htrace : WordTrace (prefixWord ++ tailWord_1325132) baseStart_1325132 baseEnd_1325132 := by
    simpa [prefixWord, tailWord_1325132, baseEnd_1325132] using wordTrace_append hprefix tailTrace_1325132
  have hstable : (prefixWord ++ tailWord_1325132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325132).length < 2 ^ (prefixWord ++ tailWord_1325132).sum := by decide
  have hdescent : baseEnd_1325132 < baseStart_1325132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325134 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_1325134 : Nat := 118140960795 + 1325134 * 2 ^ 59
def prefixEnd_1325134 : Nat := 4983230072969 + 3 ^ 40 * 1325134 * 2
def baseEnd_1325134 : Nat := 453620449076749093887217

theorem tailTrace_1325134 : CollatzResearch.WordTrace tailWord_1325134 prefixEnd_1325134 453620449076749093887217 := by
  unfold tailWord_1325134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6041450947659163464307807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32221071720848871809641637 6041450947659163464307807)
  ·
    refine ⟨9062176421488745196461711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6041450947659163464307807 9062176421488745196461711)
    ·
      refine ⟨13593264632233117794692567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9062176421488745196461711 13593264632233117794692567)
      ·
        refine ⟨20389896948349676692038851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13593264632233117794692567 20389896948349676692038851)
        ·
          refine ⟨30584845422524515038058277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20389896948349676692038851 30584845422524515038058277)
          ·
            refine ⟨5734658516723346569635927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30584845422524515038058277 5734658516723346569635927)
            ·
              refine ⟨8601987775085019854453891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5734658516723346569635927 8601987775085019854453891)
              ·
                refine ⟨12902981662627529781680837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8601987775085019854453891 12902981662627529781680837)
                ·
                  refine ⟨2419309061742661834065157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12902981662627529781680837 2419309061742661834065157)
                  ·
                    refine ⟨453620449076749093887217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2419309061742661834065157 453620449076749093887217)
                    ·
                      rfl

theorem cell22_1325134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_1325134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325134 prefixEnd_1325134 := by exact prefixLift 1325134
  have htrace : WordTrace (prefixWord ++ tailWord_1325134) baseStart_1325134 baseEnd_1325134 := by
    simpa [prefixWord, tailWord_1325134, baseEnd_1325134] using wordTrace_append hprefix tailTrace_1325134
  have hstable : (prefixWord ++ tailWord_1325134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325134).length < 2 ^ (prefixWord ++ tailWord_1325134).sum := by decide
  have hdescent : baseEnd_1325134 < baseStart_1325134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325138 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 6]
def baseStart_1325138 : Nat := 118140960795 + 1325138 * 2 ^ 59
def prefixEnd_1325138 : Nat := 4983230072969 + 3 ^ 40 * 1325138 * 2
def baseEnd_1325138 : Nat := 151207272786164805595735

theorem tailTrace_1325138 : CollatzResearch.WordTrace tailWord_1325138 prefixEnd_1325138 151207272786164805595735 := by
  unfold tailWord_1325138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12082938368314704099402017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32221168982172544265072045 12082938368314704099402017)
  ·
    refine ⟨9062203776236028074551513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12082938368314704099402017 9062203776236028074551513)
    ·
      refine ⟨6796652832177021055913635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9062203776236028074551513 6796652832177021055913635)
      ·
        refine ⟨10194979248265531583870453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6796652832177021055913635 10194979248265531583870453)
        ·
          refine ⟨955779304524893585987855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10194979248265531583870453 955779304524893585987855)
          ·
            refine ⟨1433668956787340378981783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955779304524893585987855 1433668956787340378981783)
            ·
              refine ⟨2150503435181010568472675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433668956787340378981783 2150503435181010568472675)
              ·
                refine ⟨3225755152771515852709013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2150503435181010568472675 3225755152771515852709013)
                ·
                  refine ⟨151207272786164805595735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3225755152771515852709013 151207272786164805595735)
                  ·
                    rfl

theorem cell22_1325138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_1325138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325138 prefixEnd_1325138 := by exact prefixLift 1325138
  have htrace : WordTrace (prefixWord ++ tailWord_1325138) baseStart_1325138 baseEnd_1325138 := by
    simpa [prefixWord, tailWord_1325138, baseEnd_1325138] using wordTrace_append hprefix tailTrace_1325138
  have hstable : (prefixWord ++ tailWord_1325138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325138).length < 2 ^ (prefixWord ++ tailWord_1325138).sum := by decide
  have hdescent : baseEnd_1325138 < baseStart_1325138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325241 : List Nat := [1, 2, 1, 4, 1, 2, 3, 3, 1, 4]
def baseStart_1325241 : Nat := 118140960795 + 1325241 * 2 ^ 59
def prefixEnd_1325241 : Nat := 4983230072969 + 3 ^ 40 * 1325241 * 2
def baseEnd_1325241 : Nat := 453657077363436481461889

theorem tailTrace_1325241 : CollatzResearch.WordTrace tailWord_1325241 prefixEnd_1325241 453657077363436481461889 := by
  unfold tailWord_1325241
  simp only [CollatzResearch.WordTrace]
  refine ⟨48335510191885664988607577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32223673461257109992405051 48335510191885664988607577)
  ·
    refine ⟨36251632643914248741455683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48335510191885664988607577 36251632643914248741455683)
    ·
      refine ⟨54377448965871373112183525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36251632643914248741455683 54377448965871373112183525)
      ·
        refine ⟨10195771681100882458534411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54377448965871373112183525 10195771681100882458534411)
        ·
          refine ⟨15293657521651323687801617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10195771681100882458534411 15293657521651323687801617)
          ·
            refine ⟨11470243141238492765851213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15293657521651323687801617 11470243141238492765851213)
            ·
              refine ⟨4301341177964434787194205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11470243141238492765851213 4301341177964434787194205)
              ·
                refine ⟨1613002941736663045197827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4301341177964434787194205 1613002941736663045197827)
                ·
                  refine ⟨2419504412604994567796741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613002941736663045197827 2419504412604994567796741)
                  ·
                    refine ⟨453657077363436481461889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2419504412604994567796741 453657077363436481461889)
                    ·
                      rfl

theorem cell22_1325241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_1325241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325241 prefixEnd_1325241 := by exact prefixLift 1325241
  have htrace : WordTrace (prefixWord ++ tailWord_1325241) baseStart_1325241 baseEnd_1325241 := by
    simpa [prefixWord, tailWord_1325241, baseEnd_1325241] using wordTrace_append hprefix tailTrace_1325241
  have hstable : (prefixWord ++ tailWord_1325241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325241).length < 2 ^ (prefixWord ++ tailWord_1325241).sum := by decide
  have hdescent : baseEnd_1325241 < baseStart_1325241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325410 : List Nat := [3, 3, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1325410 : Nat := 118140960795 + 1325410 * 2 ^ 59
def prefixEnd_1325410 : Nat := 4983230072969 + 3 ^ 40 * 1325410 * 2
def baseEnd_1325410 : Nat := 453714929517176373986371

theorem tailTrace_1325410 : CollatzResearch.WordTrace tailWord_1325410 prefixEnd_1325410 453714929517176373986371 := by
  unfold tailWord_1325410
  simp only [CollatzResearch.WordTrace]
  refine ⟨12085418532068351712877421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32227782752182271234339789 12085418532068351712877421)
  ·
    refine ⟨4532031949525631892329033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12085418532068351712877421 4532031949525631892329033)
    ·
      refine ⟨3399023962144223919246775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4532031949525631892329033 3399023962144223919246775)
      ·
        refine ⟨5098535943216335878870163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399023962144223919246775 5098535943216335878870163)
        ·
          refine ⟨7647803914824503818305245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5098535943216335878870163 7647803914824503818305245)
          ·
            refine ⟨2867926468059188931864467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7647803914824503818305245 2867926468059188931864467)
            ·
              refine ⟨4301889702088783397796701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2867926468059188931864467 4301889702088783397796701)
              ·
                refine ⟨1613208638283293774173763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4301889702088783397796701 1613208638283293774173763)
                ·
                  refine ⟨2419812957424940661260645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613208638283293774173763 2419812957424940661260645)
                  ·
                    refine ⟨453714929517176373986371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2419812957424940661260645 453714929517176373986371)
                    ·
                      rfl

theorem cell22_1325410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1325410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325410 prefixEnd_1325410 := by exact prefixLift 1325410
  have htrace : WordTrace (prefixWord ++ tailWord_1325410) baseStart_1325410 baseEnd_1325410 := by
    simpa [prefixWord, tailWord_1325410, baseEnd_1325410] using wordTrace_append hprefix tailTrace_1325410
  have hstable : (prefixWord ++ tailWord_1325410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325410).length < 2 ^ (prefixWord ++ tailWord_1325410).sum := by decide
  have hdescent : baseEnd_1325410 < baseStart_1325410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325423 : List Nat := [1, 1, 2, 1, 3, 1, 2, 6, 2, 3]
def baseStart_1325423 : Nat := 118140960795 + 1325423 * 2 ^ 59
def prefixEnd_1325423 : Nat := 4983230072969 + 3 ^ 40 * 1325423 * 2
def baseEnd_1325423 : Nat := 453719379682848673411331

theorem tailTrace_1325423 : CollatzResearch.WordTrace tailWord_1325423 prefixEnd_1325423 453719379682848673411331 := by
  unfold tailWord_1325423
  simp only [CollatzResearch.WordTrace]
  refine ⟨48342148277226310071732923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32228098851484206714488615 48342148277226310071732923)
  ·
    refine ⟨72513222415839465107599385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48342148277226310071732923 72513222415839465107599385)
    ·
      refine ⟨54384916811879598830699539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72513222415839465107599385 54384916811879598830699539)
      ·
        refine ⟨81577375217819398246049309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54384916811879598830699539 81577375217819398246049309)
        ·
          refine ⟨30591515706682274342268491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81577375217819398246049309 30591515706682274342268491)
          ·
            refine ⟨45887273560023411513402737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30591515706682274342268491 45887273560023411513402737)
            ·
              refine ⟨34415455170017558635052053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45887273560023411513402737 34415455170017558635052053)
              ·
                refine ⟨1613224461094573061018065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34415455170017558635052053 1613224461094573061018065)
                ·
                  refine ⟨1209918345820929795763549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1613224461094573061018065 1209918345820929795763549)
                  ·
                    refine ⟨453719379682848673411331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1209918345820929795763549 453719379682848673411331)
                    ·
                      rfl

theorem cell22_1325423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 3].length) (baseStart_1325423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325423 prefixEnd_1325423 := by exact prefixLift 1325423
  have htrace : WordTrace (prefixWord ++ tailWord_1325423) baseStart_1325423 baseEnd_1325423 := by
    simpa [prefixWord, tailWord_1325423, baseEnd_1325423] using wordTrace_append hprefix tailTrace_1325423
  have hstable : (prefixWord ++ tailWord_1325423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325423).length < 2 ^ (prefixWord ++ tailWord_1325423).sum := by decide
  have hdescent : baseEnd_1325423 < baseStart_1325423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325470 : List Nat := [4, 3, 1, 2, 1, 3, 8]
def baseStart_1325470 : Nat := 118140960795 + 1325470 * 2 ^ 59
def prefixEnd_1325470 : Nat := 4983230072969 + 3 ^ 40 * 1325470 * 2
def baseEnd_1325470 : Nat := 16805017360865045092081

theorem tailTrace_1325470 : CollatzResearch.WordTrace tailWord_1325470 prefixEnd_1325470 16805017360865045092081 := by
  unfold tailWord_1325470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6042982813507004637336733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32229241672037358065795909 6042982813507004637336733)
  ·
    refine ⟨2266118555065126739001275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6042982813507004637336733 2266118555065126739001275)
    ·
      refine ⟨3399177832597690108501913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2266118555065126739001275 3399177832597690108501913)
      ·
        refine ⟨2549383374448267581376435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3399177832597690108501913 2549383374448267581376435)
        ·
          refine ⟨3824075061672401372064653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2549383374448267581376435 3824075061672401372064653)
          ·
            refine ⟨1434028148127150514524245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3824075061672401372064653 1434028148127150514524245)
            ·
              refine ⟨16805017360865045092081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1434028148127150514524245 16805017360865045092081)
              ·
                rfl

theorem cell22_1325470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 8].length) (baseStart_1325470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325470 prefixEnd_1325470 := by exact prefixLift 1325470
  have htrace : WordTrace (prefixWord ++ tailWord_1325470) baseStart_1325470 baseEnd_1325470 := by
    simpa [prefixWord, tailWord_1325470, baseEnd_1325470] using wordTrace_append hprefix tailTrace_1325470
  have hstable : (prefixWord ++ tailWord_1325470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325470).length < 2 ^ (prefixWord ++ tailWord_1325470).sum := by decide
  have hdescent : baseEnd_1325470 < baseStart_1325470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325496 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 1, 7]
def baseStart_1325496 : Nat := 118140960795 + 1325496 * 2 ^ 59
def prefixEnd_1325496 : Nat := 4983230072969 + 3 ^ 40 * 1325496 * 2
def baseEnd_1325496 : Nat := 453744369074700816336107

theorem tailTrace_1325496 : CollatzResearch.WordTrace tailWord_1325496 prefixEnd_1325496 453744369074700816336107 := by
  unfold tailWord_1325496
  simp only [CollatzResearch.WordTrace]
  refine ⟨24172405402980921769570171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32229873870641229026093561 24172405402980921769570171)
  ·
    refine ⟨36258608104471382654355257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24172405402980921769570171 36258608104471382654355257)
    ·
      refine ⟨27193956078353536990766443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36258608104471382654355257 27193956078353536990766443)
      ·
        refine ⟨40790934117530305486149665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27193956078353536990766443 40790934117530305486149665)
        ·
          refine ⟨30593200588147729114612249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40790934117530305486149665 30593200588147729114612249)
          ·
            refine ⟨22944900441110796835959187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30593200588147729114612249 22944900441110796835959187)
            ·
              refine ⟨34417350661666195253938781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22944900441110796835959187 34417350661666195253938781)
              ·
                refine ⟨12906506498124823220227043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34417350661666195253938781 12906506498124823220227043)
                ·
                  refine ⟨19359759747187234830340565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12906506498124823220227043 19359759747187234830340565)
                  ·
                    refine ⟨453744369074700816336107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19359759747187234830340565 453744369074700816336107)
                    ·
                      rfl

theorem cell22_1325496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_1325496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325496 prefixEnd_1325496 := by exact prefixLift 1325496
  have htrace : WordTrace (prefixWord ++ tailWord_1325496) baseStart_1325496 baseEnd_1325496 := by
    simpa [prefixWord, tailWord_1325496, baseEnd_1325496] using wordTrace_append hprefix tailTrace_1325496
  have hstable : (prefixWord ++ tailWord_1325496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325496).length < 2 ^ (prefixWord ++ tailWord_1325496).sum := by decide
  have hdescent : baseEnd_1325496 < baseStart_1325496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325543 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 6]
def baseStart_1325543 : Nat := 118140960795 + 1325543 * 2 ^ 59
def prefixEnd_1325543 : Nat := 4983230072969 + 3 ^ 40 * 1325543 * 2
def baseEnd_1325543 : Nat := 151253486045069453470321

theorem tailTrace_1325543 : CollatzResearch.WordTrace tailWord_1325543 prefixEnd_1325543 151253486045069453470321 := by
  unfold tailWord_1325543
  simp only [CollatzResearch.WordTrace]
  refine ⟨48346525036791570566101283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32231016691194380377400855 48346525036791570566101283)
  ·
    refine ⟨72519787555187355849151925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48346525036791570566101283 72519787555187355849151925)
    ·
      refine ⟨6798730083298814610857993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72519787555187355849151925 6798730083298814610857993)
      ·
        refine ⟨5099047562474110958143495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6798730083298814610857993 5099047562474110958143495)
        ·
          refine ⟨7648571343711166437215243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5099047562474110958143495 7648571343711166437215243)
          ·
            refine ⟨11472857015566749655822865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7648571343711166437215243 11472857015566749655822865)
            ·
              refine ⟨8604642761675062241867149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11472857015566749655822865 8604642761675062241867149)
              ·
                refine ⟨3226741035628148340700181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8604642761675062241867149 3226741035628148340700181)
                ·
                  refine ⟨151253486045069453470321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3226741035628148340700181 151253486045069453470321)
                  ·
                    rfl

theorem cell22_1325543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 6].length) (baseStart_1325543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325543 prefixEnd_1325543 := by exact prefixLift 1325543
  have htrace : WordTrace (prefixWord ++ tailWord_1325543) baseStart_1325543 baseEnd_1325543 := by
    simpa [prefixWord, tailWord_1325543, baseEnd_1325543] using wordTrace_append hprefix tailTrace_1325543
  have hstable : (prefixWord ++ tailWord_1325543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325543).length < 2 ^ (prefixWord ++ tailWord_1325543).sum := by decide
  have hdescent : baseEnd_1325543 < baseStart_1325543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325592 : List Nat := [2, 1, 2, 3, 3, 1, 3, 2, 2, 3]
def baseStart_1325592 : Nat := 118140960795 + 1325592 * 2 ^ 59
def prefixEnd_1325592 : Nat := 4983230072969 + 3 ^ 40 * 1325592 * 2
def baseEnd_1325592 : Nat := 453777231836588565935813

theorem tailTrace_1325592 : CollatzResearch.WordTrace tailWord_1325592 prefixEnd_1325592 453777231836588565935813 := by
  unfold tailWord_1325592
  simp only [CollatzResearch.WordTrace]
  refine ⟨24174156106807025967317515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32232208142409367956423353 24174156106807025967317515)
  ·
    refine ⟨36261234160210538950976273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24174156106807025967317515 36261234160210538950976273)
    ·
      refine ⟨27195925620157904213232205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36261234160210538950976273 27195925620157904213232205)
      ·
        refine ⟨10198472107559214079962077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27195925620157904213232205 10198472107559214079962077)
        ·
          refine ⟨3824427040334705279985779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10198472107559214079962077 3824427040334705279985779)
          ·
            refine ⟨5736640560502057919978669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3824427040334705279985779 5736640560502057919978669)
            ·
              refine ⟨2151240210188271719992001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5736640560502057919978669 2151240210188271719992001)
              ·
                refine ⟨1613430157641203789994001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2151240210188271719992001 1613430157641203789994001)
                ·
                  refine ⟨1210072618230902842495501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1613430157641203789994001 1210072618230902842495501)
                  ·
                    refine ⟨453777231836588565935813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210072618230902842495501 453777231836588565935813)
                    ·
                      rfl

theorem cell22_1325592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_1325592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325592 prefixEnd_1325592 := by exact prefixLift 1325592
  have htrace : WordTrace (prefixWord ++ tailWord_1325592) baseStart_1325592 baseEnd_1325592 := by
    simpa [prefixWord, tailWord_1325592, baseEnd_1325592] using wordTrace_append hprefix tailTrace_1325592
  have hstable : (prefixWord ++ tailWord_1325592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325592).length < 2 ^ (prefixWord ++ tailWord_1325592).sum := by decide
  have hdescent : baseEnd_1325592 < baseStart_1325592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325618 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_1325618 : Nat := 118140960795 + 1325618 * 2 ^ 59
def prefixEnd_1325618 : Nat := 4983230072969 + 3 ^ 40 * 1325618 * 2
def baseEnd_1325618 : Nat := 453786132167933164785733

theorem tailTrace_1325618 : CollatzResearch.WordTrace tailWord_1325618 prefixEnd_1325618 453786132167933164785733 := by
  unfold tailWord_1325618
  simp only [CollatzResearch.WordTrace]
  refine ⟨12087315127879964593770377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32232840341013238916721005 12087315127879964593770377)
  ·
    refine ⟨9065486345909973445327783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12087315127879964593770377 9065486345909973445327783)
    ·
      refine ⟨13598229518864960167991675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9065486345909973445327783 13598229518864960167991675)
      ·
        refine ⟨20397344278297440251987513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13598229518864960167991675 20397344278297440251987513)
        ·
          refine ⟨15298008208723080188990635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20397344278297440251987513 15298008208723080188990635)
          ·
            refine ⟨22947012313084620283485953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15298008208723080188990635 22947012313084620283485953)
            ·
              refine ⟨17210259234813465212614465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22947012313084620283485953 17210259234813465212614465)
              ·
                refine ⟨12907694426110098909460849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17210259234813465212614465 12907694426110098909460849)
                ·
                  refine ⟨9680770819582574182095637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12907694426110098909460849 9680770819582574182095637)
                  ·
                    refine ⟨453786132167933164785733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9680770819582574182095637 453786132167933164785733)
                    ·
                      rfl

theorem cell22_1325618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_1325618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325618 prefixEnd_1325618 := by exact prefixLift 1325618
  have htrace : WordTrace (prefixWord ++ tailWord_1325618) baseStart_1325618 baseEnd_1325618 := by
    simpa [prefixWord, tailWord_1325618, baseEnd_1325618] using wordTrace_append hprefix tailTrace_1325618
  have hstable : (prefixWord ++ tailWord_1325618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325618).length < 2 ^ (prefixWord ++ tailWord_1325618).sum := by decide
  have hdescent : baseEnd_1325618 < baseStart_1325618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325622 : List Nat := [5, 1, 2, 1, 2, 1, 4, 6]
def baseStart_1325622 : Nat := 118140960795 + 1325622 * 2 ^ 59
def prefixEnd_1325622 : Nat := 4983230072969 + 3 ^ 40 * 1325622 * 2
def baseEnd_1325622 : Nat := 50420833494408720853969

theorem tailTrace_1325622 : CollatzResearch.WordTrace tailWord_1325622 prefixEnd_1325622 50420833494408720853969 := by
  unfold tailWord_1325622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3021837900219085441139195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32232937602336911372151413 3021837900219085441139195)
  ·
    refine ⟨4532756850328628161708793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3021837900219085441139195 4532756850328628161708793)
    ·
      refine ⟨3399567637746471121281595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4532756850328628161708793 3399567637746471121281595)
      ·
        refine ⟨5099351456619706681922393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399567637746471121281595 5099351456619706681922393)
        ·
          refine ⟨3824513592464780011441795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5099351456619706681922393 3824513592464780011441795)
          ·
            refine ⟨5736770388697170017162693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3824513592464780011441795 5736770388697170017162693)
            ·
              refine ⟨1075644447880719378218005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5736770388697170017162693 1075644447880719378218005)
              ·
                refine ⟨50420833494408720853969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1075644447880719378218005 50420833494408720853969)
                ·
                  rfl

theorem cell22_1325622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_1325622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325622 prefixEnd_1325622 := by exact prefixLift 1325622
  have htrace : WordTrace (prefixWord ++ tailWord_1325622) baseStart_1325622 baseEnd_1325622 := by
    simpa [prefixWord, tailWord_1325622, baseEnd_1325622] using wordTrace_append hprefix tailTrace_1325622
  have hstable : (prefixWord ++ tailWord_1325622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325622).length < 2 ^ (prefixWord ++ tailWord_1325622).sum := by decide
  have hdescent : baseEnd_1325622 < baseStart_1325622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325648 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 2, 5]
def baseStart_1325648 : Nat := 118140960795 + 1325648 * 2 ^ 59
def prefixEnd_1325648 : Nat := 4983230072969 + 3 ^ 40 * 1325648 * 2
def baseEnd_1325648 : Nat := 453796401781023086535641

theorem tailTrace_1325648 : CollatzResearch.WordTrace tailWord_1325648 prefixEnd_1325648 453796401781023086535641 := by
  unfold tailWord_1325648
  simp only [CollatzResearch.WordTrace]
  refine ⟨24175177350705586749336799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32233569800940782332449065 24175177350705586749336799)
  ·
    refine ⟨36262766026058380124005199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24175177350705586749336799 36262766026058380124005199)
    ·
      refine ⟨54394149039087570186007799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36262766026058380124005199 54394149039087570186007799)
      ·
        refine ⟨81591223558631355279011699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54394149039087570186007799 81591223558631355279011699)
        ·
          refine ⟨122386835337947032918517549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81591223558631355279011699 122386835337947032918517549)
          ·
            refine ⟨45895063251730137344444081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122386835337947032918517549 45895063251730137344444081)
            ·
              refine ⟨34421297438797603008333061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45895063251730137344444081 34421297438797603008333061)
              ·
                refine ⟨6453993269774550564062449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34421297438797603008333061 6453993269774550564062449)
                ·
                  refine ⟨4840494952330912923046837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6453993269774550564062449 4840494952330912923046837)
                  ·
                    refine ⟨453796401781023086535641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4840494952330912923046837 453796401781023086535641)
                    ·
                      rfl

theorem cell22_1325648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_1325648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325648 prefixEnd_1325648 := by exact prefixLift 1325648
  have htrace : WordTrace (prefixWord ++ tailWord_1325648) baseStart_1325648 baseEnd_1325648 := by
    simpa [prefixWord, tailWord_1325648, baseEnd_1325648] using wordTrace_append hprefix tailTrace_1325648
  have hstable : (prefixWord ++ tailWord_1325648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325648).length < 2 ^ (prefixWord ++ tailWord_1325648).sum := by decide
  have hdescent : baseEnd_1325648 < baseStart_1325648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325650 : List Nat := [3, 2, 2, 1, 2, 1, 2, 4, 5]
def baseStart_1325650 : Nat := 118140960795 + 1325650 * 2 ^ 59
def prefixEnd_1325650 : Nat := 4983230072969 + 3 ^ 40 * 1325650 * 2
def baseEnd_1325650 : Nat := 151265695473965249328545

theorem tailTrace_1325650 : CollatzResearch.WordTrace tailWord_1325650 prefixEnd_1325650 151265695473965249328545 := by
  unfold tailWord_1325650
  simp only [CollatzResearch.WordTrace]
  refine ⟨12087606911850981960061601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32233618431602618560164269 12087606911850981960061601)
  ·
    refine ⟨9065705183888236470046201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12087606911850981960061601 9065705183888236470046201)
    ·
      refine ⟨6799278887916177352534651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9065705183888236470046201 6799278887916177352534651)
      ·
        refine ⟨10198918331874266028801977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6799278887916177352534651 10198918331874266028801977)
        ·
          refine ⟨7649188748905699521601483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10198918331874266028801977 7649188748905699521601483)
          ·
            refine ⟨11473783123358549282402225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7649188748905699521601483 11473783123358549282402225)
            ·
              refine ⟨8605337342518911961801669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11473783123358549282402225 8605337342518911961801669)
              ·
                refine ⟨1613500751722295992837813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8605337342518911961801669 1613500751722295992837813)
                ·
                  refine ⟨151265695473965249328545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1613500751722295992837813 151265695473965249328545)
                  ·
                    rfl

theorem cell22_1325650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_1325650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325650 prefixEnd_1325650 := by exact prefixLift 1325650
  have htrace : WordTrace (prefixWord ++ tailWord_1325650) baseStart_1325650 baseEnd_1325650 := by
    simpa [prefixWord, tailWord_1325650, baseEnd_1325650] using wordTrace_append hprefix tailTrace_1325650
  have hstable : (prefixWord ++ tailWord_1325650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325650).length < 2 ^ (prefixWord ++ tailWord_1325650).sum := by decide
  have hdescent : baseEnd_1325650 < baseStart_1325650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325710 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_1325710 : Nat := 118140960795 + 1325710 * 2 ^ 59
def prefixEnd_1325710 : Nat := 4983230072969 + 3 ^ 40 * 1325710 * 2
def baseEnd_1325710 : Nat := 453817625648075591485451

theorem tailTrace_1325710 : CollatzResearch.WordTrace tailWord_1325710 prefixEnd_1325710 453817625648075591485451 := by
  unfold tailWord_1325710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6044077003398319760928823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32235077351457705391620389 6044077003398319760928823)
  ·
    refine ⟨9066115505097479641393235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6044077003398319760928823 9066115505097479641393235)
    ·
      refine ⟨13599173257646219462089853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9066115505097479641393235 13599173257646219462089853)
      ·
        refine ⟨5099689971617332298283695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13599173257646219462089853 5099689971617332298283695)
        ·
          refine ⟨7649534957425998447425543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5099689971617332298283695 7649534957425998447425543)
          ·
            refine ⟨11474302436138997671138315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7649534957425998447425543 11474302436138997671138315)
            ·
              refine ⟨17211453654208496506707473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11474302436138997671138315 17211453654208496506707473)
              ·
                refine ⟨12908590240656372380030605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17211453654208496506707473 12908590240656372380030605)
                ·
                  refine ⟨4840721340246139642511477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12908590240656372380030605 4840721340246139642511477)
                  ·
                    refine ⟨453817625648075591485451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4840721340246139642511477 453817625648075591485451)
                    ·
                      rfl

theorem cell22_1325710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_1325710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325710 prefixEnd_1325710 := by exact prefixLift 1325710
  have htrace : WordTrace (prefixWord ++ tailWord_1325710) baseStart_1325710 baseEnd_1325710 := by
    simpa [prefixWord, tailWord_1325710, baseEnd_1325710] using wordTrace_append hprefix tailTrace_1325710
  have hstable : (prefixWord ++ tailWord_1325710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325710).length < 2 ^ (prefixWord ++ tailWord_1325710).sum := by decide
  have hdescent : baseEnd_1325710 < baseStart_1325710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325725 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_1325725 : Nat := 118140960795 + 1325725 * 2 ^ 59
def prefixEnd_1325725 : Nat := 4983230072969 + 3 ^ 40 * 1325725 * 2
def baseEnd_1325725 : Nat := 453822760454620552360405

theorem tailTrace_1325725 : CollatzResearch.WordTrace tailWord_1325725 prefixEnd_1325725 453822760454620552360405 := by
  unfold tailWord_1325725
  simp only [CollatzResearch.WordTrace]
  refine ⟨48353163122132215649226629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32235442081421477099484419 48353163122132215649226629)
  ·
    refine ⟨9066218085399790434229993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48353163122132215649226629 9066218085399790434229993)
    ·
      refine ⟨6799663564049842825672495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9066218085399790434229993 6799663564049842825672495)
      ·
        refine ⟨10199495346074764238508743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6799663564049842825672495 10199495346074764238508743)
        ·
          refine ⟨15299243019112146357763115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10199495346074764238508743 15299243019112146357763115)
          ·
            refine ⟨22948864528668219536644673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15299243019112146357763115 22948864528668219536644673)
            ·
              refine ⟨17211648396501164652483505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22948864528668219536644673 17211648396501164652483505)
              ·
                refine ⟨12908736297375873489362629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17211648396501164652483505 12908736297375873489362629)
                ·
                  refine ⟨2420388055757976279255493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12908736297375873489362629 2420388055757976279255493)
                  ·
                    refine ⟨453822760454620552360405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2420388055757976279255493 453822760454620552360405)
                    ·
                      rfl

theorem cell22_1325725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_1325725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325725 prefixEnd_1325725 := by exact prefixLift 1325725
  have htrace : WordTrace (prefixWord ++ tailWord_1325725) baseStart_1325725 baseEnd_1325725 := by
    simpa [prefixWord, tailWord_1325725, baseEnd_1325725] using wordTrace_append hprefix tailTrace_1325725
  have hstable : (prefixWord ++ tailWord_1325725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325725).length < 2 ^ (prefixWord ++ tailWord_1325725).sum := by decide
  have hdescent : baseEnd_1325725 < baseStart_1325725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325761 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1325761 : Nat := 118140960795 + 1325761 * 2 ^ 59
def prefixEnd_1325761 : Nat := 4983230072969 + 3 ^ 40 * 1325761 * 2
def baseEnd_1325761 : Nat := 453835083990328458460295

theorem tailTrace_1325761 : CollatzResearch.WordTrace tailWord_1325761 prefixEnd_1325761 453835083990328458460295 := by
  unfold tailWord_1325761
  simp only [CollatzResearch.WordTrace]
  refine ⟨48354476150001793797537137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32236317433334529198358091 48354476150001793797537137)
  ·
    refine ⟨36265857112501345348152853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48354476150001793797537137 36265857112501345348152853)
    ·
      refine ⟨1699962052148500563194665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36265857112501345348152853 1699962052148500563194665)
      ·
        refine ⟨1274971539111375422395999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1699962052148500563194665 1274971539111375422395999)
        ·
          refine ⟨1912457308667063133593999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274971539111375422395999 1912457308667063133593999)
          ·
            refine ⟨2868685963000594700390999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912457308667063133593999 2868685963000594700390999)
            ·
              refine ⟨4303028944500892050586499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2868685963000594700390999 4303028944500892050586499)
              ·
                refine ⟨6454543416751338075879749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303028944500892050586499 6454543416751338075879749)
                ·
                  refine ⟨1210226890640875889227453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6454543416751338075879749 1210226890640875889227453)
                  ·
                    refine ⟨453835083990328458460295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210226890640875889227453 453835083990328458460295)
                    ·
                      rfl

theorem cell22_1325761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1325761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325761 prefixEnd_1325761 := by exact prefixLift 1325761
  have htrace : WordTrace (prefixWord ++ tailWord_1325761) baseStart_1325761 baseEnd_1325761 := by
    simpa [prefixWord, tailWord_1325761, baseEnd_1325761] using wordTrace_append hprefix tailTrace_1325761
  have hstable : (prefixWord ++ tailWord_1325761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325761).length < 2 ^ (prefixWord ++ tailWord_1325761).sum := by decide
  have hdescent : baseEnd_1325761 < baseStart_1325761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325806 : List Nat := [4, 1, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_1325806 : Nat := 118140960795 + 1325806 * 2 ^ 59
def prefixEnd_1325806 : Nat := 4983230072969 + 3 ^ 40 * 1325806 * 2
def baseEnd_1325806 : Nat := 453850488409963341085157

theorem tailTrace_1325806 : CollatzResearch.WordTrace tailWord_1325806 prefixEnd_1325806 453850488409963341085157 := by
  unfold tailWord_1325806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6044514679354845810365659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32237411623225844321950181 6044514679354845810365659)
  ·
    refine ⟨9066772019032268715548489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6044514679354845810365659 9066772019032268715548489)
    ·
      refine ⟨6800079014274201536661367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9066772019032268715548489 6800079014274201536661367)
      ·
        refine ⟨10200118521411302304992051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6800079014274201536661367 10200118521411302304992051)
        ·
          refine ⟨15300177782116953457488077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10200118521411302304992051 15300177782116953457488077)
          ·
            refine ⟨5737566668293857546558029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15300177782116953457488077 5737566668293857546558029)
            ·
              refine ⟨2151587500610196579959261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5737566668293857546558029 2151587500610196579959261)
              ·
                refine ⟨806845312728823717484723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2151587500610196579959261 806845312728823717484723)
                ·
                  refine ⟨1210267969093235576227085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806845312728823717484723 1210267969093235576227085)
                  ·
                    refine ⟨453850488409963341085157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210267969093235576227085 453850488409963341085157)
                    ·
                      rfl

theorem cell22_1325806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_1325806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325806 prefixEnd_1325806 := by exact prefixLift 1325806
  have htrace : WordTrace (prefixWord ++ tailWord_1325806) baseStart_1325806 baseEnd_1325806 := by
    simpa [prefixWord, tailWord_1325806, baseEnd_1325806] using wordTrace_append hprefix tailTrace_1325806
  have hstable : (prefixWord ++ tailWord_1325806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325806).length < 2 ^ (prefixWord ++ tailWord_1325806).sum := by decide
  have hdescent : baseEnd_1325806 < baseStart_1325806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325815 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 5, 4]
def baseStart_1325815 : Nat := 118140960795 + 1325815 * 2 ^ 59
def prefixEnd_1325815 : Nat := 4983230072969 + 3 ^ 40 * 1325815 * 2
def baseEnd_1325815 : Nat := 453853569293890317610129

theorem tailTrace_1325815 : CollatzResearch.WordTrace tailWord_1325815 prefixEnd_1325815 453853569293890317610129 := by
  unfold tailWord_1325815
  simp only [CollatzResearch.WordTrace]
  refine ⟨48356445691806161020002899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32237630461204107346668599 48356445691806161020002899)
  ·
    refine ⟨72534668537709241530004349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48356445691806161020002899 72534668537709241530004349)
    ·
      refine ⟨27200500701640965573751631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72534668537709241530004349 27200500701640965573751631)
      ·
        refine ⟨40800751052461448360627447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27200500701640965573751631 40800751052461448360627447)
        ·
          refine ⟨61201126578692172540941171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40800751052461448360627447 61201126578692172540941171)
          ·
            refine ⟨91801689868038258811411757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61201126578692172540941171 91801689868038258811411757)
            ·
              refine ⟨34425633700514347054279409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91801689868038258811411757 34425633700514347054279409)
              ·
                refine ⟨25819225275385760290709557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34425633700514347054279409 25819225275385760290709557)
                ·
                  refine ⟨2420552369567415027254021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25819225275385760290709557 2420552369567415027254021)
                  ·
                    refine ⟨453853569293890317610129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2420552369567415027254021 453853569293890317610129)
                    ·
                      rfl

theorem cell22_1325815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_1325815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325815 prefixEnd_1325815 := by exact prefixLift 1325815
  have htrace : WordTrace (prefixWord ++ tailWord_1325815) baseStart_1325815 baseEnd_1325815 := by
    simpa [prefixWord, tailWord_1325815, baseEnd_1325815] using wordTrace_append hprefix tailTrace_1325815
  have hstable : (prefixWord ++ tailWord_1325815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325815).length < 2 ^ (prefixWord ++ tailWord_1325815).sum := by decide
  have hdescent : baseEnd_1325815 < baseStart_1325815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325864 : List Nat := [2, 1, 5, 1, 1, 1, 2, 5, 4]
def baseStart_1325864 : Nat := 118140960795 + 1325864 * 2 ^ 59
def prefixEnd_1325864 : Nat := 4983230072969 + 3 ^ 40 * 1325864 * 2
def baseEnd_1325864 : Nat := 151290114331756841044993

theorem tailTrace_1325864 : CollatzResearch.WordTrace tailWord_1325864 prefixEnd_1325864 151290114331756841044993 := by
  unfold tailWord_1325864
  simp only [CollatzResearch.WordTrace]
  refine ⟨24179116434314321194268323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32238821912419094925691097 24179116434314321194268323)
  ·
    refine ⟨36268674651471481791402485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24179116434314321194268323 36268674651471481791402485)
    ·
      refine ⟨3400188248575451417943983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36268674651471481791402485 3400188248575451417943983)
      ·
        refine ⟨5100282372863177126915975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3400188248575451417943983 5100282372863177126915975)
        ·
          refine ⟨7650423559294765690373963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5100282372863177126915975 7650423559294765690373963)
          ·
            refine ⟨11475635338942148535560945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7650423559294765690373963 11475635338942148535560945)
            ·
              refine ⟨8606726504206611401670709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11475635338942148535560945 8606726504206611401670709)
              ·
                refine ⟨806880609769369818906629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8606726504206611401670709 806880609769369818906629)
                ·
                  refine ⟨151290114331756841044993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 806880609769369818906629 151290114331756841044993)
                  ·
                    rfl

theorem cell22_1325864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 4].length) (baseStart_1325864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325864 prefixEnd_1325864 := by exact prefixLift 1325864
  have htrace : WordTrace (prefixWord ++ tailWord_1325864) baseStart_1325864 baseEnd_1325864 := by
    simpa [prefixWord, tailWord_1325864, baseEnd_1325864] using wordTrace_append hprefix tailTrace_1325864
  have hstable : (prefixWord ++ tailWord_1325864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325864).length < 2 ^ (prefixWord ++ tailWord_1325864).sum := by decide
  have hdescent : baseEnd_1325864 < baseStart_1325864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325875 : List Nat := [1, 1, 1, 2, 6, 11]
def baseStart_1325875 : Nat := 118140960795 + 1325875 * 2 ^ 59
def prefixEnd_1325875 : Nat := 4983230072969 + 3 ^ 40 * 1325875 * 2
def baseEnd_1325875 : Nat := 5603384055803335322345

theorem tailTrace_1325875 : CollatzResearch.WordTrace tailWord_1325875 prefixEnd_1325875 5603384055803335322345 := by
  unfold tailWord_1325875
  simp only [CollatzResearch.WordTrace]
  refine ⟨48358634071588791267187079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32239089381059194178124719 48358634071588791267187079)
  ·
    refine ⟨72537951107383186900780619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48358634071588791267187079 72537951107383186900780619)
    ·
      refine ⟨108806926661074780351170929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72537951107383186900780619 108806926661074780351170929)
      ·
        refine ⟨81605194995806085263378197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108806926661074780351170929 81605194995806085263378197)
        ·
          refine ⟨3825243515428410246720853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81605194995806085263378197 3825243515428410246720853)
          ·
            refine ⟨5603384055803335322345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3825243515428410246720853 5603384055803335322345)
            ·
              rfl

theorem cell22_1325875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 11].length) (baseStart_1325875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325875 prefixEnd_1325875 := by exact prefixLift 1325875
  have htrace : WordTrace (prefixWord ++ tailWord_1325875) baseStart_1325875 baseEnd_1325875 := by
    simpa [prefixWord, tailWord_1325875, baseEnd_1325875] using wordTrace_append hprefix tailTrace_1325875
  have hstable : (prefixWord ++ tailWord_1325875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325875).length < 2 ^ (prefixWord ++ tailWord_1325875).sum := by decide
  have hdescent : baseEnd_1325875 < baseStart_1325875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325879 : List Nat := [1, 1, 3, 1, 2, 1, 6, 2, 2, 3]
def baseStart_1325879 : Nat := 118140960795 + 1325879 * 2 ^ 59
def prefixEnd_1325879 : Nat := 4983230072969 + 3 ^ 40 * 1325879 * 2
def baseEnd_1325879 : Nat := 453875477801815484009933

theorem tailTrace_1325879 : CollatzResearch.WordTrace tailWord_1325879 prefixEnd_1325879 453875477801815484009933 := by
  unfold tailWord_1325879
  simp only [CollatzResearch.WordTrace]
  refine ⟨48358779963574299950332691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32239186642382866633555127 48358779963574299950332691)
  ·
    refine ⟨72538169945361449925499037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48358779963574299950332691 72538169945361449925499037)
    ·
      refine ⟨27201813729510543722062139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72538169945361449925499037 27201813729510543722062139)
      ·
        refine ⟨40802720594265815583093209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27201813729510543722062139 40802720594265815583093209)
        ·
          refine ⟨30602040445699361687319907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40802720594265815583093209 30602040445699361687319907)
          ·
            refine ⟨45903060668549042530979861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30602040445699361687319907 45903060668549042530979861)
            ·
              refine ⟨2151705968838236368639681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45903060668549042530979861 2151705968838236368639681)
              ·
                refine ⟨1613779476628677276479761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2151705968838236368639681 1613779476628677276479761)
                ·
                  refine ⟨1210334607471507957359821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1613779476628677276479761 1210334607471507957359821)
                  ·
                    refine ⟨453875477801815484009933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210334607471507957359821 453875477801815484009933)
                    ·
                      rfl

theorem cell22_1325879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_1325879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325879 prefixEnd_1325879 := by exact prefixLift 1325879
  have htrace : WordTrace (prefixWord ++ tailWord_1325879) baseStart_1325879 baseEnd_1325879 := by
    simpa [prefixWord, tailWord_1325879, baseEnd_1325879] using wordTrace_append hprefix tailTrace_1325879
  have hstable : (prefixWord ++ tailWord_1325879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325879).length < 2 ^ (prefixWord ++ tailWord_1325879).sum := by decide
  have hdescent : baseEnd_1325879 < baseStart_1325879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325937 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 7]
def baseStart_1325937 : Nat := 118140960795 + 1325937 * 2 ^ 59
def prefixEnd_1325937 : Nat := 4983230072969 + 3 ^ 40 * 1325937 * 2
def baseEnd_1325937 : Nat := 151298444129040888686585

theorem tailTrace_1325937 : CollatzResearch.WordTrace tailWord_1325937 prefixEnd_1325937 151298444129040888686585 := by
  unfold tailWord_1325937
  simp only [CollatzResearch.WordTrace]
  refine ⟨48360895397364175855944065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32240596931576117237296043 48360895397364175855944065)
  ·
    refine ⟨36270671548023131891958049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48360895397364175855944065 36270671548023131891958049)
    ·
      refine ⟨27203003661017348918968537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36270671548023131891958049 27203003661017348918968537)
      ·
        refine ⟨20402252745763011689226403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27203003661017348918968537 20402252745763011689226403)
        ·
          refine ⟨30603379118644517533839605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20402252745763011689226403 30603379118644517533839605)
          ·
            refine ⟨2869066792372923518797463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30603379118644517533839605 2869066792372923518797463)
            ·
              refine ⟨4303600188559385278196195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869066792372923518797463 4303600188559385278196195)
              ·
                refine ⟨6455400282839077917294293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303600188559385278196195 6455400282839077917294293)
                ·
                  refine ⟨151298444129040888686585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6455400282839077917294293 151298444129040888686585)
                  ·
                    rfl

theorem cell22_1325937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_1325937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325937 prefixEnd_1325937 := by exact prefixLift 1325937
  have htrace : WordTrace (prefixWord ++ tailWord_1325937) baseStart_1325937 baseEnd_1325937 := by
    simpa [prefixWord, tailWord_1325937, baseEnd_1325937] using wordTrace_append hprefix tailTrace_1325937
  have hstable : (prefixWord ++ tailWord_1325937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325937).length < 2 ^ (prefixWord ++ tailWord_1325937).sum := by decide
  have hdescent : baseEnd_1325937 < baseStart_1325937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325941 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1325941 : Nat := 118140960795 + 1325941 * 2 ^ 59
def prefixEnd_1325941 : Nat := 4983230072969 + 3 ^ 40 * 1325941 * 2
def baseEnd_1325941 : Nat := 453896701668867988959743

theorem tailTrace_1325941 : CollatzResearch.WordTrace tailWord_1325941 prefixEnd_1325941 453896701668867988959743 := by
  unfold tailWord_1325941
  simp only [CollatzResearch.WordTrace]
  refine ⟨48361041289349684539089677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32240694192899789692726451 48361041289349684539089677)
  ·
    refine ⟨18135390483506131702158629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48361041289349684539089677 18135390483506131702158629)
    ·
      refine ⟨3400385715657399694154743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18135390483506131702158629 3400385715657399694154743)
      ·
        refine ⟨5100578573486099541232115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3400385715657399694154743 5100578573486099541232115)
        ·
          refine ⟨7650867860229149311848173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5100578573486099541232115 7650867860229149311848173)
          ·
            refine ⟨2869075447585930991943065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7650867860229149311848173 2869075447585930991943065)
            ·
              refine ⟨2151806585689448243957299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2869075447585930991943065 2151806585689448243957299)
              ·
                refine ⟨3227709878534172365935949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151806585689448243957299 3227709878534172365935949)
                ·
                  refine ⟨1210391204450314637225981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3227709878534172365935949 1210391204450314637225981)
                  ·
                    refine ⟨453896701668867988959743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210391204450314637225981 453896701668867988959743)
                    ·
                      rfl

theorem cell22_1325941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1325941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325941 prefixEnd_1325941 := by exact prefixLift 1325941
  have htrace : WordTrace (prefixWord ++ tailWord_1325941) baseStart_1325941 baseEnd_1325941 := by
    simpa [prefixWord, tailWord_1325941, baseEnd_1325941] using wordTrace_append hprefix tailTrace_1325941
  have hstable : (prefixWord ++ tailWord_1325941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325941).length < 2 ^ (prefixWord ++ tailWord_1325941).sum := by decide
  have hdescent : baseEnd_1325941 < baseStart_1325941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325984 : List Nat := [2, 1, 1, 4, 1, 1, 4, 3, 1, 4]
def baseStart_1325984 : Nat := 118140960795 + 1325984 * 2 ^ 59
def prefixEnd_1325984 : Nat := 4983230072969 + 3 ^ 40 * 1325984 * 2
def baseEnd_1325984 : Nat := 453911421447630210134611

theorem tailTrace_1325984 : CollatzResearch.WordTrace tailWord_1325984 prefixEnd_1325984 453911421447630210134611 := by
  unfold tailWord_1325984
  simp only [CollatzResearch.WordTrace]
  refine ⟨24181304814096951441452503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32241739752129268588603337 24181304814096951441452503)
  ·
    refine ⟨36271957221145427162178755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24181304814096951441452503 36271957221145427162178755)
    ·
      refine ⟨54407935831718140743268133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36271957221145427162178755 54407935831718140743268133)
      ·
        refine ⟨10201487968447151389362775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54407935831718140743268133 10201487968447151389362775)
        ·
          refine ⟨15302231952670727084044163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10201487968447151389362775 15302231952670727084044163)
          ·
            refine ⟨22953347929006090626066245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15302231952670727084044163 22953347929006090626066245)
            ·
              refine ⟨4303752736688641992387421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22953347929006090626066245 4303752736688641992387421)
              ·
                refine ⟨1613907276258240747145283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4303752736688641992387421 1613907276258240747145283)
                ·
                  refine ⟨2420860914387361120717925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613907276258240747145283 2420860914387361120717925)
                  ·
                    refine ⟨453911421447630210134611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2420860914387361120717925 453911421447630210134611)
                    ·
                      rfl

theorem cell22_1325984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_1325984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1325984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1325984 prefixEnd_1325984 := by exact prefixLift 1325984
  have htrace : WordTrace (prefixWord ++ tailWord_1325984) baseStart_1325984 baseEnd_1325984 := by
    simpa [prefixWord, tailWord_1325984, baseEnd_1325984] using wordTrace_append hprefix tailTrace_1325984
  have hstable : (prefixWord ++ tailWord_1325984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325984).length < 2 ^ (prefixWord ++ tailWord_1325984).sum := by decide
  have hdescent : baseEnd_1325984 < baseStart_1325984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326014 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1326014 : Nat := 118140960795 + 1326014 * 2 ^ 59
def prefixEnd_1326014 : Nat := 4983230072969 + 3 ^ 40 * 1326014 * 2
def baseEnd_1326014 : Nat := 453921691060720131884519

theorem tailTrace_1326014 : CollatzResearch.WordTrace tailWord_1326014 prefixEnd_1326014 453921691060720131884519 := by
  unfold tailWord_1326014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6045462977260652250812137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32242469212056812004331397 6045462977260652250812137)
  ·
    refine ⟨4534097232945489188109103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6045462977260652250812137 4534097232945489188109103)
    ·
      refine ⟨6801145849418233782163655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4534097232945489188109103 6801145849418233782163655)
      ·
        refine ⟨10201718774127350673245483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6801145849418233782163655 10201718774127350673245483)
        ·
          refine ⟨15302578161191026009868225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10201718774127350673245483 15302578161191026009868225)
          ·
            refine ⟨11476933620893269507401169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15302578161191026009868225 11476933620893269507401169)
            ·
              refine ⟨8607700215669952130550877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11476933620893269507401169 8607700215669952130550877)
              ·
                refine ⟨3227887580876232048956579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8607700215669952130550877 3227887580876232048956579)
                ·
                  refine ⟨4841831371314348073434869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3227887580876232048956579 4841831371314348073434869)
                  ·
                    refine ⟨453921691060720131884519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4841831371314348073434869 453921691060720131884519)
                    ·
                      rfl

theorem cell22_1326014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1326014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326014 prefixEnd_1326014 := by exact prefixLift 1326014
  have htrace : WordTrace (prefixWord ++ tailWord_1326014) baseStart_1326014 baseEnd_1326014 := by
    simpa [prefixWord, tailWord_1326014, baseEnd_1326014] using wordTrace_append hprefix tailTrace_1326014
  have hstable : (prefixWord ++ tailWord_1326014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326014).length < 2 ^ (prefixWord ++ tailWord_1326014).sum := by decide
  have hdescent : baseEnd_1326014 < baseStart_1326014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326027 : List Nat := [1, 1, 1, 1, 3, 5, 2, 8]
def baseStart_1326027 : Nat := 118140960795 + 1326027 * 2 ^ 59
def prefixEnd_1326027 : Nat := 4983230072969 + 3 ^ 40 * 1326027 * 2
def baseEnd_1326027 : Nat := 50436237914043603478831

theorem tailTrace_1326027 : CollatzResearch.WordTrace tailWord_1326027 prefixEnd_1326027 50436237914043603478831 := by
  unfold tailWord_1326027
  simp only [CollatzResearch.WordTrace]
  refine ⟨48364177967038121226720335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32242785311358747484480223 48364177967038121226720335)
  ·
    refine ⟨72546266950557181840080503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48364177967038121226720335 72546266950557181840080503)
    ·
      refine ⟨108819400425835772760120755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72546266950557181840080503 108819400425835772760120755)
      ·
        refine ⟨163229100638753659140181133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108819400425835772760120755 163229100638753659140181133)
        ·
          refine ⟨61210912739532622177567925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163229100638753659140181133 61210912739532622177567925)
          ·
            refine ⟨5738523069331183329146993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61210912739532622177567925 5738523069331183329146993)
            ·
              refine ⟨4303892301998387496860245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5738523069331183329146993 4303892301998387496860245)
              ·
                refine ⟨50436237914043603478831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4303892301998387496860245 50436237914043603478831)
                ·
                  rfl

theorem cell22_1326027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 8].length) (baseStart_1326027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326027 prefixEnd_1326027 := by exact prefixLift 1326027
  have htrace : WordTrace (prefixWord ++ tailWord_1326027) baseStart_1326027 baseEnd_1326027 := by
    simpa [prefixWord, tailWord_1326027, baseEnd_1326027] using wordTrace_append hprefix tailTrace_1326027
  have hstable : (prefixWord ++ tailWord_1326027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326027).length < 2 ^ (prefixWord ++ tailWord_1326027).sum := by decide
  have hdescent : baseEnd_1326027 < baseStart_1326027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326044 : List Nat := [2, 2, 6, 12]
def baseStart_1326044 : Nat := 118140960795 + 1326044 * 2 ^ 59
def prefixEnd_1326044 : Nat := 4983230072969 + 3 ^ 40 * 1326044 * 2
def baseEnd_1326044 : Nat := 622677586658175656563

theorem tailTrace_1326044 : CollatzResearch.WordTrace tailWord_1326044 prefixEnd_1326044 622677586658175656563 := by
  unfold tailWord_1326044
  simp only [CollatzResearch.WordTrace]
  refine ⟨24182399003988266565044593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32243198671984355420059457 24182399003988266565044593)
  ·
    refine ⟨18136799252991199923783445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24182399003988266565044593 18136799252991199923783445)
    ·
      refine ⟨850162464983962496427349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18136799252991199923783445 850162464983962496427349)
      ·
        refine ⟨622677586658175656563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 850162464983962496427349 622677586658175656563)
        ·
          rfl

theorem cell22_1326044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 12].length) (baseStart_1326044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326044 prefixEnd_1326044 := by exact prefixLift 1326044
  have htrace : WordTrace (prefixWord ++ tailWord_1326044) baseStart_1326044 baseEnd_1326044 := by
    simpa [prefixWord, tailWord_1326044, baseEnd_1326044] using wordTrace_append hprefix tailTrace_1326044
  have hstable : (prefixWord ++ tailWord_1326044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326044).length < 2 ^ (prefixWord ++ tailWord_1326044).sum := by decide
  have hdescent : baseEnd_1326044 < baseStart_1326044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326050 : List Nat := [3, 3, 3, 1, 1, 1, 4, 2, 4]
def baseStart_1326050 : Nat := 118140960795 + 1326050 * 2 ^ 59
def prefixEnd_1326050 : Nat := 4983230072969 + 3 ^ 40 * 1326050 * 2
def baseEnd_1326050 : Nat := 151311338198809345994803

theorem tailTrace_1326050 : CollatzResearch.WordTrace tailWord_1326050 prefixEnd_1326050 151311338198809345994803 := by
  unfold tailWord_1326050
  simp only [CollatzResearch.WordTrace]
  refine ⟨12091254211488699038701901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32243344563969864103205069 12091254211488699038701901)
  ·
    refine ⟨4534220329308262139513213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12091254211488699038701901 4534220329308262139513213)
    ·
      refine ⟨1700332623490598302317455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4534220329308262139513213 1700332623490598302317455)
      ·
        refine ⟨2550498935235897453476183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1700332623490598302317455 2550498935235897453476183)
        ·
          refine ⟨3825748402853846180214275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550498935235897453476183 3825748402853846180214275)
          ·
            refine ⟨5738622604280769270321413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3825748402853846180214275 5738622604280769270321413)
            ·
              refine ⟨1075991738302644238185265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5738622604280769270321413 1075991738302644238185265)
              ·
                refine ⟨806993803726983178638949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075991738302644238185265 806993803726983178638949)
                ·
                  refine ⟨151311338198809345994803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 806993803726983178638949 151311338198809345994803)
                  ·
                    rfl

theorem cell22_1326050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_1326050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326050 prefixEnd_1326050 := by exact prefixLift 1326050
  have htrace : WordTrace (prefixWord ++ tailWord_1326050) baseStart_1326050 baseEnd_1326050 := by
    simpa [prefixWord, tailWord_1326050, baseEnd_1326050] using wordTrace_append hprefix tailTrace_1326050
  have hstable : (prefixWord ++ tailWord_1326050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326050).length < 2 ^ (prefixWord ++ tailWord_1326050).sum := by decide
  have hdescent : baseEnd_1326050 < baseStart_1326050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326072 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 9]
def baseStart_1326072 : Nat := 118140960795 + 1326072 * 2 ^ 59
def prefixEnd_1326072 : Nat := 4983230072969 + 3 ^ 40 * 1326072 * 2
def baseEnd_1326072 : Nat := 151313848548675771311447

theorem tailTrace_1326072 : CollatzResearch.WordTrace tailWord_1326072 prefixEnd_1326072 151313848548675771311447 := by
  unfold tailWord_1326072
  simp only [CollatzResearch.WordTrace]
  refine ⟨24182909625937546956054235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32243879501250062608072313 24182909625937546956054235)
  ·
    refine ⟨36274364438906320434081353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24182909625937546956054235 36274364438906320434081353)
    ·
      refine ⟨27205773329179740325561015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36274364438906320434081353 27205773329179740325561015)
      ·
        refine ⟨40808659993769610488341523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27205773329179740325561015 40808659993769610488341523)
        ·
          refine ⟨61212989990654415732512285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40808659993769610488341523 61212989990654415732512285)
          ·
            refine ⟨22954871246495405899692107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61212989990654415732512285 22954871246495405899692107)
            ·
              refine ⟨34432306869743108849538161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22954871246495405899692107 34432306869743108849538161)
              ·
                refine ⟨25824230152307331637153621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34432306869743108849538161 25824230152307331637153621)
                ·
                  refine ⟨151313848548675771311447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25824230152307331637153621 151313848548675771311447)
                  ·
                    rfl

theorem cell22_1326072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_1326072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326072 prefixEnd_1326072 := by exact prefixLift 1326072
  have htrace : WordTrace (prefixWord ++ tailWord_1326072) baseStart_1326072 baseEnd_1326072 := by
    simpa [prefixWord, tailWord_1326072, baseEnd_1326072] using wordTrace_append hprefix tailTrace_1326072
  have hstable : (prefixWord ++ tailWord_1326072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326072).length < 2 ^ (prefixWord ++ tailWord_1326072).sum := by decide
  have hdescent : baseEnd_1326072 < baseStart_1326072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326076 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 3, 3]
def baseStart_1326076 : Nat := 118140960795 + 1326076 * 2 ^ 59
def prefixEnd_1326076 : Nat := 4983230072969 + 3 ^ 40 * 1326076 * 2
def baseEnd_1326076 : Nat := 453942914927772636834329

theorem tailTrace_1326076 : CollatzResearch.WordTrace tailWord_1326076 prefixEnd_1326076 453942914927772636834329 := by
  unfold tailWord_1326076
  simp only [CollatzResearch.WordTrace]
  refine ⟨24182982571930301297627041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32243976762573735063502721 24182982571930301297627041)
  ·
    refine ⟨18137236928947725973220281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24182982571930301297627041 18137236928947725973220281)
    ·
      refine ⟨13602927696710794479915211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18137236928947725973220281 13602927696710794479915211)
      ·
        refine ⟨20404391545066191719872817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13602927696710794479915211 20404391545066191719872817)
        ·
          refine ⟨15303293658799643789904613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20404391545066191719872817 15303293658799643789904613)
          ·
            refine ⟨2869367561024933210607115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15303293658799643789904613 2869367561024933210607115)
            ·
              refine ⟨4304051341537399815910673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869367561024933210607115 4304051341537399815910673)
              ·
                refine ⟨3228038506153049861933005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4304051341537399815910673 3228038506153049861933005)
                ·
                  refine ⟨1210514439807393698224877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3228038506153049861933005 1210514439807393698224877)
                  ·
                    refine ⟨453942914927772636834329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210514439807393698224877 453942914927772636834329)
                    ·
                      rfl

theorem cell22_1326076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_1326076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326076 prefixEnd_1326076 := by exact prefixLift 1326076
  have htrace : WordTrace (prefixWord ++ tailWord_1326076) baseStart_1326076 baseEnd_1326076 := by
    simpa [prefixWord, tailWord_1326076, baseEnd_1326076] using wordTrace_append hprefix tailTrace_1326076
  have hstable : (prefixWord ++ tailWord_1326076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326076).length < 2 ^ (prefixWord ++ tailWord_1326076).sum := by decide
  have hdescent : baseEnd_1326076 < baseStart_1326076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326078 : List Nat := [4, 2, 2, 2, 2, 1, 3, 6]
def baseStart_1326078 : Nat := 118140960795 + 1326078 * 2 ^ 59
def prefixEnd_1326078 : Nat := 4983230072969 + 3 ^ 40 * 1326078 * 2
def baseEnd_1326078 : Nat := 50438177729849477587147

theorem tailTrace_1326078 : CollatzResearch.WordTrace tailWord_1326078 prefixEnd_1326078 50438177729849477587147 := by
  unfold tailWord_1326078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6045754761231669617103361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32244025393235571291217925 6045754761231669617103361)
  ·
    refine ⟨4534316070923752212827521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6045754761231669617103361 4534316070923752212827521)
    ·
      refine ⟨3400737053192814159620641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4534316070923752212827521 3400737053192814159620641)
      ·
        refine ⟨2550552789894610619715481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3400737053192814159620641 2550552789894610619715481)
        ·
          refine ⟨1912914592420957964786611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2550552789894610619715481 1912914592420957964786611)
          ·
            refine ⟨2869371888631436947179917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912914592420957964786611 2869371888631436947179917)
            ·
              refine ⟨1076014458236788855192469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2869371888631436947179917 1076014458236788855192469)
              ·
                refine ⟨50438177729849477587147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1076014458236788855192469 50438177729849477587147)
                ·
                  rfl

theorem cell22_1326078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_1326078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326078 prefixEnd_1326078 := by exact prefixLift 1326078
  have htrace : WordTrace (prefixWord ++ tailWord_1326078) baseStart_1326078 baseEnd_1326078 := by
    simpa [prefixWord, tailWord_1326078, baseEnd_1326078] using wordTrace_append hprefix tailTrace_1326078
  have hstable : (prefixWord ++ tailWord_1326078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326078).length < 2 ^ (prefixWord ++ tailWord_1326078).sum := by decide
  have hdescent : baseEnd_1326078 < baseStart_1326078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326104 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 2, 5]
def baseStart_1326104 : Nat := 118140960795 + 1326104 * 2 ^ 59
def prefixEnd_1326104 : Nat := 4983230072969 + 3 ^ 40 * 1326104 * 2
def baseEnd_1326104 : Nat := 453952499899989897134243

theorem tailTrace_1326104 : CollatzResearch.WordTrace tailWord_1326104 prefixEnd_1326104 453952499899989897134243 := by
  unfold tailWord_1326104
  simp only [CollatzResearch.WordTrace]
  refine ⟨24183493193879581688636683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32244657591839442251515577 24183493193879581688636683)
  ·
    refine ⟨36275239790819372532955025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24183493193879581688636683 36275239790819372532955025)
    ·
      refine ⟨27206429843114529399716269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36275239790819372532955025 27206429843114529399716269)
      ·
        refine ⟨10202411191167948524893601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27206429843114529399716269 10202411191167948524893601)
        ·
          refine ⟨7651808393375961393670201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10202411191167948524893601 7651808393375961393670201)
          ·
            refine ⟨5738856295031971045252651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7651808393375961393670201 5738856295031971045252651)
            ·
              refine ⟨8608284442547956567878977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5738856295031971045252651 8608284442547956567878977)
              ·
                refine ⟨6456213331910967425909233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8608284442547956567878977 6456213331910967425909233)
                ·
                  refine ⟨4842159998933225569431925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6456213331910967425909233 4842159998933225569431925)
                  ·
                    refine ⟨453952499899989897134243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4842159998933225569431925 453952499899989897134243)
                    ·
                      rfl

theorem cell22_1326104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_1326104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326104 prefixEnd_1326104 := by exact prefixLift 1326104
  have htrace : WordTrace (prefixWord ++ tailWord_1326104) baseStart_1326104 baseEnd_1326104 := by
    simpa [prefixWord, tailWord_1326104, baseEnd_1326104] using wordTrace_append hprefix tailTrace_1326104
  have hstable : (prefixWord ++ tailWord_1326104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326104).length < 2 ^ (prefixWord ++ tailWord_1326104).sum := by decide
  have hdescent : baseEnd_1326104 < baseStart_1326104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326136 : List Nat := [2, 1, 2, 1, 5, 1, 1, 4, 1, 4]
def baseStart_1326136 : Nat := 118140960795 + 1326136 * 2 ^ 59
def prefixEnd_1326136 : Nat := 4983230072969 + 3 ^ 40 * 1326136 * 2
def baseEnd_1326136 : Nat := 453963454153952480334145

theorem tailTrace_1326136 : CollatzResearch.WordTrace tailWord_1326136 prefixEnd_1326136 453963454153952480334145 := by
  unfold tailWord_1326136
  simp only [CollatzResearch.WordTrace]
  refine ⟨24184076761821616421219131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32245435682428821894958841 24184076761821616421219131)
  ·
    refine ⟨36276115142732424631828697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24184076761821616421219131 36276115142732424631828697)
    ·
      refine ⟨27207086357049318473871523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36276115142732424631828697 27207086357049318473871523)
      ·
        refine ⟨40810629535573977710807285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27207086357049318473871523 40810629535573977710807285)
        ·
          refine ⟨3825996518960060410388183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40810629535573977710807285 3825996518960060410388183)
          ·
            refine ⟨5738994778440090615582275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3825996518960060410388183 5738994778440090615582275)
            ·
              refine ⟨8608492167660135923373413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5738994778440090615582275 8608492167660135923373413)
              ·
                refine ⟨1614092281436275485632515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8608492167660135923373413 1614092281436275485632515)
                ·
                  refine ⟨2421138422154413228448773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614092281436275485632515 2421138422154413228448773)
                  ·
                    refine ⟨453963454153952480334145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2421138422154413228448773 453963454153952480334145)
                    ·
                      rfl

theorem cell22_1326136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_1326136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326136 prefixEnd_1326136 := by exact prefixLift 1326136
  have htrace : WordTrace (prefixWord ++ tailWord_1326136) baseStart_1326136 baseEnd_1326136 := by
    simpa [prefixWord, tailWord_1326136, baseEnd_1326136] using wordTrace_append hprefix tailTrace_1326136
  have hstable : (prefixWord ++ tailWord_1326136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326136).length < 2 ^ (prefixWord ++ tailWord_1326136).sum := by decide
  have hdescent : baseEnd_1326136 < baseStart_1326136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326149 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_1326149 : Nat := 118140960795 + 1326149 * 2 ^ 59
def prefixEnd_1326149 : Nat := 4983230072969 + 3 ^ 40 * 1326149 * 2
def baseEnd_1326149 : Nat := 453967904319624779759105

theorem tailTrace_1326149 : CollatzResearch.WordTrace tailWord_1326149 prefixEnd_1326149 453967904319624779759105 := by
  unfold tailWord_1326149
  simp only [CollatzResearch.WordTrace]
  refine ⟨48368627672596136062661501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32245751781730757375107667 48368627672596136062661501)
  ·
    refine ⟨18138235377223551023498063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48368627672596136062661501 18138235377223551023498063)
    ·
      refine ⟨27207353065835326535247095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18138235377223551023498063 27207353065835326535247095)
      ·
        refine ⟨40811029598752989802870643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27207353065835326535247095 40811029598752989802870643)
        ·
          refine ⟨61216544398129484704305965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40811029598752989802870643 61216544398129484704305965)
          ·
            refine ⟨22956204149298556764114737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61216544398129484704305965 22956204149298556764114737)
            ·
              refine ⟨17217153111973917573086053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22956204149298556764114737 17217153111973917573086053)
              ·
                refine ⟨3228216208495109544953635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17217153111973917573086053 3228216208495109544953635)
                ·
                  refine ⟨4842324312742664317430453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228216208495109544953635 4842324312742664317430453)
                  ·
                    refine ⟨453967904319624779759105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4842324312742664317430453 453967904319624779759105)
                    ·
                      rfl

theorem cell22_1326149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_1326149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326149 prefixEnd_1326149 := by exact prefixLift 1326149
  have htrace : WordTrace (prefixWord ++ tailWord_1326149) baseStart_1326149 baseEnd_1326149 := by
    simpa [prefixWord, tailWord_1326149, baseEnd_1326149] using wordTrace_append hprefix tailTrace_1326149
  have hstable : (prefixWord ++ tailWord_1326149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326149).length < 2 ^ (prefixWord ++ tailWord_1326149).sum := by decide
  have hdescent : baseEnd_1326149 < baseStart_1326149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326168 : List Nat := [2, 1, 2, 2, 1, 3, 5, 2, 4]
def baseStart_1326168 : Nat := 118140960795 + 1326168 * 2 ^ 59
def prefixEnd_1326168 : Nat := 4983230072969 + 3 ^ 40 * 1326168 * 2
def baseEnd_1326168 : Nat := 151324802802638354511349

theorem tailTrace_1326168 : CollatzResearch.WordTrace tailWord_1326168 prefixEnd_1326168 151324802802638354511349 := by
  unfold tailWord_1326168
  simp only [CollatzResearch.WordTrace]
  refine ⟨24184660329763651153801579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32246213773018201538402105 24184660329763651153801579)
  ·
    refine ⟨36276990494645476730702369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24184660329763651153801579 36276990494645476730702369)
    ·
      refine ⟨27207742870984107548026777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36276990494645476730702369 27207742870984107548026777)
      ·
        refine ⟨20405807153238080661020083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27207742870984107548026777 20405807153238080661020083)
        ·
          refine ⟨30608710729857120991530125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20405807153238080661020083 30608710729857120991530125)
          ·
            refine ⟨11478266523696420371823797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30608710729857120991530125 11478266523696420371823797)
            ·
              refine ⟨1076087486596539409858481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11478266523696420371823797 1076087486596539409858481)
              ·
                refine ⟨807065614947404557393861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1076087486596539409858481 807065614947404557393861)
                ·
                  refine ⟨151324802802638354511349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 807065614947404557393861 151324802802638354511349)
                  ·
                    rfl

theorem cell22_1326168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 4].length) (baseStart_1326168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326168 prefixEnd_1326168 := by exact prefixLift 1326168
  have htrace : WordTrace (prefixWord ++ tailWord_1326168) baseStart_1326168 baseEnd_1326168 := by
    simpa [prefixWord, tailWord_1326168, baseEnd_1326168] using wordTrace_append hprefix tailTrace_1326168
  have hstable : (prefixWord ++ tailWord_1326168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326168).length < 2 ^ (prefixWord ++ tailWord_1326168).sum := by decide
  have hdescent : baseEnd_1326168 < baseStart_1326168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326183 : List Nat := [1, 1, 5, 1, 1, 4, 1, 3, 2, 3]
def baseStart_1326183 : Nat := 118140960795 + 1326183 * 2 ^ 59
def prefixEnd_1326183 : Nat := 4983230072969 + 3 ^ 40 * 1326183 * 2
def baseEnd_1326183 : Nat := 453979543214460024409001

theorem tailTrace_1326183 : CollatzResearch.WordTrace tailWord_1326183 prefixEnd_1326183 453979543214460024409001 := by
  unfold tailWord_1326183
  simp only [CollatzResearch.WordTrace]
  refine ⟨48369867754472959869399203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32246578502981973246266135 48369867754472959869399203)
  ·
    refine ⟨72554801631709439804098805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48369867754472959869399203 72554801631709439804098805)
    ·
      refine ⟨6802012652972759981634263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72554801631709439804098805 6802012652972759981634263)
      ·
        refine ⟨10203018979459139972451395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6802012652972759981634263 10203018979459139972451395)
        ·
          refine ⟨15304528469188709958677093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10203018979459139972451395 15304528469188709958677093)
          ·
            refine ⟨2869599087972883117251955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15304528469188709958677093 2869599087972883117251955)
            ·
              refine ⟨4304398631959324675877933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869599087972883117251955 4304398631959324675877933)
              ·
                refine ⟨1614149486984746753454225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4304398631959324675877933 1614149486984746753454225)
                ·
                  refine ⟨1210612115238560065090669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1614149486984746753454225 1210612115238560065090669)
                  ·
                    refine ⟨453979543214460024409001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210612115238560065090669 453979543214460024409001)
                    ·
                      rfl

theorem cell22_1326183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_1326183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326183 prefixEnd_1326183 := by exact prefixLift 1326183
  have htrace : WordTrace (prefixWord ++ tailWord_1326183) baseStart_1326183 baseEnd_1326183 := by
    simpa [prefixWord, tailWord_1326183, baseEnd_1326183] using wordTrace_append hprefix tailTrace_1326183
  have hstable : (prefixWord ++ tailWord_1326183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326183).length < 2 ^ (prefixWord ++ tailWord_1326183).sum := by decide
  have hdescent : baseEnd_1326183 < baseStart_1326183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326198 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_1326198 : Nat := 118140960795 + 1326198 * 2 ^ 59
def prefixEnd_1326198 : Nat := 4983230072969 + 3 ^ 40 * 1326198 * 2
def baseEnd_1326198 : Nat := 453984678021004985283955

theorem tailTrace_1326198 : CollatzResearch.WordTrace tailWord_1326198 prefixEnd_1326198 453984678021004985283955 := by
  unfold tailWord_1326198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3023150928088663589449703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32246943232945744954130165 3023150928088663589449703)
  ·
    refine ⟨4534726392132995384174555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3023150928088663589449703 4534726392132995384174555)
    ·
      refine ⟨6802089588199493076261833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4534726392132995384174555 6802089588199493076261833)
      ·
        refine ⟨5101567191149619807196375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6802089588199493076261833 5101567191149619807196375)
        ·
          refine ⟨7652350786724429710794563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5101567191149619807196375 7652350786724429710794563)
          ·
            refine ⟨11478526180086644566191845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7652350786724429710794563 11478526180086644566191845)
            ·
              refine ⟨2152223658766245856160971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11478526180086644566191845 2152223658766245856160971)
              ·
                refine ⟨3228335488149368784241457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2152223658766245856160971 3228335488149368784241457)
                ·
                  refine ⟨2421251616112026588181093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3228335488149368784241457 2421251616112026588181093)
                  ·
                    refine ⟨453984678021004985283955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2421251616112026588181093 453984678021004985283955)
                    ·
                      rfl

theorem cell22_1326198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_1326198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326198 prefixEnd_1326198 := by exact prefixLift 1326198
  have htrace : WordTrace (prefixWord ++ tailWord_1326198) baseStart_1326198 baseEnd_1326198 := by
    simpa [prefixWord, tailWord_1326198, baseEnd_1326198] using wordTrace_append hprefix tailTrace_1326198
  have hstable : (prefixWord ++ tailWord_1326198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326198).length < 2 ^ (prefixWord ++ tailWord_1326198).sum := by decide
  have hdescent : baseEnd_1326198 < baseStart_1326198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326226 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1326226 : Nat := 118140960795 + 1326226 * 2 ^ 59
def prefixEnd_1326226 : Nat := 4983230072969 + 3 ^ 40 * 1326226 * 2
def baseEnd_1326226 : Nat := 453994262993222245583869

theorem tailTrace_1326226 : CollatzResearch.WordTrace tailWord_1326226 prefixEnd_1326226 453994262993222245583869 := by
  unfold tailWord_1326226
  simp only [CollatzResearch.WordTrace]
  refine ⟨12092859023329294553303633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32247624062211452142143021 12092859023329294553303633)
  ·
    refine ⟨9069644267496970914977725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12092859023329294553303633 9069644267496970914977725)
    ·
      refine ⟨3401116600311364093116647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9069644267496970914977725 3401116600311364093116647)
      ·
        refine ⟨5101674900467046139674971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401116600311364093116647 5101674900467046139674971)
        ·
          refine ⟨7652512350700569209512457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5101674900467046139674971 7652512350700569209512457)
          ·
            refine ⟨5739384263025426907134343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7652512350700569209512457 5739384263025426907134343)
            ·
              refine ⟨8609076394538140360701515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5739384263025426907134343 8609076394538140360701515)
              ·
                refine ⟨12913614591807210541052273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8609076394538140360701515 12913614591807210541052273)
                ·
                  refine ⟨9685210943855407905789205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12913614591807210541052273 9685210943855407905789205)
                  ·
                    refine ⟨453994262993222245583869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9685210943855407905789205 453994262993222245583869)
                    ·
                      rfl

theorem cell22_1326226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1326226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326226 prefixEnd_1326226 := by exact prefixLift 1326226
  have htrace : WordTrace (prefixWord ++ tailWord_1326226) baseStart_1326226 baseEnd_1326226 := by
    simpa [prefixWord, tailWord_1326226, baseEnd_1326226] using wordTrace_append hprefix tailTrace_1326226
  have hstable : (prefixWord ++ tailWord_1326226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326226).length < 2 ^ (prefixWord ++ tailWord_1326226).sum := by decide
  have hdescent : baseEnd_1326226 < baseStart_1326226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326241 : List Nat := [1, 2, 3, 3, 1, 1, 1, 5, 5]
def baseStart_1326241 : Nat := 118140960795 + 1326241 * 2 ^ 59
def prefixEnd_1326241 : Nat := 4983230072969 + 3 ^ 40 * 1326241 * 2
def baseEnd_1326241 : Nat := 151333132599922402152941

theorem tailTrace_1326241 : CollatzResearch.WordTrace tailWord_1326241 prefixEnd_1326241 151333132599922402152941 := by
  unfold tailWord_1326241
  simp only [CollatzResearch.WordTrace]
  refine ⟨48371983188262835775010577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32247988792175223850007051 48371983188262835775010577)
  ·
    refine ⟨36278987391197126831257933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48371983188262835775010577 36278987391197126831257933)
    ·
      refine ⟨13604620271698922561721725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36278987391197126831257933 13604620271698922561721725)
      ·
        refine ⟨5101732601887095960645647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13604620271698922561721725 5101732601887095960645647)
        ·
          refine ⟨7652598902830643940968471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5101732601887095960645647 7652598902830643940968471)
          ·
            refine ⟨11478898354245965911452707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7652598902830643940968471 11478898354245965911452707)
            ·
              refine ⟨17218347531368948867179061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11478898354245965911452707 17218347531368948867179061)
              ·
                refine ⟨1614220081065838956298037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17218347531368948867179061 1614220081065838956298037)
                ·
                  refine ⟨151333132599922402152941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1614220081065838956298037 151333132599922402152941)
                  ·
                    rfl

theorem cell22_1326241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 5].length) (baseStart_1326241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326241 prefixEnd_1326241 := by exact prefixLift 1326241
  have htrace : WordTrace (prefixWord ++ tailWord_1326241) baseStart_1326241 baseEnd_1326241 := by
    simpa [prefixWord, tailWord_1326241, baseEnd_1326241] using wordTrace_append hprefix tailTrace_1326241
  have hstable : (prefixWord ++ tailWord_1326241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326241).length < 2 ^ (prefixWord ++ tailWord_1326241).sum := by decide
  have hdescent : baseEnd_1326241 < baseStart_1326241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326273 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1326273 : Nat := 118140960795 + 1326273 * 2 ^ 59
def prefixEnd_1326273 : Nat := 4983230072969 + 3 ^ 40 * 1326273 * 2
def baseEnd_1326273 : Nat := 454010352053729789658725

theorem tailTrace_1326273 : CollatzResearch.WordTrace tailWord_1326273 prefixEnd_1326273 454010352053729789658725 := by
  unfold tailWord_1326273
  simp only [CollatzResearch.WordTrace]
  refine ⟨48373150324146905240175473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32248766882764603493450315 48373150324146905240175473)
  ·
    refine ⟨36279862743110178930131605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48373150324146905240175473 36279862743110178930131605)
    ·
      refine ⟨1700618566083289637349919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36279862743110178930131605 1700618566083289637349919)
      ·
        refine ⟨2550927849124934456024879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1700618566083289637349919 2550927849124934456024879)
        ·
          refine ⟨3826391773687401684037319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550927849124934456024879 3826391773687401684037319)
          ·
            refine ⟨5739587660531102526055979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826391773687401684037319 5739587660531102526055979)
            ·
              refine ⟨8609381490796653789083969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5739587660531102526055979 8609381490796653789083969)
              ·
                refine ⟨6457036118097490341812977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8609381490796653789083969 6457036118097490341812977)
                ·
                  refine ⟨4842777088573117756359733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6457036118097490341812977 4842777088573117756359733)
                  ·
                    refine ⟨454010352053729789658725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4842777088573117756359733 454010352053729789658725)
                    ·
                      rfl

theorem cell22_1326273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1326273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326273 prefixEnd_1326273 := by exact prefixLift 1326273
  have htrace : WordTrace (prefixWord ++ tailWord_1326273) baseStart_1326273 baseEnd_1326273 := by
    simpa [prefixWord, tailWord_1326273, baseEnd_1326273] using wordTrace_append hprefix tailTrace_1326273
  have hstable : (prefixWord ++ tailWord_1326273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326273).length < 2 ^ (prefixWord ++ tailWord_1326273).sum := by decide
  have hdescent : baseEnd_1326273 < baseStart_1326273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326292 : List Nat := [2, 4, 1, 4, 1, 1, 3, 1, 5]
def baseStart_1326292 : Nat := 118140960795 + 1326292 * 2 ^ 59
def prefixEnd_1326292 : Nat := 4983230072969 + 3 ^ 40 * 1326292 * 2
def baseEnd_1326292 : Nat := 151338952047340024477889

theorem tailTrace_1326292 : CollatzResearch.WordTrace tailWord_1326292 prefixEnd_1326292 151338952047340024477889 := by
  unfold tailWord_1326292
  simp only [CollatzResearch.WordTrace]
  refine ⟨24186921655539035742558565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32249228874052047656744753 24186921655539035742558565)
  ·
    refine ⟨4535047810413569201729731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24186921655539035742558565 4535047810413569201729731)
    ·
      refine ⟨6802571715620353802594597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4535047810413569201729731 6802571715620353802594597)
      ·
        refine ⟨1275482196678816337986487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6802571715620353802594597 1275482196678816337986487)
        ·
          refine ⟨1913223295018224506979731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275482196678816337986487 1913223295018224506979731)
          ·
            refine ⟨2869834942527336760469597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913223295018224506979731 2869834942527336760469597)
            ·
              refine ⟨1076188103447751285176099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2869834942527336760469597 1076188103447751285176099)
              ·
                refine ⟨1614282155171626927764149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076188103447751285176099 1614282155171626927764149)
                ·
                  refine ⟨151338952047340024477889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1614282155171626927764149 151338952047340024477889)
                  ·
                    rfl

theorem cell22_1326292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_1326292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326292 prefixEnd_1326292 := by exact prefixLift 1326292
  have htrace : WordTrace (prefixWord ++ tailWord_1326292) baseStart_1326292 baseEnd_1326292 := by
    simpa [prefixWord, tailWord_1326292, baseEnd_1326292] using wordTrace_append hprefix tailTrace_1326292
  have hstable : (prefixWord ++ tailWord_1326292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326292).length < 2 ^ (prefixWord ++ tailWord_1326292).sum := by decide
  have hdescent : baseEnd_1326292 < baseStart_1326292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326316 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_1326316 : Nat := 118140960795 + 1326316 * 2 ^ 59
def prefixEnd_1326316 : Nat := 4983230072969 + 3 ^ 40 * 1326316 * 2
def baseEnd_1326316 : Nat := 454025071832492010833593

theorem tailTrace_1326316 : CollatzResearch.WordTrace tailWord_1326316 prefixEnd_1326316 454025071832492010833593 := by
  unfold tailWord_1326316
  simp only [CollatzResearch.WordTrace]
  refine ⟨24187359331495561791995401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32249812441994082389327201 24187359331495561791995401)
  ·
    refine ⟨18140519498621671343996551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24187359331495561791995401 18140519498621671343996551)
    ·
      refine ⟨27210779247932507015994827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18140519498621671343996551 27210779247932507015994827)
      ·
        refine ⟨40816168871898760523992241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27210779247932507015994827 40816168871898760523992241)
        ·
          refine ⟨30612126653924070392994181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40816168871898760523992241 30612126653924070392994181)
          ·
            refine ⟨5739773747610763198686409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30612126653924070392994181 5739773747610763198686409)
            ·
              refine ⟨4304830310708072399014807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5739773747610763198686409 4304830310708072399014807)
              ·
                refine ⟨6457245466062108598522211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4304830310708072399014807 6457245466062108598522211)
                ·
                  refine ⟨9685868199093162897783317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6457245466062108598522211 9685868199093162897783317)
                  ·
                    refine ⟨454025071832492010833593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9685868199093162897783317 454025071832492010833593)
                    ·
                      rfl

theorem cell22_1326316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_1326316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326316 prefixEnd_1326316 := by exact prefixLift 1326316
  have htrace : WordTrace (prefixWord ++ tailWord_1326316) baseStart_1326316 baseEnd_1326316 := by
    simpa [prefixWord, tailWord_1326316, baseEnd_1326316] using wordTrace_append hprefix tailTrace_1326316
  have hstable : (prefixWord ++ tailWord_1326316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326316).length < 2 ^ (prefixWord ++ tailWord_1326316).sum := by decide
  have hdescent : baseEnd_1326316 < baseStart_1326316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326318 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_1326318 : Nat := 118140960795 + 1326318 * 2 ^ 59
def prefixEnd_1326318 : Nat := 4983230072969 + 3 ^ 40 * 1326318 * 2
def baseEnd_1326318 : Nat := 454025756473364672283587

theorem tailTrace_1326318 : CollatzResearch.WordTrace tailWord_1326318 prefixEnd_1326318 454025756473364672283587 := by
  unfold tailWord_1326318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6046848951122984740695451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32249861072655918617042405 6046848951122984740695451)
  ·
    refine ⟨9070273426684477111043177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6046848951122984740695451 9070273426684477111043177)
    ·
      refine ⟨6802705070013357833282383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9070273426684477111043177 6802705070013357833282383)
      ·
        refine ⟨10204057605020036749923575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6802705070013357833282383 10204057605020036749923575)
        ·
          refine ⟨15306086407530055124885363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10204057605020036749923575 15306086407530055124885363)
          ·
            refine ⟨22959129611295082687328045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15306086407530055124885363 22959129611295082687328045)
            ·
              refine ⟨8609673604235656007748017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22959129611295082687328045 8609673604235656007748017)
              ·
                refine ⟨6457255203176742005811013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8609673604235656007748017 6457255203176742005811013)
                ·
                  refine ⟨1210735350595639126089565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6457255203176742005811013 1210735350595639126089565)
                  ·
                    refine ⟨454025756473364672283587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210735350595639126089565 454025756473364672283587)
                    ·
                      rfl

theorem cell22_1326318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_1326318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326318 prefixEnd_1326318 := by exact prefixLift 1326318
  have htrace : WordTrace (prefixWord ++ tailWord_1326318) baseStart_1326318 baseEnd_1326318 := by
    simpa [prefixWord, tailWord_1326318, baseEnd_1326318] using wordTrace_append hprefix tailTrace_1326318
  have hstable : (prefixWord ++ tailWord_1326318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326318).length < 2 ^ (prefixWord ++ tailWord_1326318).sum := by decide
  have hdescent : baseEnd_1326318 < baseStart_1326318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326380 : List Nat := [2, 2, 1, 1, 1, 3, 1, 7, 1, 3]
def baseStart_1326380 : Nat := 118140960795 + 1326380 * 2 ^ 59
def prefixEnd_1326380 : Nat := 4983230072969 + 3 ^ 40 * 1326380 * 2
def baseEnd_1326380 : Nat := 454046980340417177233397

theorem tailTrace_1326380 : CollatzResearch.WordTrace tailWord_1326380 prefixEnd_1326380 454046980340417177233397 := by
  unfold tailWord_1326380
  simp only [CollatzResearch.WordTrace]
  refine ⟨24188526467379631257160297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32251368623172841676213729 24188526467379631257160297)
  ·
    refine ⟨18141394850534723442870223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24188526467379631257160297 18141394850534723442870223)
    ·
      refine ⟨27212092275802085164305335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18141394850534723442870223 27212092275802085164305335)
      ·
        refine ⟨40818138413703127746458003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27212092275802085164305335 40818138413703127746458003)
        ·
          refine ⟨61227207620554691619687005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40818138413703127746458003 61227207620554691619687005)
          ·
            refine ⟨22960202857708009357382627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61227207620554691619687005 22960202857708009357382627)
            ·
              refine ⟨34440304286562014036073941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22960202857708009357382627 34440304286562014036073941)
              ·
                refine ⟨807194631716297203970483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 34440304286562014036073941 807194631716297203970483)
                ·
                  refine ⟨1210791947574445805955725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807194631716297203970483 1210791947574445805955725)
                  ·
                    refine ⟨454046980340417177233397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210791947574445805955725 454046980340417177233397)
                    ·
                      rfl

theorem cell22_1326380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_1326380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326380 prefixEnd_1326380 := by exact prefixLift 1326380
  have htrace : WordTrace (prefixWord ++ tailWord_1326380) baseStart_1326380 baseEnd_1326380 := by
    simpa [prefixWord, tailWord_1326380, baseEnd_1326380] using wordTrace_append hprefix tailTrace_1326380
  have hstable : (prefixWord ++ tailWord_1326380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326380).length < 2 ^ (prefixWord ++ tailWord_1326380).sum := by decide
  have hdescent : baseEnd_1326380 < baseStart_1326380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326423 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 3, 4]
def baseStart_1326423 : Nat := 118140960795 + 1326423 * 2 ^ 59
def prefixEnd_1326423 : Nat := 4983230072969 + 3 ^ 40 * 1326423 * 2
def baseEnd_1326423 : Nat := 454061700119179398408265

theorem tailTrace_1326423 : CollatzResearch.WordTrace tailWord_1326423 prefixEnd_1326423 454061700119179398408265 := by
  unfold tailWord_1326423
  simp only [CollatzResearch.WordTrace]
  refine ⟨48378621273603480858135923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32252414182402320572090615 48378621273603480858135923)
  ·
    refine ⟨72567931910405221287203885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48378621273603480858135923 72567931910405221287203885)
    ·
      refine ⟨27212974466401957982701457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72567931910405221287203885 27212974466401957982701457)
      ·
        refine ⟨20409730849801468487026093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27212974466401957982701457 20409730849801468487026093)
        ·
          refine ⟨7653649068675550682634785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20409730849801468487026093 7653649068675550682634785)
          ·
            refine ⟨5740236801506663011976089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7653649068675550682634785 5740236801506663011976089)
            ·
              refine ⟨4305177601129997258982067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5740236801506663011976089 4305177601129997258982067)
              ·
                refine ⟨6457766401694995888473101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305177601129997258982067 6457766401694995888473101)
                ·
                  refine ⟨2421662400635623458177413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6457766401694995888473101 2421662400635623458177413)
                  ·
                    refine ⟨454061700119179398408265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2421662400635623458177413 454061700119179398408265)
                    ·
                      rfl

theorem cell22_1326423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_1326423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326423 prefixEnd_1326423 := by exact prefixLift 1326423
  have htrace : WordTrace (prefixWord ++ tailWord_1326423) baseStart_1326423 baseEnd_1326423 := by
    simpa [prefixWord, tailWord_1326423, baseEnd_1326423] using wordTrace_append hprefix tailTrace_1326423
  have hstable : (prefixWord ++ tailWord_1326423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326423).length < 2 ^ (prefixWord ++ tailWord_1326423).sum := by decide
  have hdescent : baseEnd_1326423 < baseStart_1326423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326451 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 5, 6]
def baseStart_1326451 : Nat := 118140960795 + 1326451 * 2 ^ 59
def prefixEnd_1326451 : Nat := 4983230072969 + 3 ^ 40 * 1326451 * 2
def baseEnd_1326451 : Nat := 454071285091396658708179

theorem tailTrace_1326451 : CollatzResearch.WordTrace tailWord_1326451 prefixEnd_1326451 454071285091396658708179 := by
  unfold tailWord_1326451
  simp only [CollatzResearch.WordTrace]
  refine ⟨48379642517502041640155207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32253095011668027760103471 48379642517502041640155207)
  ·
    refine ⟨72569463776253062460232811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48379642517502041640155207 72569463776253062460232811)
    ·
      refine ⟨108854195664379593690349217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72569463776253062460232811 108854195664379593690349217)
      ·
        refine ⟨81640646748284695267761913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108854195664379593690349217 81640646748284695267761913)
        ·
          refine ⟨61230485061213521450821435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81640646748284695267761913 61230485061213521450821435)
          ·
            refine ⟨91845727591820282176232153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61230485061213521450821435 91845727591820282176232153)
            ·
              refine ⟨68884295693865211632174115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91845727591820282176232153 68884295693865211632174115)
              ·
                refine ⟨103326443540797817448261173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68884295693865211632174115 103326443540797817448261173)
                ·
                  refine ⟨9686854081949795385774485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103326443540797817448261173 9686854081949795385774485)
                  ·
                    refine ⟨454071285091396658708179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9686854081949795385774485 454071285091396658708179)
                    ·
                      rfl

theorem cell22_1326451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_1326451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326451 prefixEnd_1326451 := by exact prefixLift 1326451
  have htrace : WordTrace (prefixWord ++ tailWord_1326451) baseStart_1326451 baseEnd_1326451 := by
    simpa [prefixWord, tailWord_1326451, baseEnd_1326451] using wordTrace_append hprefix tailTrace_1326451
  have hstable : (prefixWord ++ tailWord_1326451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326451).length < 2 ^ (prefixWord ++ tailWord_1326451).sum := by decide
  have hdescent : baseEnd_1326451 < baseStart_1326451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326468 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_1326468 : Nat := 118140960795 + 1326468 * 2 ^ 59
def prefixEnd_1326468 : Nat := 4983230072969 + 3 ^ 40 * 1326468 * 2
def baseEnd_1326468 : Nat := 454077104538814281033127

theorem tailTrace_1326468 : CollatzResearch.WordTrace tailWord_1326468 prefixEnd_1326468 454077104538814281033127 := by
  unfold tailWord_1326468
  simp only [CollatzResearch.WordTrace]
  refine ⟨24190131279220226771762029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32253508372293635695682705 24190131279220226771762029)
  ·
    refine ⟨9071299229707585039410761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24190131279220226771762029 9071299229707585039410761)
    ·
      refine ⟨6803474422280688779558071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9071299229707585039410761 6803474422280688779558071)
      ·
        refine ⟨10205211633421033169337107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6803474422280688779558071 10205211633421033169337107)
        ·
          refine ⟨15307817450131549754005661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10205211633421033169337107 15307817450131549754005661)
          ·
            refine ⟨5740431543799331157752123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15307817450131549754005661 5740431543799331157752123)
            ·
              refine ⟨8610647315698996736628185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5740431543799331157752123 8610647315698996736628185)
              ·
                refine ⟨6457985486774247552471139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8610647315698996736628185 6457985486774247552471139)
                ·
                  refine ⟨9686978230161371328706709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6457985486774247552471139 9686978230161371328706709)
                  ·
                    refine ⟨454077104538814281033127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9686978230161371328706709 454077104538814281033127)
                    ·
                      rfl

theorem cell22_1326468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_1326468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326468 prefixEnd_1326468 := by exact prefixLift 1326468
  have htrace : WordTrace (prefixWord ++ tailWord_1326468) baseStart_1326468 baseEnd_1326468 := by
    simpa [prefixWord, tailWord_1326468, baseEnd_1326468] using wordTrace_append hprefix tailTrace_1326468
  have hstable : (prefixWord ++ tailWord_1326468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326468).length < 2 ^ (prefixWord ++ tailWord_1326468).sum := by decide
  have hdescent : baseEnd_1326468 < baseStart_1326468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326513 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 2, 6]
def baseStart_1326513 : Nat := 118140960795 + 1326513 * 2 ^ 59
def prefixEnd_1326513 : Nat := 4983230072969 + 3 ^ 40 * 1326513 * 2
def baseEnd_1326513 : Nat := 454092508958449163657989

theorem tailTrace_1326513 : CollatzResearch.WordTrace tailWord_1326513 prefixEnd_1326513 454092508958449163657989 := by
  unfold tailWord_1326513
  simp only [CollatzResearch.WordTrace]
  refine ⟨48381903843277426228912193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32254602562184950819274795 48381903843277426228912193)
  ·
    refine ⟨36286427882458069671684145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48381903843277426228912193 36286427882458069671684145)
    ·
      refine ⟨27214820911843552253763109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36286427882458069671684145 27214820911843552253763109)
      ·
        refine ⟨5102778920970666047580583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27214820911843552253763109 5102778920970666047580583)
        ·
          refine ⟨7654168381455999071370875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5102778920970666047580583 7654168381455999071370875)
          ·
            refine ⟨11481252572183998607056313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7654168381455999071370875 11481252572183998607056313)
            ·
              refine ⟨8610939429137998955292235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11481252572183998607056313 8610939429137998955292235)
              ·
                refine ⟨12916409143706998432938353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8610939429137998955292235 12916409143706998432938353)
                ·
                  refine ⟨9687306857780248824703765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12916409143706998432938353 9687306857780248824703765)
                  ·
                    refine ⟨454092508958449163657989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9687306857780248824703765 454092508958449163657989)
                    ·
                      rfl

theorem cell22_1326513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_1326513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326513 prefixEnd_1326513 := by exact prefixLift 1326513
  have htrace : WordTrace (prefixWord ++ tailWord_1326513) baseStart_1326513 baseEnd_1326513 := by
    simpa [prefixWord, tailWord_1326513, baseEnd_1326513] using wordTrace_append hprefix tailTrace_1326513
  have hstable : (prefixWord ++ tailWord_1326513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326513).length < 2 ^ (prefixWord ++ tailWord_1326513).sum := by decide
  have hdescent : baseEnd_1326513 < baseStart_1326513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326521 : List Nat := [1, 2, 1, 4, 5, 1, 2, 1, 2, 3]
def baseStart_1326521 : Nat := 118140960795 + 1326521 * 2 ^ 59
def prefixEnd_1326521 : Nat := 4983230072969 + 3 ^ 40 * 1326521 * 2
def baseEnd_1326521 : Nat := 454095247521939809457965

theorem tailTrace_1326521 : CollatzResearch.WordTrace tailWord_1326521 prefixEnd_1326521 454095247521939809457965 := by
  unfold tailWord_1326521
  simp only [CollatzResearch.WordTrace]
  refine ⟨48382195627248443595203417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32254797084832295730135611 48382195627248443595203417)
  ·
    refine ⟨36286646720436332696402563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48382195627248443595203417 36286646720436332696402563)
    ·
      refine ⟨54429970080654499044603845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36286646720436332696402563 54429970080654499044603845)
      ·
        refine ⟨10205619390122718570863221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54429970080654499044603845 10205619390122718570863221)
        ·
          refine ⟨956776817824004866018427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10205619390122718570863221 956776817824004866018427)
          ·
            refine ⟨1435165226736007299027641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956776817824004866018427 1435165226736007299027641)
            ·
              refine ⟨1076373920052005474270731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435165226736007299027641 1076373920052005474270731)
              ·
                refine ⟨1614560880078008211406097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076373920052005474270731 1614560880078008211406097)
                ·
                  refine ⟨1210920660058506158554573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1614560880078008211406097 1210920660058506158554573)
                  ·
                    refine ⟨454095247521939809457965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210920660058506158554573 454095247521939809457965)
                    ·
                      rfl

theorem cell22_1326521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 2, 3].length) (baseStart_1326521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326521 prefixEnd_1326521 := by exact prefixLift 1326521
  have htrace : WordTrace (prefixWord ++ tailWord_1326521) baseStart_1326521 baseEnd_1326521 := by
    simpa [prefixWord, tailWord_1326521, baseEnd_1326521] using wordTrace_append hprefix tailTrace_1326521
  have hstable : (prefixWord ++ tailWord_1326521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326521).length < 2 ^ (prefixWord ++ tailWord_1326521).sum := by decide
  have hdescent : baseEnd_1326521 < baseStart_1326521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326620 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1326620 : Nat := 118140960795 + 1326620 * 2 ^ 59
def prefixEnd_1326620 : Nat := 4983230072969 + 3 ^ 40 * 1326620 * 2
def baseEnd_1326620 : Nat := 454129137245136551232661

theorem tailTrace_1326620 : CollatzResearch.WordTrace tailWord_1326620 prefixEnd_1326620 454129137245136551232661 := by
  unfold tailWord_1326620
  simp only [CollatzResearch.WordTrace]
  refine ⟨24192903226944891751528657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32257204302593189002038209 24192903226944891751528657)
  ·
    refine ⟨18144677420208668813646493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24192903226944891751528657 18144677420208668813646493)
    ·
      refine ⟨6804254032578250805117435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18144677420208668813646493 6804254032578250805117435)
      ·
        refine ⟨10206381048867376207676153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6804254032578250805117435 10206381048867376207676153)
        ·
          refine ⟨7654785786650532155757115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10206381048867376207676153 7654785786650532155757115)
          ·
            refine ⟨11482178679975798233635673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7654785786650532155757115 11482178679975798233635673)
            ·
              refine ⟨8611634009981848675226755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11482178679975798233635673 8611634009981848675226755)
              ·
                refine ⟨12917451014972773012840133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8611634009981848675226755 12917451014972773012840133)
                ·
                  refine ⟨2422022065307394939907525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12917451014972773012840133 2422022065307394939907525)
                  ·
                    refine ⟨454129137245136551232661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2422022065307394939907525 454129137245136551232661)
                    ·
                      rfl

theorem cell22_1326620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1326620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326620 prefixEnd_1326620 := by exact prefixLift 1326620
  have htrace : WordTrace (prefixWord ++ tailWord_1326620) baseStart_1326620 baseEnd_1326620 := by
    simpa [prefixWord, tailWord_1326620, baseEnd_1326620] using wordTrace_append hprefix tailTrace_1326620
  have hstable : (prefixWord ++ tailWord_1326620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326620).length < 2 ^ (prefixWord ++ tailWord_1326620).sum := by decide
  have hdescent : baseEnd_1326620 < baseStart_1326620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326669 : List Nat := [1, 6, 1, 1, 4, 1, 8]
def baseStart_1326669 : Nat := 118140960795 + 1326669 * 2 ^ 59
def prefixEnd_1326669 : Nat := 4983230072969 + 3 ^ 40 * 1326669 * 2
def baseEnd_1326669 : Nat := 16820218923945065065093

theorem tailTrace_1326669 : CollatzResearch.WordTrace tailWord_1326669 prefixEnd_1326669 16820218923945065065093 := by
  unfold tailWord_1326669
  simp only [CollatzResearch.WordTrace]
  refine ⟨48387593630712264871591061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32258395753808176581060707 48387593630712264871591061)
  ·
    refine ⟨2268168451439637415855831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48387593630712264871591061 2268168451439637415855831)
    ·
      refine ⟨3402252677159456123783747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2268168451439637415855831 3402252677159456123783747)
      ·
        refine ⟨5103379015739184185675621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402252677159456123783747 5103379015739184185675621)
        ·
          refine ⟨956883565451097034814179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5103379015739184185675621 956883565451097034814179)
          ·
            refine ⟨1435325348176645552221269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956883565451097034814179 1435325348176645552221269)
            ·
              refine ⟨16820218923945065065093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1435325348176645552221269 16820218923945065065093)
              ·
                rfl

theorem cell22_1326669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 8].length) (baseStart_1326669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326669 prefixEnd_1326669 := by exact prefixLift 1326669
  have htrace : WordTrace (prefixWord ++ tailWord_1326669) baseStart_1326669 baseEnd_1326669 := by
    simpa [prefixWord, tailWord_1326669, baseEnd_1326669] using wordTrace_append hprefix tailTrace_1326669
  have hstable : (prefixWord ++ tailWord_1326669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326669).length < 2 ^ (prefixWord ++ tailWord_1326669).sum := by decide
  have hdescent : baseEnd_1326669 < baseStart_1326669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326680 : List Nat := [2, 1, 2, 2, 1, 2, 1, 6, 5]
def baseStart_1326680 : Nat := 118140960795 + 1326680 * 2 ^ 59
def prefixEnd_1326680 : Nat := 4983230072969 + 3 ^ 40 * 1326680 * 2
def baseEnd_1326680 : Nat := 151383225490438798244159

theorem tailTrace_1326680 : CollatzResearch.WordTrace tailWord_1326680 prefixEnd_1326680 151383225490438798244159 := by
  unfold tailWord_1326680
  simp only [CollatzResearch.WordTrace]
  refine ⟨24193997416836206875120747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32258663222448275833494329 24193997416836206875120747)
  ·
    refine ⟨36290996125254310312681121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24193997416836206875120747 36290996125254310312681121)
    ·
      refine ⟨27218247093940732734510841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36290996125254310312681121 27218247093940732734510841)
      ·
        refine ⟨20413685320455549550883131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27218247093940732734510841 20413685320455549550883131)
        ·
          refine ⟨30620527980683324326324697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20413685320455549550883131 30620527980683324326324697)
          ·
            refine ⟨22965395985512493244743523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30620527980683324326324697 22965395985512493244743523)
            ·
              refine ⟨34448093978268739867115285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22965395985512493244743523 34448093978268739867115285)
              ·
                refine ⟨1614754405231347181271029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34448093978268739867115285 1614754405231347181271029)
                ·
                  refine ⟨151383225490438798244159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1614754405231347181271029 151383225490438798244159)
                  ·
                    rfl

theorem cell22_1326680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 5].length) (baseStart_1326680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326680 prefixEnd_1326680 := by exact prefixLift 1326680
  have htrace : WordTrace (prefixWord ++ tailWord_1326680) baseStart_1326680 baseEnd_1326680 := by
    simpa [prefixWord, tailWord_1326680, baseEnd_1326680] using wordTrace_append hprefix tailTrace_1326680
  have hstable : (prefixWord ++ tailWord_1326680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326680).length < 2 ^ (prefixWord ++ tailWord_1326680).sum := by decide
  have hdescent : baseEnd_1326680 < baseStart_1326680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326684 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1326684 : Nat := 118140960795 + 1326684 * 2 ^ 59
def prefixEnd_1326684 : Nat := 4983230072969 + 3 ^ 40 * 1326684 * 2
def baseEnd_1326684 : Nat := 454151045753061717632465

theorem tailTrace_1326684 : CollatzResearch.WordTrace tailWord_1326684 prefixEnd_1326684 454151045753061717632465 := by
  unfold tailWord_1326684
  simp only [CollatzResearch.WordTrace]
  refine ⟨24194070362828961216693553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32258760483771948288924737 24194070362828961216693553)
  ·
    refine ⟨18145552772121720912520165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24194070362828961216693553 18145552772121720912520165)
    ·
      refine ⟨3402291144772822671097531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18145552772121720912520165 3402291144772822671097531)
      ·
        refine ⟨5103436717159234006646297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402291144772822671097531 5103436717159234006646297)
        ·
          refine ⟨3827577537869425504984723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5103436717159234006646297 3827577537869425504984723)
          ·
            refine ⟨5741366306804138257477085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3827577537869425504984723 5741366306804138257477085)
            ·
              refine ⟨2153012365051551846553907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5741366306804138257477085 2153012365051551846553907)
              ·
                refine ⟨3229518547577327769830861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2153012365051551846553907 3229518547577327769830861)
                ·
                  refine ⟨1211069455341497913686573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3229518547577327769830861 1211069455341497913686573)
                  ·
                    refine ⟨454151045753061717632465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1211069455341497913686573 454151045753061717632465)
                    ·
                      rfl

theorem cell22_1326684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1326684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326684 prefixEnd_1326684 := by exact prefixLift 1326684
  have htrace : WordTrace (prefixWord ++ tailWord_1326684) baseStart_1326684 baseEnd_1326684 := by
    simpa [prefixWord, tailWord_1326684, baseEnd_1326684] using wordTrace_append hprefix tailTrace_1326684
  have hstable : (prefixWord ++ tailWord_1326684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326684).length < 2 ^ (prefixWord ++ tailWord_1326684).sum := by decide
  have hdescent : baseEnd_1326684 < baseStart_1326684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326695 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1326695 : Nat := 118140960795 + 1326695 * 2 ^ 59
def prefixEnd_1326695 : Nat := 4983230072969 + 3 ^ 40 * 1326695 * 2
def baseEnd_1326695 : Nat := 454154811277861355607431

theorem tailTrace_1326695 : CollatzResearch.WordTrace tailWord_1326695 prefixEnd_1326695 454154811277861355607431 := by
  unfold tailWord_1326695
  simp only [CollatzResearch.WordTrace]
  refine ⟨48388541928618071312037539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32259027952412047541358359 48388541928618071312037539)
  ·
    refine ⟨72582812892927106968056309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48388541928618071312037539 72582812892927106968056309)
    ·
      refine ⟨6804638708711916278255279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72582812892927106968056309 6804638708711916278255279)
      ·
        refine ⟨10206958063067874417382919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6804638708711916278255279 10206958063067874417382919)
        ·
          refine ⟨15310437094601811626074379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10206958063067874417382919 15310437094601811626074379)
          ·
            refine ⟨22965655641902717439111569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15310437094601811626074379 22965655641902717439111569)
            ·
              refine ⟨17224241731427038079333677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22965655641902717439111569 17224241731427038079333677)
              ·
                refine ⟨6459090649285139279750129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17224241731427038079333677 6459090649285139279750129)
                ·
                  refine ⟨4844317986963854459812597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6459090649285139279750129 4844317986963854459812597)
                  ·
                    refine ⟨454154811277861355607431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4844317986963854459812597 454154811277861355607431)
                    ·
                      rfl

theorem cell22_1326695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1326695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326695 prefixEnd_1326695 := by exact prefixLift 1326695
  have htrace : WordTrace (prefixWord ++ tailWord_1326695) baseStart_1326695 baseEnd_1326695 := by
    simpa [prefixWord, tailWord_1326695, baseEnd_1326695] using wordTrace_append hprefix tailTrace_1326695
  have hstable : (prefixWord ++ tailWord_1326695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326695).length < 2 ^ (prefixWord ++ tailWord_1326695).sum := by decide
  have hdescent : baseEnd_1326695 < baseStart_1326695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326697 : List Nat := [1, 2, 1, 1, 1, 4, 6, 1, 5]
def baseStart_1326697 : Nat := 118140960795 + 1326697 * 2 ^ 59
def prefixEnd_1326697 : Nat := 4983230072969 + 3 ^ 40 * 1326697 * 2
def baseEnd_1326697 : Nat := 151385165306244672352475

theorem tailTrace_1326697 : CollatzResearch.WordTrace tailWord_1326697 prefixEnd_1326697 151385165306244672352475 := by
  unfold tailWord_1326697
  simp only [CollatzResearch.WordTrace]
  refine ⟨48388614874610825653610345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32259076583073883769073563 48388614874610825653610345)
  ·
    refine ⟨36291461155958119240207759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48388614874610825653610345 36291461155958119240207759)
    ·
      refine ⟨54437191733937178860311639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36291461155958119240207759 54437191733937178860311639)
      ·
        refine ⟨81655787600905768290467459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54437191733937178860311639 81655787600905768290467459)
        ·
          refine ⟨122483681401358652435701189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81655787600905768290467459 122483681401358652435701189)
          ·
            refine ⟨22965690262754747331693973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122483681401358652435701189 22965690262754747331693973)
            ·
              refine ⟨1076516731066628781173155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22965690262754747331693973 1076516731066628781173155)
              ·
                refine ⟨1614775096599943171759733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076516731066628781173155 1614775096599943171759733)
                ·
                  refine ⟨151385165306244672352475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1614775096599943171759733 151385165306244672352475)
                  ·
                    rfl

theorem cell22_1326697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 5].length) (baseStart_1326697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326697 prefixEnd_1326697 := by exact prefixLift 1326697
  have htrace : WordTrace (prefixWord ++ tailWord_1326697) baseStart_1326697 baseEnd_1326697 := by
    simpa [prefixWord, tailWord_1326697, baseEnd_1326697] using wordTrace_append hprefix tailTrace_1326697
  have hstable : (prefixWord ++ tailWord_1326697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326697).length < 2 ^ (prefixWord ++ tailWord_1326697).sum := by decide
  have hdescent : baseEnd_1326697 < baseStart_1326697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326755 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 1, 6]
def baseStart_1326755 : Nat := 118140960795 + 1326755 * 2 ^ 59
def prefixEnd_1326755 : Nat := 4983230072969 + 3 ^ 40 * 1326755 * 2
def baseEnd_1326755 : Nat := 454175350504041199107247

theorem tailTrace_1326755 : CollatzResearch.WordTrace tailWord_1326755 prefixEnd_1326755 454175350504041199107247 := by
  unfold tailWord_1326755
  simp only [CollatzResearch.WordTrace]
  refine ⟨48390730308400701559221719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32260486872267134372814479 48390730308400701559221719)
  ·
    refine ⟨72586095462601052338832579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48390730308400701559221719 72586095462601052338832579)
    ·
      refine ⟨108879143193901578508248869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72586095462601052338832579 108879143193901578508248869)
      ·
        refine ⟨20414839348856545970296663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108879143193901578508248869 20414839348856545970296663)
        ·
          refine ⟨30622259023284818955444995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20414839348856545970296663 30622259023284818955444995)
          ·
            refine ⟨45933388534927228433167493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30622259023284818955444995 45933388534927228433167493)
            ·
              refine ⟨8612510350298855331218905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45933388534927228433167493 8612510350298855331218905)
              ·
                refine ⟨6459382762724141498414179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8612510350298855331218905 6459382762724141498414179)
                ·
                  refine ⟨9689074144086212247621269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6459382762724141498414179 9689074144086212247621269)
                  ·
                    refine ⟨454175350504041199107247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9689074144086212247621269 454175350504041199107247)
                    ·
                      rfl

theorem cell22_1326755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 6].length) (baseStart_1326755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326755 prefixEnd_1326755 := by exact prefixLift 1326755
  have htrace : WordTrace (prefixWord ++ tailWord_1326755) baseStart_1326755 baseEnd_1326755 := by
    simpa [prefixWord, tailWord_1326755, baseEnd_1326755] using wordTrace_append hprefix tailTrace_1326755
  have hstable : (prefixWord ++ tailWord_1326755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326755).length < 2 ^ (prefixWord ++ tailWord_1326755).sum := by decide
  have hdescent : baseEnd_1326755 < baseStart_1326755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326770 : List Nat := [3, 2, 1, 1, 1, 2, 2, 10]
def baseStart_1326770 : Nat := 118140960795 + 1326770 * 2 ^ 59
def prefixEnd_1326770 : Nat := 4983230072969 + 3 ^ 40 * 1326770 * 2
def baseEnd_1326770 : Nat := 50464498367842906664689

theorem tailTrace_1326770 : CollatzResearch.WordTrace tailWord_1326770 prefixEnd_1326770 50464498367842906664689 := by
  unfold tailWord_1326770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12097819350836589780254441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32260851602230906080678509 12097819350836589780254441)
  ·
    refine ⟨9073364513127442335190831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12097819350836589780254441 9073364513127442335190831)
    ·
      refine ⟨13610046769691163502786247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9073364513127442335190831 13610046769691163502786247)
      ·
        refine ⟨20415070154536745254179371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13610046769691163502786247 20415070154536745254179371)
        ·
          refine ⟨30622605231805117881269057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20415070154536745254179371 30622605231805117881269057)
          ·
            refine ⟨22966953923853838410951793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30622605231805117881269057 22966953923853838410951793)
            ·
              refine ⟨17225215442890378808213845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22966953923853838410951793 17225215442890378808213845)
              ·
                refine ⟨50464498367842906664689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17225215442890378808213845 50464498367842906664689)
                ·
                  rfl

theorem cell22_1326770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_1326770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326770 prefixEnd_1326770 := by exact prefixLift 1326770
  have htrace : WordTrace (prefixWord ++ tailWord_1326770) baseStart_1326770 baseEnd_1326770 := by
    simpa [prefixWord, tailWord_1326770, baseEnd_1326770] using wordTrace_append hprefix tailTrace_1326770
  have hstable : (prefixWord ++ tailWord_1326770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326770).length < 2 ^ (prefixWord ++ tailWord_1326770).sum := by decide
  have hdescent : baseEnd_1326770 < baseStart_1326770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326800 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 2, 6]
def baseStart_1326800 : Nat := 118140960795 + 1326800 * 2 ^ 59
def prefixEnd_1326800 : Nat := 4983230072969 + 3 ^ 40 * 1326800 * 2
def baseEnd_1326800 : Nat := 454190754923676081732109

theorem tailTrace_1326800 : CollatzResearch.WordTrace tailWord_1326800 prefixEnd_1326800 454190754923676081732109 := by
  unfold tailWord_1326800
  simp only [CollatzResearch.WordTrace]
  refine ⟨24196185796618837122304927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32261581062158449496406569 24196185796618837122304927)
  ·
    refine ⟨36294278694928255683457391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24196185796618837122304927 36294278694928255683457391)
    ·
      refine ⟨54441418042392383525186087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36294278694928255683457391 54441418042392383525186087)
      ·
        refine ⟨81662127063588575287779131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54441418042392383525186087 81662127063588575287779131)
        ·
          refine ⟨122493190595382862931668697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81662127063588575287779131 122493190595382862931668697)
          ·
            refine ⟨91869892946537147198751523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122493190595382862931668697 91869892946537147198751523)
            ·
              refine ⟨137804839419805720798127285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91869892946537147198751523 137804839419805720798127285)
              ·
                refine ⟨12919203695606786324824433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137804839419805720798127285 12919203695606786324824433)
                ·
                  refine ⟨9689402771705089743618325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12919203695606786324824433 9689402771705089743618325)
                  ·
                    refine ⟨454190754923676081732109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9689402771705089743618325 454190754923676081732109)
                    ·
                      rfl

theorem cell22_1326800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_1326800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326800 prefixEnd_1326800 := by exact prefixLift 1326800
  have htrace : WordTrace (prefixWord ++ tailWord_1326800) baseStart_1326800 baseEnd_1326800 := by
    simpa [prefixWord, tailWord_1326800, baseEnd_1326800] using wordTrace_append hprefix tailTrace_1326800
  have hstable : (prefixWord ++ tailWord_1326800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326800).length < 2 ^ (prefixWord ++ tailWord_1326800).sum := by decide
  have hdescent : baseEnd_1326800 < baseStart_1326800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326866 : List Nat := [3, 2, 4, 1, 1, 2, 1, 3, 5]
def baseStart_1326866 : Nat := 118140960795 + 1326866 * 2 ^ 59
def prefixEnd_1326866 : Nat := 4983230072969 + 3 ^ 40 * 1326866 * 2
def baseEnd_1326866 : Nat := 151404449357491303193969

theorem tailTrace_1326866 : CollatzResearch.WordTrace tailWord_1326866 prefixEnd_1326866 151404449357491303193969 := by
  unfold tailWord_1326866
  simp only [CollatzResearch.WordTrace]
  refine ⟨12098694702749641879128113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32263185873999045011008301 12098694702749641879128113)
  ·
    refine ⟨9074021027062231409346085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12098694702749641879128113 9074021027062231409346085)
    ·
      refine ⟨1701378942574168389252391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9074021027062231409346085 1701378942574168389252391)
      ·
        refine ⟨2552068413861252583878587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1701378942574168389252391 2552068413861252583878587)
        ·
          refine ⟨3828102620791878875817881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552068413861252583878587 3828102620791878875817881)
          ·
            refine ⟨2871076965593909156863411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3828102620791878875817881 2871076965593909156863411)
            ·
              refine ⟨4306615448390863735295117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871076965593909156863411 4306615448390863735295117)
              ·
                refine ⟨1614980793146573900735669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4306615448390863735295117 1614980793146573900735669)
                ·
                  refine ⟨151404449357491303193969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1614980793146573900735669 151404449357491303193969)
                  ·
                    rfl

theorem cell22_1326866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_1326866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326866 prefixEnd_1326866 := by exact prefixLift 1326866
  have htrace : WordTrace (prefixWord ++ tailWord_1326866) baseStart_1326866 baseEnd_1326866 := by
    simpa [prefixWord, tailWord_1326866, baseEnd_1326866] using wordTrace_append hprefix tailTrace_1326866
  have hstable : (prefixWord ++ tailWord_1326866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326866).length < 2 ^ (prefixWord ++ tailWord_1326866).sum := by decide
  have hdescent : baseEnd_1326866 < baseStart_1326866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326892 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_1326892 : Nat := 118140960795 + 1326892 * 2 ^ 59
def prefixEnd_1326892 : Nat := 4983230072969 + 3 ^ 40 * 1326892 * 2
def baseEnd_1326892 : Nat := 454222248403818508431827

theorem tailTrace_1326892 : CollatzResearch.WordTrace tailWord_1326892 prefixEnd_1326892 454222248403818508431827 := by
  unfold tailWord_1326892
  simp only [CollatzResearch.WordTrace]
  refine ⟨24197863554452186978479465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32263818072602915971305953 24197863554452186978479465)
  ·
    refine ⟨18148397665839140233859599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24197863554452186978479465 18148397665839140233859599)
    ·
      refine ⟨27222596498758710350789399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18148397665839140233859599 27222596498758710350789399)
      ·
        refine ⟨40833894748138065526184099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27222596498758710350789399 40833894748138065526184099)
        ·
          refine ⟨61250842122207098289276149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40833894748138065526184099 61250842122207098289276149)
          ·
            refine ⟨5742266448956915464619639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61250842122207098289276149 5742266448956915464619639)
            ·
              refine ⟨8613399673435373196929459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5742266448956915464619639 8613399673435373196929459)
              ·
                refine ⟨12920099510153059795394189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8613399673435373196929459 12920099510153059795394189)
                ·
                  refine ⟨4845037316307397423272821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12920099510153059795394189 4845037316307397423272821)
                  ·
                    refine ⟨454222248403818508431827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4845037316307397423272821 454222248403818508431827)
                    ·
                      rfl

theorem cell22_1326892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_1326892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326892 prefixEnd_1326892 := by exact prefixLift 1326892
  have htrace : WordTrace (prefixWord ++ tailWord_1326892) baseStart_1326892 baseEnd_1326892 := by
    simpa [prefixWord, tailWord_1326892, baseEnd_1326892] using wordTrace_append hprefix tailTrace_1326892
  have hstable : (prefixWord ++ tailWord_1326892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326892).length < 2 ^ (prefixWord ++ tailWord_1326892).sum := by decide
  have hdescent : baseEnd_1326892 < baseStart_1326892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326911 : List Nat := [1, 1, 2, 2, 6, 1, 1, 4, 4]
def baseStart_1326911 : Nat := 118140960795 + 1326911 * 2 ^ 59
def prefixEnd_1326911 : Nat := 4983230072969 + 3 ^ 40 * 1326911 * 2
def baseEnd_1326911 : Nat := 151409584164036264068923

theorem tailTrace_1326911 : CollatzResearch.WordTrace tailWord_1326911 prefixEnd_1326911 151409584164036264068923 := by
  unfold tailWord_1326911
  simp only [CollatzResearch.WordTrace]
  refine ⟨48396420095835540201900587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32264280063890360134600391 48396420095835540201900587)
  ·
    refine ⟨72594630143753310302850881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48396420095835540201900587 72594630143753310302850881)
    ·
      refine ⟨54445972607814982727138161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72594630143753310302850881 54445972607814982727138161)
      ·
        refine ⟨40834479455861237045353621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54445972607814982727138161 40834479455861237045353621)
        ·
          refine ⟨1914116224493495486500951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40834479455861237045353621 1914116224493495486500951)
          ·
            refine ⟨2871174336740243229751427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1914116224493495486500951 2871174336740243229751427)
            ·
              refine ⟨4306761505110364844627141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871174336740243229751427 4306761505110364844627141)
              ·
                refine ⟨807517782208193408367589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4306761505110364844627141 807517782208193408367589)
                ·
                  refine ⟨151409584164036264068923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 807517782208193408367589 151409584164036264068923)
                  ·
                    rfl

theorem cell22_1326911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 4].length) (baseStart_1326911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326911 prefixEnd_1326911 := by exact prefixLift 1326911
  have htrace : WordTrace (prefixWord ++ tailWord_1326911) baseStart_1326911 baseEnd_1326911 := by
    simpa [prefixWord, tailWord_1326911, baseEnd_1326911] using wordTrace_append hprefix tailTrace_1326911
  have hstable : (prefixWord ++ tailWord_1326911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326911).length < 2 ^ (prefixWord ++ tailWord_1326911).sum := by decide
  have hdescent : baseEnd_1326911 < baseStart_1326911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326990 : List Nat := [4, 1, 1, 5, 2, 1, 2, 6]
def baseStart_1326990 : Nat := 118140960795 + 1326990 * 2 ^ 59
def prefixEnd_1326990 : Nat := 4983230072969 + 3 ^ 40 * 1326990 * 2
def baseEnd_1326990 : Nat := 50472866200730991053503

theorem tailTrace_1326990 : CollatzResearch.WordTrace tailWord_1326990 prefixEnd_1326990 50472866200730991053503 := by
  unfold tailWord_1326990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6049912682818667086753303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32266200975032891129350949 6049912682818667086753303)
  ·
    refine ⟨9074869024228000630129955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6049912682818667086753303 9074869024228000630129955)
    ·
      refine ⟨13612303536342000945194933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9074869024228000630129955 13612303536342000945194933)
      ·
        refine ⟨1276153456532062588612025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13612303536342000945194933 1276153456532062588612025)
        ·
          refine ⟨957115092399046941459019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1276153456532062588612025 957115092399046941459019)
          ·
            refine ⟨1435672638598570412188529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957115092399046941459019 1435672638598570412188529)
            ·
              refine ⟨1076754478948927809141397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435672638598570412188529 1076754478948927809141397)
              ·
                refine ⟨50472866200730991053503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1076754478948927809141397 50472866200730991053503)
                ·
                  rfl

theorem cell22_1326990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_1326990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1326990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1326990 prefixEnd_1326990 := by exact prefixLift 1326990
  have htrace : WordTrace (prefixWord ++ tailWord_1326990) baseStart_1326990 baseEnd_1326990 := by
    simpa [prefixWord, tailWord_1326990, baseEnd_1326990] using wordTrace_append hprefix tailTrace_1326990
  have hstable : (prefixWord ++ tailWord_1326990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326990).length < 2 ^ (prefixWord ++ tailWord_1326990).sum := by decide
  have hdescent : baseEnd_1326990 < baseStart_1326990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327005 : List Nat := [1, 4, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_1327005 : Nat := 118140960795 + 1327005 * 2 ^ 59
def prefixEnd_1327005 : Nat := 4983230072969 + 3 ^ 40 * 1327005 * 2
def baseEnd_1327005 : Nat := 454260930613123880356481

theorem tailTrace_1327005 : CollatzResearch.WordTrace tailWord_1327005 prefixEnd_1327005 454260930613123880356481 := by
  unfold tailWord_1327005
  simp only [CollatzResearch.WordTrace]
  refine ⟨48399848557494994255822469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32266565704996662837214979 48399848557494994255822469)
  ·
    refine ⟨9074971604530311422966713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48399848557494994255822469 9074971604530311422966713)
    ·
      refine ⟨6806228703397733567225035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9074971604530311422966713 6806228703397733567225035)
      ·
        refine ⟨10209343055096600350837553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6806228703397733567225035 10209343055096600350837553)
        ·
          refine ⟨7657007291322450263128165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10209343055096600350837553 7657007291322450263128165)
          ·
            refine ⟨1435688867122959424336531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7657007291322450263128165 1435688867122959424336531)
            ·
              refine ⟨2153533300684439136504797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1435688867122959424336531 2153533300684439136504797)
              ·
                refine ⟨807574987756664676189299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2153533300684439136504797 807574987756664676189299)
                ·
                  refine ⟨1211362481634997014283949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807574987756664676189299 1211362481634997014283949)
                  ·
                    refine ⟨454260930613123880356481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1211362481634997014283949 454260930613123880356481)
                    ·
                      rfl

theorem cell22_1327005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_1327005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327005 prefixEnd_1327005 := by exact prefixLift 1327005
  have htrace : WordTrace (prefixWord ++ tailWord_1327005) baseStart_1327005 baseEnd_1327005 := by
    simpa [prefixWord, tailWord_1327005, baseEnd_1327005] using wordTrace_append hprefix tailTrace_1327005
  have hstable : (prefixWord ++ tailWord_1327005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327005).length < 2 ^ (prefixWord ++ tailWord_1327005).sum := by decide
  have hdescent : baseEnd_1327005 < baseStart_1327005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327048 : List Nat := [2, 1, 3, 1, 4, 3, 1, 2, 1, 4]
def baseStart_1327048 : Nat := 118140960795 + 1327048 * 2 ^ 59
def prefixEnd_1327048 : Nat := 4983230072969 + 3 ^ 40 * 1327048 * 2
def baseEnd_1327048 : Nat := 454275650391886101531349

theorem tailTrace_1327048 : CollatzResearch.WordTrace tailWord_1327048 prefixEnd_1327048 454275650391886101531349 := by
  unfold tailWord_1327048
  simp only [CollatzResearch.WordTrace]
  refine ⟨24200708448169606299818899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32267611264226141733091865 24200708448169606299818899)
  ·
    refine ⟨36301062672254409449728349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24200708448169606299818899 36301062672254409449728349)
    ·
      refine ⟨13612898502095403543648131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36301062672254409449728349 13612898502095403543648131)
      ·
        refine ⟨20419347753143105315472197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13612898502095403543648131 20419347753143105315472197)
        ·
          refine ⟨3828627703714332246651037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20419347753143105315472197 3828627703714332246651037)
          ·
            refine ⟨1435735388892874592494139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3828627703714332246651037 1435735388892874592494139)
            ·
              refine ⟨2153603083339311888741209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1435735388892874592494139 2153603083339311888741209)
              ·
                refine ⟨1615202312504483916555907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2153603083339311888741209 1615202312504483916555907)
                ·
                  refine ⟨2422803468756725874833861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615202312504483916555907 2422803468756725874833861)
                  ·
                    refine ⟨454275650391886101531349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2422803468756725874833861 454275650391886101531349)
                    ·
                      rfl

theorem cell22_1327048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_1327048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327048 prefixEnd_1327048 := by exact prefixLift 1327048
  have htrace : WordTrace (prefixWord ++ tailWord_1327048) baseStart_1327048 baseEnd_1327048 := by
    simpa [prefixWord, tailWord_1327048, baseEnd_1327048] using wordTrace_append hprefix tailTrace_1327048
  have hstable : (prefixWord ++ tailWord_1327048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327048).length < 2 ^ (prefixWord ++ tailWord_1327048).sum := by decide
  have hdescent : baseEnd_1327048 < baseStart_1327048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327061 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_1327061 : Nat := 118140960795 + 1327061 * 2 ^ 59
def prefixEnd_1327061 : Nat := 4983230072969 + 3 ^ 40 * 1327061 * 2
def baseEnd_1327061 : Nat := 454280100557558400956309

theorem tailTrace_1327061 : CollatzResearch.WordTrace tailWord_1327061 prefixEnd_1327061 454280100557558400956309 := by
  unfold tailWord_1327061
  simp only [CollatzResearch.WordTrace]
  refine ⟨48401891045292115819861037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32267927363528077213240691 48401891045292115819861037)
  ·
    refine ⟨18150709141984543432447889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48401891045292115819861037 18150709141984543432447889)
    ·
      refine ⟨13613031856488407574335917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18150709141984543432447889 13613031856488407574335917)
      ·
        refine ⟨5104886946183152840375969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13613031856488407574335917 5104886946183152840375969)
        ·
          refine ⟨3828665209637364630281977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5104886946183152840375969 3828665209637364630281977)
          ·
            refine ⟨2871498907228023472711483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3828665209637364630281977 2871498907228023472711483)
            ·
              refine ⟨4307248360842035209067225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871498907228023472711483 4307248360842035209067225)
              ·
                refine ⟨3230436270631526406800419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4307248360842035209067225 3230436270631526406800419)
                ·
                  refine ⟨4845654405947289610200629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3230436270631526406800419 4845654405947289610200629)
                  ·
                    refine ⟨454280100557558400956309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4845654405947289610200629 454280100557558400956309)
                    ·
                      rfl

theorem cell22_1327061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_1327061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327061 prefixEnd_1327061 := by exact prefixLift 1327061
  have htrace : WordTrace (prefixWord ++ tailWord_1327061) baseStart_1327061 baseEnd_1327061 := by
    simpa [prefixWord, tailWord_1327061, baseEnd_1327061] using wordTrace_append hprefix tailTrace_1327061
  have hstable : (prefixWord ++ tailWord_1327061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327061).length < 2 ^ (prefixWord ++ tailWord_1327061).sum := by decide
  have hdescent : baseEnd_1327061 < baseStart_1327061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327123 : List Nat := [1, 1, 1, 2, 1, 4, 3, 5, 1, 3]
def baseStart_1327123 : Nat := 118140960795 + 1327123 * 2 ^ 59
def prefixEnd_1327123 : Nat := 4983230072969 + 3 ^ 40 * 1327123 * 2
def baseEnd_1327123 : Nat := 454301324424610905906119

theorem tailTrace_1327123 : CollatzResearch.WordTrace tailWord_1327123 prefixEnd_1327123 454301324424610905906119 := by
  unfold tailWord_1327123
  simp only [CollatzResearch.WordTrace]
  refine ⟨48404152371067500408618023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32269434914045000272412015 48404152371067500408618023)
  ·
    refine ⟨72606228556601250612927035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48404152371067500408618023 72606228556601250612927035)
    ·
      refine ⟨108909342834901875919390553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72606228556601250612927035 108909342834901875919390553)
      ·
        refine ⟨81682007126176406939542915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108909342834901875919390553 81682007126176406939542915)
        ·
          refine ⟨122523010689264610409314373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81682007126176406939542915 122523010689264610409314373)
          ·
            refine ⟨22973064504237114451746445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122523010689264610409314373 22973064504237114451746445)
            ·
              refine ⟨8614899189088917919404917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22973064504237114451746445 8614899189088917919404917)
              ·
                refine ⟨807646798977086054944211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8614899189088917919404917 807646798977086054944211)
                ·
                  refine ⟨1211470198465629082416317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807646798977086054944211 1211470198465629082416317)
                  ·
                    refine ⟨454301324424610905906119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1211470198465629082416317 454301324424610905906119)
                    ·
                      rfl

theorem cell22_1327123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 1, 3].length) (baseStart_1327123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327123 prefixEnd_1327123 := by exact prefixLift 1327123
  have htrace : WordTrace (prefixWord ++ tailWord_1327123) baseStart_1327123 baseEnd_1327123 := by
    simpa [prefixWord, tailWord_1327123, baseEnd_1327123] using wordTrace_append hprefix tailTrace_1327123
  have hstable : (prefixWord ++ tailWord_1327123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327123).length < 2 ^ (prefixWord ++ tailWord_1327123).sum := by decide
  have hdescent : baseEnd_1327123 < baseStart_1327123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327140 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_1327140 : Nat := 118140960795 + 1327140 * 2 ^ 59
def prefixEnd_1327140 : Nat := 4983230072969 + 3 ^ 40 * 1327140 * 2
def baseEnd_1327140 : Nat := 454307143872028528231067

theorem tailTrace_1327140 : CollatzResearch.WordTrace tailWord_1327140 prefixEnd_1327140 454307143872028528231067 := by
  unfold tailWord_1327140
  simp only [CollatzResearch.WordTrace]
  refine ⟨24202386206002956155993437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32269848274670608207991249 24202386206002956155993437)
  ·
    refine ⟨9075894827251108558497539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24202386206002956155993437 9075894827251108558497539)
    ·
      refine ⟨13613842240876662837746309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9075894827251108558497539 13613842240876662837746309)
      ·
        refine ⟨2552595420164374282077433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13613842240876662837746309 2552595420164374282077433)
        ·
          refine ⟨1914446565123280711558075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2552595420164374282077433 1914446565123280711558075)
          ·
            refine ⟨2871669847684921067337113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1914446565123280711558075 2871669847684921067337113)
            ·
              refine ⟨2153752385763690800502835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2871669847684921067337113 2153752385763690800502835)
              ·
                refine ⟨3230628578645536200754253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2153752385763690800502835 3230628578645536200754253)
                ·
                  refine ⟨1211485716992076075282845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3230628578645536200754253 1211485716992076075282845)
                  ·
                    refine ⟨454307143872028528231067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1211485716992076075282845 454307143872028528231067)
                    ·
                      rfl

theorem cell22_1327140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_1327140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327140 prefixEnd_1327140 := by exact prefixLift 1327140
  have htrace : WordTrace (prefixWord ++ tailWord_1327140) baseStart_1327140 baseEnd_1327140 := by
    simpa [prefixWord, tailWord_1327140, baseEnd_1327140] using wordTrace_append hprefix tailTrace_1327140
  have hstable : (prefixWord ++ tailWord_1327140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327140).length < 2 ^ (prefixWord ++ tailWord_1327140).sum := by decide
  have hdescent : baseEnd_1327140 < baseStart_1327140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327153 : List Nat := [1, 2, 2, 3, 1, 4, 3, 1, 5]
def baseStart_1327153 : Nat := 118140960795 + 1327153 * 2 ^ 59
def prefixEnd_1327153 : Nat := 4983230072969 + 3 ^ 40 * 1327153 * 2
def baseEnd_1327153 : Nat := 151437198012566942552009

theorem tailTrace_1327153 : CollatzResearch.WordTrace tailWord_1327153 prefixEnd_1327153 151437198012566942552009 := by
  unfold tailWord_1327153
  simp only [CollatzResearch.WordTrace]
  refine ⟨48405246560958815532210113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32270164373972543688140075 48405246560958815532210113)
  ·
    refine ⟨36303934920719111649157585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48405246560958815532210113 36303934920719111649157585)
    ·
      refine ⟨27227951190539333736868189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36303934920719111649157585 27227951190539333736868189)
      ·
        refine ⟨10210481696452250151325571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27227951190539333736868189 10210481696452250151325571)
        ·
          refine ⟨15315722544678375226988357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10210481696452250151325571 15315722544678375226988357)
          ·
            refine ⟨2871697977127195355060317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15315722544678375226988357 2871697977127195355060317)
            ·
              refine ⟨1076886741422698258147619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2871697977127195355060317 1076886741422698258147619)
              ·
                refine ⟨1615330112134047387221429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076886741422698258147619 1615330112134047387221429)
                ·
                  refine ⟨151437198012566942552009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1615330112134047387221429 151437198012566942552009)
                  ·
                    rfl

theorem cell22_1327153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 5].length) (baseStart_1327153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327153 prefixEnd_1327153 := by exact prefixLift 1327153
  have htrace : WordTrace (prefixWord ++ tailWord_1327153) baseStart_1327153 baseEnd_1327153 := by
    simpa [prefixWord, tailWord_1327153, baseEnd_1327153] using wordTrace_append hprefix tailTrace_1327153
  have hstable : (prefixWord ++ tailWord_1327153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327153).length < 2 ^ (prefixWord ++ tailWord_1327153).sum := by decide
  have hdescent : baseEnd_1327153 < baseStart_1327153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327228 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_1327228 : Nat := 118140960795 + 1327228 * 2 ^ 59
def prefixEnd_1327228 : Nat := 4983230072969 + 3 ^ 40 * 1327228 * 2
def baseEnd_1327228 : Nat := 454337268070425632030797

theorem tailTrace_1327228 : CollatzResearch.WordTrace tailWord_1327228 prefixEnd_1327228 454337268070425632030797 := by
  unfold tailWord_1327228
  simp only [CollatzResearch.WordTrace]
  refine ⟨24203991017843551670595169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32271988023791402227460225 24203991017843551670595169)
  ·
    refine ⟨18152993263382663752946377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24203991017843551670595169 18152993263382663752946377)
    ·
      refine ⟨13614744947536997814709783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18152993263382663752946377 13614744947536997814709783)
      ·
        refine ⟨20422117421305496722064675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13614744947536997814709783 20422117421305496722064675)
        ·
          refine ⟨30633176131958245083097013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20422117421305496722064675 30633176131958245083097013)
          ·
            refine ⟨2871860262371085476540345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30633176131958245083097013 2871860262371085476540345)
            ·
              refine ⟨2153895196778314107405259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2871860262371085476540345 2153895196778314107405259)
              ·
                refine ⟨3230842795167471161107889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2153895196778314107405259 3230842795167471161107889)
                ·
                  refine ⟨2423132096375603370830917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3230842795167471161107889 2423132096375603370830917)
                  ·
                    refine ⟨454337268070425632030797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2423132096375603370830917 454337268070425632030797)
                    ·
                      rfl

theorem cell22_1327228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_1327228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327228 prefixEnd_1327228 := by exact prefixLift 1327228
  have htrace : WordTrace (prefixWord ++ tailWord_1327228) baseStart_1327228 baseEnd_1327228 := by
    simpa [prefixWord, tailWord_1327228, baseEnd_1327228] using wordTrace_append hprefix tailTrace_1327228
  have hstable : (prefixWord ++ tailWord_1327228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327228).length < 2 ^ (prefixWord ++ tailWord_1327228).sum := by decide
  have hdescent : baseEnd_1327228 < baseStart_1327228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327333 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 6]
def baseStart_1327333 : Nat := 118140960795 + 1327333 * 2 ^ 59
def prefixEnd_1327333 : Nat := 4983230072969 + 3 ^ 40 * 1327333 * 2
def baseEnd_1327333 : Nat := 151457737238746786051825

theorem tailTrace_1327333 : CollatzResearch.WordTrace tailWord_1327333 prefixEnd_1327333 151457737238746786051825 := by
  unfold tailWord_1327333
  simp only [CollatzResearch.WordTrace]
  refine ⟨48411811700306706273762653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32274541133537804182508435 48411811700306706273762653)
  ·
    refine ⟨18154429387615014852660995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48411811700306706273762653 18154429387615014852660995)
    ·
      refine ⟨27231644081422522278991493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18154429387615014852660995 27231644081422522278991493)
      ·
        refine ⟨5105933265266722927310905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27231644081422522278991493 5105933265266722927310905)
        ·
          refine ⟨3829449948950042195483179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5105933265266722927310905 3829449948950042195483179)
          ·
            refine ⟨5744174923425063293224769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829449948950042195483179 5744174923425063293224769)
            ·
              refine ⟨4308131192568797469918577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5744174923425063293224769 4308131192568797469918577)
              ·
                refine ⟨3231098394426598102438933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4308131192568797469918577 3231098394426598102438933)
                ·
                  refine ⟨151457737238746786051825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3231098394426598102438933 151457737238746786051825)
                  ·
                    rfl

theorem cell22_1327333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_1327333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327333 prefixEnd_1327333 := by exact prefixLift 1327333
  have htrace : WordTrace (prefixWord ++ tailWord_1327333) baseStart_1327333 baseEnd_1327333 := by
    simpa [prefixWord, tailWord_1327333, baseEnd_1327333] using wordTrace_append hprefix tailTrace_1327333
  have hstable : (prefixWord ++ tailWord_1327333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327333).length < 2 ^ (prefixWord ++ tailWord_1327333).sum := by decide
  have hdescent : baseEnd_1327333 < baseStart_1327333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327335 : List Nat := [1, 1, 5, 3, 1, 1, 1, 4, 1, 4]
def baseStart_1327335 : Nat := 118140960795 + 1327335 * 2 ^ 59
def prefixEnd_1327335 : Nat := 4983230072969 + 3 ^ 40 * 1327335 * 2
def baseEnd_1327335 : Nat := 454373896357113019605469

theorem tailTrace_1327335 : CollatzResearch.WordTrace tailWord_1327335 prefixEnd_1327335 454373896357113019605469 := by
  unfold tailWord_1327335
  simp only [CollatzResearch.WordTrace]
  refine ⟨48411884646299460615335459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32274589764199640410223639 48411884646299460615335459)
  ·
    refine ⟨72617826969449190923003189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48411884646299460615335459 72617826969449190923003189)
    ·
      refine ⟨6807921278385861649031549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72617826969449190923003189 6807921278385861649031549)
      ·
        refine ⟨2552970479394698118386831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6807921278385861649031549 2552970479394698118386831)
        ·
          refine ⟨3829455719092047177580247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552970479394698118386831 3829455719092047177580247)
          ·
            refine ⟨5744183578638070766370371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829455719092047177580247 5744183578638070766370371)
            ·
              refine ⟨8616275367957106149555557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5744183578638070766370371 8616275367957106149555557)
              ·
                refine ⟨1615551631491957403041667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8616275367957106149555557 1615551631491957403041667)
                ·
                  refine ⟨2423327447237936104562501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615551631491957403041667 2423327447237936104562501)
                  ·
                    refine ⟨454373896357113019605469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2423327447237936104562501 454373896357113019605469)
                    ·
                      rfl

theorem cell22_1327335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_1327335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327335 prefixEnd_1327335 := by exact prefixLift 1327335
  have htrace : WordTrace (prefixWord ++ tailWord_1327335) baseStart_1327335 baseEnd_1327335 := by
    simpa [prefixWord, tailWord_1327335, baseEnd_1327335] using wordTrace_append hprefix tailTrace_1327335
  have hstable : (prefixWord ++ tailWord_1327335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327335).length < 2 ^ (prefixWord ++ tailWord_1327335).sum := by decide
  have hdescent : baseEnd_1327335 < baseStart_1327335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327363 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 2, 4]
def baseStart_1327363 : Nat := 118140960795 + 1327363 * 2 ^ 59
def prefixEnd_1327363 : Nat := 4983230072969 + 3 ^ 40 * 1327363 * 2
def baseEnd_1327363 : Nat := 454383481329330279905383

theorem tailTrace_1327363 : CollatzResearch.WordTrace tailWord_1327363 prefixEnd_1327363 454383481329330279905383 := by
  unfold tailWord_1327363
  simp only [CollatzResearch.WordTrace]
  refine ⟨48412905890198021397354743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32275270593465347598236495 48412905890198021397354743)
  ·
    refine ⟨72619358835297032096032115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48412905890198021397354743 72619358835297032096032115)
    ·
      refine ⟨108929038252945548144048173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72619358835297032096032115 108929038252945548144048173)
      ·
        refine ⟨40848389344854580554018065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108929038252945548144048173 40848389344854580554018065)
        ·
          refine ⟨30636292008640935415513549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40848389344854580554018065 30636292008640935415513549)
          ·
            refine ⟨11488609503240350780817581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30636292008640935415513549 11488609503240350780817581)
            ·
              refine ⟨4308228563715131542806593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11488609503240350780817581 4308228563715131542806593)
              ·
                refine ⟨3231171422786348657104945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4308228563715131542806593 3231171422786348657104945)
                ·
                  refine ⟨2423378567089761492828709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3231171422786348657104945 2423378567089761492828709)
                  ·
                    refine ⟨454383481329330279905383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2423378567089761492828709 454383481329330279905383)
                    ·
                      rfl

theorem cell22_1327363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 4].length) (baseStart_1327363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327363 prefixEnd_1327363 := by exact prefixLift 1327363
  have htrace : WordTrace (prefixWord ++ tailWord_1327363) baseStart_1327363 baseEnd_1327363 := by
    simpa [prefixWord, tailWord_1327363, baseEnd_1327363] using wordTrace_append hprefix tailTrace_1327363
  have hstable : (prefixWord ++ tailWord_1327363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327363).length < 2 ^ (prefixWord ++ tailWord_1327363).sum := by decide
  have hdescent : baseEnd_1327363 < baseStart_1327363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327367 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 6]
def baseStart_1327367 : Nat := 118140960795 + 1327367 * 2 ^ 59
def prefixEnd_1327367 : Nat := 4983230072969 + 3 ^ 40 * 1327367 * 2
def baseEnd_1327367 : Nat := 151461616870358534268457

theorem tailTrace_1327367 : CollatzResearch.WordTrace tailWord_1327367 prefixEnd_1327367 151461616870358534268457 := by
  unfold tailWord_1327367
  simp only [CollatzResearch.WordTrace]
  refine ⟨48413051782183530080500355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32275367854789020053666903 48413051782183530080500355)
  ·
    refine ⟨72619577673275295120750533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48413051782183530080500355 72619577673275295120750533)
    ·
      refine ⟨13616170813739117835140725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72619577673275295120750533 13616170813739117835140725)
      ·
        refine ⟨1276516013788042297044443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13616170813739117835140725 1276516013788042297044443)
        ·
          refine ⟨1914774020682063445566665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1276516013788042297044443 1914774020682063445566665)
          ·
            refine ⟨1436080515511547584174999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1914774020682063445566665 1436080515511547584174999)
            ·
              refine ⟨2154120773267321376262499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436080515511547584174999 2154120773267321376262499)
              ·
                refine ⟨3231181159900982064393749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154120773267321376262499 3231181159900982064393749)
                ·
                  refine ⟨151461616870358534268457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3231181159900982064393749 151461616870358534268457)
                  ·
                    rfl

theorem cell22_1327367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 6].length) (baseStart_1327367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327367 prefixEnd_1327367 := by exact prefixLift 1327367
  have htrace : WordTrace (prefixWord ++ tailWord_1327367) baseStart_1327367 baseEnd_1327367 := by
    simpa [prefixWord, tailWord_1327367, baseEnd_1327367] using wordTrace_append hprefix tailTrace_1327367
  have hstable : (prefixWord ++ tailWord_1327367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327367).length < 2 ^ (prefixWord ++ tailWord_1327367).sum := by decide
  have hdescent : baseEnd_1327367 < baseStart_1327367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327399 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1327399 : Nat := 118140960795 + 1327399 * 2 ^ 59
def prefixEnd_1327399 : Nat := 4983230072969 + 3 ^ 40 * 1327399 * 2
def baseEnd_1327399 : Nat := 454395804865038186005273

theorem tailTrace_1327399 : CollatzResearch.WordTrace tailWord_1327399 prefixEnd_1327399 454395804865038186005273 := by
  unfold tailWord_1327399
  simp only [CollatzResearch.WordTrace]
  refine ⟨48414218918067599545665251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32276145945378399697110167 48414218918067599545665251)
  ·
    refine ⟨72621328377101399318497877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48414218918067599545665251 72621328377101399318497877)
    ·
      refine ⟨851031191919157023263647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 72621328377101399318497877 851031191919157023263647)
      ·
        refine ⟨1276546787878735534895471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851031191919157023263647 1276546787878735534895471)
        ·
          refine ⟨1914820181818103302343207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1276546787878735534895471 1914820181818103302343207)
          ·
            refine ⟨2872230272727154953514811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1914820181818103302343207 2872230272727154953514811)
            ·
              refine ⟨4308345409090732430272217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2872230272727154953514811 4308345409090732430272217)
              ·
                refine ⟨3231259056818049322704163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4308345409090732430272217 3231259056818049322704163)
                ·
                  refine ⟨4846888585227073984056245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3231259056818049322704163 4846888585227073984056245)
                  ·
                    refine ⟨454395804865038186005273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4846888585227073984056245 454395804865038186005273)
                    ·
                      rfl

theorem cell22_1327399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1327399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327399 prefixEnd_1327399 := by exact prefixLift 1327399
  have htrace : WordTrace (prefixWord ++ tailWord_1327399) baseStart_1327399 baseEnd_1327399 := by
    simpa [prefixWord, tailWord_1327399, baseEnd_1327399] using wordTrace_append hprefix tailTrace_1327399
  have hstable : (prefixWord ++ tailWord_1327399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327399).length < 2 ^ (prefixWord ++ tailWord_1327399).sum := by decide
  have hdescent : baseEnd_1327399 < baseStart_1327399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327485 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 6]
def baseStart_1327485 : Nat := 118140960795 + 1327485 * 2 ^ 59
def prefixEnd_1327485 : Nat := 4983230072969 + 3 ^ 40 * 1327485 * 2
def baseEnd_1327485 : Nat := 151475081474187542785003

theorem tailTrace_1327485 : CollatzResearch.WordTrace tailWord_1327485 prefixEnd_1327485 151475081474187542785003 := by
  unfold tailWord_1327485
  simp only [CollatzResearch.WordTrace]
  refine ⟨48417355595756036233295909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32278237063837357488863939 48417355595756036233295909)
  ·
    refine ⟨9078254174204256793742983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48417355595756036233295909 9078254174204256793742983)
    ·
      refine ⟨13617381261306385190614475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9078254174204256793742983 13617381261306385190614475)
      ·
        refine ⟨20426071891959577785921713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13617381261306385190614475 20426071891959577785921713)
        ·
          refine ⟨15319553918969683339441285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20426071891959577785921713 15319553918969683339441285)
          ·
            refine ⟨2872416359806815626145241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15319553918969683339441285 2872416359806815626145241)
            ·
              refine ⟨2154312269855111719608931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2872416359806815626145241 2154312269855111719608931)
              ·
                refine ⟨3231468404782667579413397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154312269855111719608931 3231468404782667579413397)
                ·
                  refine ⟨151475081474187542785003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3231468404782667579413397 151475081474187542785003)
                  ·
                    rfl

theorem cell22_1327485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_1327485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327485 prefixEnd_1327485 := by exact prefixLift 1327485
  have htrace : WordTrace (prefixWord ++ tailWord_1327485) baseStart_1327485 baseEnd_1327485 := by
    simpa [prefixWord, tailWord_1327485, baseEnd_1327485] using wordTrace_append hprefix tailTrace_1327485
  have hstable : (prefixWord ++ tailWord_1327485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327485).length < 2 ^ (prefixWord ++ tailWord_1327485).sum := by decide
  have hdescent : baseEnd_1327485 < baseStart_1327485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327500 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_1327500 : Nat := 118140960795 + 1327500 * 2 ^ 59
def prefixEnd_1327500 : Nat := 4983230072969 + 3 ^ 40 * 1327500 * 2
def baseEnd_1327500 : Nat := 454430379229107589229963

theorem tailTrace_1327500 : CollatzResearch.WordTrace tailWord_1327500 prefixEnd_1327500 454430379229107589229963 := by
  unfold tailWord_1327500
  simp only [CollatzResearch.WordTrace]
  refine ⟨24208951345350846897545977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32278601793801129196727969 24208951345350846897545977)
  ·
    refine ⟨18156713509013135173159483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24208951345350846897545977 18156713509013135173159483)
    ·
      refine ⟨27235070263519702759739225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18156713509013135173159483 27235070263519702759739225)
      ·
        refine ⟨20426302697639777069804419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27235070263519702759739225 20426302697639777069804419)
        ·
          refine ⟨30639454046459665604706629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20426302697639777069804419 30639454046459665604706629)
          ·
            refine ⟨5744897633711187300882493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30639454046459665604706629 5744897633711187300882493)
            ·
              refine ⟨2154336612641695237830935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5744897633711187300882493 2154336612641695237830935)
              ·
                refine ⟨3231504918962542856746403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154336612641695237830935 3231504918962542856746403)
                ·
                  refine ⟨4847257378443814285119605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3231504918962542856746403 4847257378443814285119605)
                  ·
                    refine ⟨454430379229107589229963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4847257378443814285119605 454430379229107589229963)
                    ·
                      rfl

theorem cell22_1327500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_1327500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327500 prefixEnd_1327500 := by exact prefixLift 1327500
  have htrace : WordTrace (prefixWord ++ tailWord_1327500) baseStart_1327500 baseEnd_1327500 := by
    simpa [prefixWord, tailWord_1327500, baseEnd_1327500] using wordTrace_append hprefix tailTrace_1327500
  have hstable : (prefixWord ++ tailWord_1327500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327500).length < 2 ^ (prefixWord ++ tailWord_1327500).sum := by decide
  have hdescent : baseEnd_1327500 < baseStart_1327500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327513 : List Nat := [1, 2, 1, 2, 1, 4, 3, 8]
def baseStart_1327513 : Nat := 118140960795 + 1327513 * 2 ^ 59
def prefixEnd_1327513 : Nat := 4983230072969 + 3 ^ 40 * 1327513 * 2
def baseEnd_1327513 : Nat := 50492758821642209850547

theorem tailTrace_1327513 : CollatzResearch.WordTrace tailWord_1327513 prefixEnd_1327513 50492758821642209850547 := by
  unfold tailWord_1327513
  simp only [CollatzResearch.WordTrace]
  refine ⟨48418376839654597015315193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32278917893103064676876795 48418376839654597015315193)
  ·
    refine ⟨36313782629740947761486395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48418376839654597015315193 36313782629740947761486395)
    ·
      refine ⟨54470673944611421642229593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36313782629740947761486395 54470673944611421642229593)
      ·
        refine ⟨40853005458458566231672195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54470673944611421642229593 40853005458458566231672195)
        ·
          refine ⟨61279508187687849347508293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40853005458458566231672195 61279508187687849347508293)
          ·
            refine ⟨11489907785191471752657805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61279508187687849347508293 11489907785191471752657805)
            ·
              refine ⟨4308715419446801907246677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11489907785191471752657805 4308715419446801907246677)
              ·
                refine ⟨50492758821642209850547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4308715419446801907246677 50492758821642209850547)
                ·
                  rfl

theorem cell22_1327513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 8].length) (baseStart_1327513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327513 prefixEnd_1327513 := by exact prefixLift 1327513
  have htrace : WordTrace (prefixWord ++ tailWord_1327513) baseStart_1327513 baseEnd_1327513 := by
    simpa [prefixWord, tailWord_1327513, baseEnd_1327513] using wordTrace_append hprefix tailTrace_1327513
  have hstable : (prefixWord ++ tailWord_1327513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327513).length < 2 ^ (prefixWord ++ tailWord_1327513).sum := by decide
  have hdescent : baseEnd_1327513 < baseStart_1327513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327592 : List Nat := [2, 1, 4, 1, 1, 4, 2, 2, 5]
def baseStart_1327592 : Nat := 118140960795 + 1327592 * 2 ^ 59
def prefixEnd_1327592 : Nat := 4983230072969 + 3 ^ 40 * 1327592 * 2
def baseEnd_1327592 : Nat := 151487290903083338643227

theorem tailTrace_1327592 : CollatzResearch.WordTrace tailWord_1327592 prefixEnd_1327592 151487290903083338643227 := by
  unfold tailWord_1327592
  simp only [CollatzResearch.WordTrace]
  refine ⟨24210629103184196753720515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32280838804245595671627353 24210629103184196753720515)
  ·
    refine ⟨36315943654776295130580773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24210629103184196753720515 36315943654776295130580773)
    ·
      refine ⟨6809239435270555336983895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36315943654776295130580773 6809239435270555336983895)
      ·
        refine ⟨10213859152905833005475843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6809239435270555336983895 10213859152905833005475843)
        ·
          refine ⟨15320788729358749508213765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10213859152905833005475843 15320788729358749508213765)
          ·
            refine ⟨2872647886754765532790081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15320788729358749508213765 2872647886754765532790081)
            ·
              refine ⟨2154485915066074149592561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2872647886754765532790081 2154485915066074149592561)
              ·
                refine ⟨1615864436299555612194421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2154485915066074149592561 1615864436299555612194421)
                ·
                  refine ⟨151487290903083338643227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1615864436299555612194421 151487290903083338643227)
                  ·
                    rfl

theorem cell22_1327592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 5].length) (baseStart_1327592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327592 prefixEnd_1327592 := by exact prefixLift 1327592
  have htrace : WordTrace (prefixWord ++ tailWord_1327592) baseStart_1327592 baseEnd_1327592 := by
    simpa [prefixWord, tailWord_1327592, baseEnd_1327592] using wordTrace_append hprefix tailTrace_1327592
  have hstable : (prefixWord ++ tailWord_1327592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327592).length < 2 ^ (prefixWord ++ tailWord_1327592).sum := by decide
  have hdescent : baseEnd_1327592 < baseStart_1327592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327635 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 1, 5]
def baseStart_1327635 : Nat := 118140960795 + 1327635 * 2 ^ 59
def prefixEnd_1327635 : Nat := 4983230072969 + 3 ^ 40 * 1327635 * 2
def baseEnd_1327635 : Nat := 454476592488012237104549

theorem tailTrace_1327635 : CollatzResearch.WordTrace tailWord_1327635 prefixEnd_1327635 454476592488012237104549 := by
  unfold tailWord_1327635
  simp only [CollatzResearch.WordTrace]
  refine ⟨48422826545212611851256359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32281884363475074567504239 48422826545212611851256359)
  ·
    refine ⟨72634239817818917776884539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48422826545212611851256359 72634239817818917776884539)
    ·
      refine ⟨108951359726728376665326809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72634239817818917776884539 108951359726728376665326809)
      ·
        refine ⟨81713519795046282498995107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108951359726728376665326809 81713519795046282498995107)
        ·
          refine ⟨122570279692569423748492661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81713519795046282498995107 122570279692569423748492661)
          ·
            refine ⟨11490963721178383476421187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122570279692569423748492661 11490963721178383476421187)
            ·
              refine ⟨17236445581767575214631781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11490963721178383476421187 17236445581767575214631781)
              ·
                refine ⟨3231833546581420352743459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17236445581767575214631781 3231833546581420352743459)
                ·
                  refine ⟨4847750319872130529115189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3231833546581420352743459 4847750319872130529115189)
                  ·
                    refine ⟨454476592488012237104549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4847750319872130529115189 454476592488012237104549)
                    ·
                      rfl

theorem cell22_1327635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 5].length) (baseStart_1327635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327635 prefixEnd_1327635 := by exact prefixLift 1327635
  have htrace : WordTrace (prefixWord ++ tailWord_1327635) baseStart_1327635 baseEnd_1327635 := by
    simpa [prefixWord, tailWord_1327635, baseEnd_1327635] using wordTrace_append hprefix tailTrace_1327635
  have hstable : (prefixWord ++ tailWord_1327635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327635).length < 2 ^ (prefixWord ++ tailWord_1327635).sum := by decide
  have hdescent : baseEnd_1327635 < baseStart_1327635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327686 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1327686 : Nat := 118140960795 + 1327686 * 2 ^ 59
def prefixEnd_1327686 : Nat := 4983230072969 + 3 ^ 40 * 1327686 * 2
def baseEnd_1327686 : Nat := 454494050830265104079393

theorem tailTrace_1327686 : CollatzResearch.WordTrace tailWord_1327686 prefixEnd_1327686 454494050830265104079393 := by
  unfold tailWord_1327686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1513271458375870236292591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32283124445351898374241941 1513271458375870236292591)
  ·
    refine ⟨2269907187563805354438887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1513271458375870236292591 2269907187563805354438887)
    ·
      refine ⟨3404860781345708031658331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2269907187563805354438887 3404860781345708031658331)
      ·
        refine ⟨5107291172018562047487497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3404860781345708031658331 5107291172018562047487497)
        ·
          refine ⟨3830468379013921535615623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5107291172018562047487497 3830468379013921535615623)
          ·
            refine ⟨5745702568520882303423435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3830468379013921535615623 5745702568520882303423435)
            ·
              refine ⟨8618553852781323455135153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5745702568520882303423435 8618553852781323455135153)
              ·
                refine ⟨6463915389585992591351365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8618553852781323455135153 6463915389585992591351365)
                ·
                  refine ⟨1211984135547373610878381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6463915389585992591351365 1211984135547373610878381)
                  ·
                    refine ⟨454494050830265104079393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1211984135547373610878381 454494050830265104079393)
                    ·
                      rfl

theorem cell22_1327686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1327686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327686 prefixEnd_1327686 := by exact prefixLift 1327686
  have htrace : WordTrace (prefixWord ++ tailWord_1327686) baseStart_1327686 baseEnd_1327686 := by
    simpa [prefixWord, tailWord_1327686, baseEnd_1327686] using wordTrace_append hprefix tailTrace_1327686
  have hstable : (prefixWord ++ tailWord_1327686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327686).length < 2 ^ (prefixWord ++ tailWord_1327686).sum := by decide
  have hdescent : baseEnd_1327686 < baseStart_1327686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327720 : List Nat := [2, 1, 4, 3, 3, 1, 2, 1, 2, 3]
def baseStart_1327720 : Nat := 118140960795 + 1327720 * 2 ^ 59
def prefixEnd_1327720 : Nat := 4983230072969 + 3 ^ 40 * 1327720 * 2
def baseEnd_1327720 : Nat := 454505689725100348729289

theorem tailTrace_1327720 : CollatzResearch.WordTrace tailWord_1327720 prefixEnd_1327720 454505689725100348729289 := by
  unfold tailWord_1327720
  simp only [CollatzResearch.WordTrace]
  refine ⟨24212963374952335684050307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32283951166603114245400409 24212963374952335684050307)
  ·
    refine ⟨36319445062428503526075461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24212963374952335684050307 36319445062428503526075461)
    ·
      refine ⟨6809895949205344411139149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36319445062428503526075461 6809895949205344411139149)
      ·
        refine ⟨2553710980952004154177181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6809895949205344411139149 2553710980952004154177181)
        ·
          refine ⟨957641617857001557816443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2553710980952004154177181 957641617857001557816443)
          ·
            refine ⟨1436462426785502336724665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957641617857001557816443 1436462426785502336724665)
            ·
              refine ⟨1077346820089126752543499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1436462426785502336724665 1077346820089126752543499)
              ·
                refine ⟨1616020230133690128815249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077346820089126752543499 1616020230133690128815249)
                ·
                  refine ⟨1212015172600267596611437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1616020230133690128815249 1212015172600267596611437)
                  ·
                    refine ⟨454505689725100348729289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1212015172600267596611437 454505689725100348729289)
                    ·
                      rfl

theorem cell22_1327720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_1327720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327720 prefixEnd_1327720 := by exact prefixLift 1327720
  have htrace : WordTrace (prefixWord ++ tailWord_1327720) baseStart_1327720 baseEnd_1327720 := by
    simpa [prefixWord, tailWord_1327720, baseEnd_1327720] using wordTrace_append hprefix tailTrace_1327720
  have hstable : (prefixWord ++ tailWord_1327720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327720).length < 2 ^ (prefixWord ++ tailWord_1327720).sum := by decide
  have hdescent : baseEnd_1327720 < baseStart_1327720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327755 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 10]
def baseStart_1327755 : Nat := 118140960795 + 1327755 * 2 ^ 59
def prefixEnd_1327755 : Nat := 4983230072969 + 3 ^ 40 * 1327755 * 2
def baseEnd_1327755 : Nat := 151505890313457308034727

theorem tailTrace_1327755 : CollatzResearch.WordTrace tailWord_1327755 prefixEnd_1327755 151505890313457308034727 := by
  unfold tailWord_1327755
  simp only [CollatzResearch.WordTrace]
  refine ⟨48427203304777872345624719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32284802203185248230416479 48427203304777872345624719)
  ·
    refine ⟨72640804957166808518437079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48427203304777872345624719 72640804957166808518437079)
    ·
      refine ⟨108961207435750212777655619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72640804957166808518437079 108961207435750212777655619)
      ·
        refine ⟨163441811153625319166483429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108961207435750212777655619 163441811153625319166483429)
        ·
          refine ⟨30645339591304747343715643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163441811153625319166483429 30645339591304747343715643)
          ·
            refine ⟨45968009386957121015573465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30645339591304747343715643 45968009386957121015573465)
            ·
              refine ⟨34476007040217840761680099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45968009386957121015573465 34476007040217840761680099)
              ·
                refine ⟨51714010560326761142520149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34476007040217840761680099 51714010560326761142520149)
                ·
                  refine ⟨151505890313457308034727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 51714010560326761142520149 151505890313457308034727)
                  ·
                    rfl

theorem cell22_1327755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 10].length) (baseStart_1327755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327755 prefixEnd_1327755 := by exact prefixLift 1327755
  have htrace : WordTrace (prefixWord ++ tailWord_1327755) baseStart_1327755 baseEnd_1327755 := by
    simpa [prefixWord, tailWord_1327755, baseEnd_1327755] using wordTrace_append hprefix tailTrace_1327755
  have hstable : (prefixWord ++ tailWord_1327755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327755).length < 2 ^ (prefixWord ++ tailWord_1327755).sum := by decide
  have hdescent : baseEnd_1327755 < baseStart_1327755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327774 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1327774 : Nat := 118140960795 + 1327774 * 2 ^ 59
def prefixEnd_1327774 : Nat := 4983230072969 + 3 ^ 40 * 1327774 * 2
def baseEnd_1327774 : Nat := 454524175028662207879123

theorem tailTrace_1327774 : CollatzResearch.WordTrace tailWord_1327774 prefixEnd_1327774 454524175028662207879123 := by
  unfold tailWord_1327774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6053487036463629823820797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32285264194472692393710917 6053487036463629823820797)
  ·
    refine ⟨2270057638673861183932799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6053487036463629823820797 2270057638673861183932799)
    ·
      refine ⟨3405086458010791775899199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2270057638673861183932799 3405086458010791775899199)
      ·
        refine ⟨5107629687016187663848799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3405086458010791775899199 5107629687016187663848799)
        ·
          refine ⟨7661444530524281495773199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5107629687016187663848799 7661444530524281495773199)
          ·
            refine ⟨11492166795786422243659799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7661444530524281495773199 11492166795786422243659799)
            ·
              refine ⟨17238250193679633365489699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11492166795786422243659799 17238250193679633365489699)
              ·
                refine ⟨25857375290519450048234549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17238250193679633365489699 25857375290519450048234549)
                ·
                  refine ⟨2424128933486198442021989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25857375290519450048234549 2424128933486198442021989)
                  ·
                    refine ⟨454524175028662207879123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2424128933486198442021989 454524175028662207879123)
                    ·
                      rfl

theorem cell22_1327774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1327774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327774 prefixEnd_1327774 := by exact prefixLift 1327774
  have htrace : WordTrace (prefixWord ++ tailWord_1327774) baseStart_1327774 baseEnd_1327774 := by
    simpa [prefixWord, tailWord_1327774, baseEnd_1327774] using wordTrace_append hprefix tailTrace_1327774
  have hstable : (prefixWord ++ tailWord_1327774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327774).length < 2 ^ (prefixWord ++ tailWord_1327774).sum := by decide
  have hdescent : baseEnd_1327774 < baseStart_1327774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327789 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 6]
def baseStart_1327789 : Nat := 118140960795 + 1327789 * 2 ^ 59
def prefixEnd_1327789 : Nat := 4983230072969 + 3 ^ 40 * 1327789 * 2
def baseEnd_1327789 : Nat := 151509769945069056251359

theorem tailTrace_1327789 : CollatzResearch.WordTrace tailWord_1327789 prefixEnd_1327789 151509769945069056251359 := by
  unfold tailWord_1327789
  simp only [CollatzResearch.WordTrace]
  refine ⟨48428443386654696152362421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32285628924436464101574947 48428443386654696152362421)
  ·
    refine ⟨4540166567498877764283977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48428443386654696152362421 4540166567498877764283977)
    ·
      refine ⟨3405124925624158323212983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4540166567498877764283977 3405124925624158323212983)
      ·
        refine ⟨5107687388436237484819475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3405124925624158323212983 5107687388436237484819475)
        ·
          refine ⟨7661531082654356227229213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5107687388436237484819475 7661531082654356227229213)
          ·
            refine ⟨2873074155995383585210955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7661531082654356227229213 2873074155995383585210955)
            ·
              refine ⟨4309611233993075377816433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873074155995383585210955 4309611233993075377816433)
              ·
                refine ⟨3232208425494806533362325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4309611233993075377816433 3232208425494806533362325)
                ·
                  refine ⟨151509769945069056251359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3232208425494806533362325 151509769945069056251359)
                  ·
                    rfl

theorem cell22_1327789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_1327789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327789 prefixEnd_1327789 := by exact prefixLift 1327789
  have htrace : WordTrace (prefixWord ++ tailWord_1327789) baseStart_1327789 baseEnd_1327789 := by
    simpa [prefixWord, tailWord_1327789, baseEnd_1327789] using wordTrace_append hprefix tailTrace_1327789
  have hstable : (prefixWord ++ tailWord_1327789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327789).length < 2 ^ (prefixWord ++ tailWord_1327789).sum := by decide
  have hdescent : baseEnd_1327789 < baseStart_1327789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327802 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_1327802 : Nat := 118140960795 + 1327802 * 2 ^ 59
def prefixEnd_1327802 : Nat := 4983230072969 + 3 ^ 40 * 1327802 * 2
def baseEnd_1327802 : Nat := 454533760000879468179037

theorem tailTrace_1327802 : CollatzResearch.WordTrace tailWord_1327802 prefixEnd_1327802 454533760000879468179037 := by
  unfold tailWord_1327802
  simp only [CollatzResearch.WordTrace]
  refine ⟨12107229383901899843146415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32285945023738399581723773 12107229383901899843146415)
  ·
    refine ⟨18160844075852849764719623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12107229383901899843146415 18160844075852849764719623)
    ·
      refine ⟨27241266113779274647079435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18160844075852849764719623 27241266113779274647079435)
      ·
        refine ⟨40861899170668911970619153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27241266113779274647079435 40861899170668911970619153)
        ·
          refine ⟨30646424378001683977964365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40861899170668911970619153 30646424378001683977964365)
          ·
            refine ⟨11492409141750631491736637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30646424378001683977964365 11492409141750631491736637)
            ·
              refine ⟨4309653428156486809401239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11492409141750631491736637 4309653428156486809401239)
              ·
                refine ⟨6464480142234730214101859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4309653428156486809401239 6464480142234730214101859)
                ·
                  refine ⟨9696720213352095321152789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6464480142234730214101859 9696720213352095321152789)
                  ·
                    refine ⟨454533760000879468179037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9696720213352095321152789 454533760000879468179037)
                    ·
                      rfl

theorem cell22_1327802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_1327802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327802 prefixEnd_1327802 := by exact prefixLift 1327802
  have htrace : WordTrace (prefixWord ++ tailWord_1327802) baseStart_1327802 baseEnd_1327802 := by
    simpa [prefixWord, tailWord_1327802, baseEnd_1327802] using wordTrace_append hprefix tailTrace_1327802
  have hstable : (prefixWord ++ tailWord_1327802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327802).length < 2 ^ (prefixWord ++ tailWord_1327802).sum := by decide
  have hdescent : baseEnd_1327802 < baseStart_1327802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327804 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 4, 3]
def baseStart_1327804 : Nat := 118140960795 + 1327804 * 2 ^ 59
def prefixEnd_1327804 : Nat := 4983230072969 + 3 ^ 40 * 1327804 * 2
def baseEnd_1327804 : Nat := 454534444641752129629031

theorem tailTrace_1327804 : CollatzResearch.WordTrace tailWord_1327804 prefixEnd_1327804 454534444641752129629031 := by
  unfold tailWord_1327804
  simp only [CollatzResearch.WordTrace]
  refine ⟨24214495240800176857079233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32285993654400235809438977 24214495240800176857079233)
  ·
    refine ⟨18160871430600132642809425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24214495240800176857079233 18160871430600132642809425)
    ·
      refine ⟨13620653572950099482107069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18160871430600132642809425 13620653572950099482107069)
      ·
        refine ⟨5107745089856287305790151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13620653572950099482107069 5107745089856287305790151)
        ·
          refine ⟨7661617634784430958685227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5107745089856287305790151 7661617634784430958685227)
          ·
            refine ⟨11492426452176646438027841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7661617634784430958685227 11492426452176646438027841)
            ·
              refine ⟨8619319839132484828520881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11492426452176646438027841 8619319839132484828520881)
              ·
                refine ⟨6464489879349363621390661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8619319839132484828520881 6464489879349363621390661)
                ·
                  refine ⟨1212091852378005679010749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6464489879349363621390661 1212091852378005679010749)
                  ·
                    refine ⟨454534444641752129629031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1212091852378005679010749 454534444641752129629031)
                    ·
                      rfl

theorem cell22_1327804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_1327804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327804 prefixEnd_1327804 := by exact prefixLift 1327804
  have htrace : WordTrace (prefixWord ++ tailWord_1327804) baseStart_1327804 baseEnd_1327804 := by
    simpa [prefixWord, tailWord_1327804, baseEnd_1327804] using wordTrace_append hprefix tailTrace_1327804
  have hstable : (prefixWord ++ tailWord_1327804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327804).length < 2 ^ (prefixWord ++ tailWord_1327804).sum := by decide
  have hdescent : baseEnd_1327804 < baseStart_1327804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327806 : List Nat := [4, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_1327806 : Nat := 118140960795 + 1327806 * 2 ^ 59
def prefixEnd_1327806 : Nat := 4983230072969 + 3 ^ 40 * 1327806 * 2
def baseEnd_1327806 : Nat := 151511709760874930359675

theorem tailTrace_1327806 : CollatzResearch.WordTrace tailWord_1327806 prefixEnd_1327806 151511709760874930359675 := by
  unfold tailWord_1327806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6053632928449138506966409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32286042285062072037154181 6053632928449138506966409)
  ·
    refine ⟨4540224696336853880224807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6053632928449138506966409 4540224696336853880224807)
    ·
      refine ⟨6810337044505280820337211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4540224696336853880224807 6810337044505280820337211)
      ·
        refine ⟨10215505566757921230505817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6810337044505280820337211 10215505566757921230505817)
        ·
          refine ⟨7661629175068440922879363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10215505566757921230505817 7661629175068440922879363)
          ·
            refine ⟨11492443762602661384319045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7661629175068440922879363 11492443762602661384319045)
            ·
              refine ⟨2154833205487999009559821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11492443762602661384319045 2154833205487999009559821)
              ·
                refine ⟨808062452057999628584933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2154833205487999009559821 808062452057999628584933)
                ·
                  refine ⟨151511709760874930359675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 808062452057999628584933 151511709760874930359675)
                  ·
                    rfl

theorem cell22_1327806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_1327806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327806 prefixEnd_1327806 := by exact prefixLift 1327806
  have htrace : WordTrace (prefixWord ++ tailWord_1327806) baseStart_1327806 baseEnd_1327806 := by
    simpa [prefixWord, tailWord_1327806, baseEnd_1327806] using wordTrace_append hprefix tailTrace_1327806
  have hstable : (prefixWord ++ tailWord_1327806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327806).length < 2 ^ (prefixWord ++ tailWord_1327806).sum := by decide
  have hdescent : baseEnd_1327806 < baseStart_1327806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327849 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 3, 3]
def baseStart_1327849 : Nat := 118140960795 + 1327849 * 2 ^ 59
def prefixEnd_1327849 : Nat := 4983230072969 + 3 ^ 40 * 1327849 * 2
def baseEnd_1327849 : Nat := 454549849061387012253893

theorem tailTrace_1327849 : CollatzResearch.WordTrace tailWord_1327849 prefixEnd_1327849 454549849061387012253893 := by
  unfold tailWord_1327849
  simp only [CollatzResearch.WordTrace]
  refine ⟨48430631766437326399546601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32287087844291550933031067 48430631766437326399546601)
  ·
    refine ⟨36322973824827994799659951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48430631766437326399546601 36322973824827994799659951)
    ·
      refine ⟨54484460737241992199489927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36322973824827994799659951 54484460737241992199489927)
      ·
        refine ⟨81726691105862988299234891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54484460737241992199489927 81726691105862988299234891)
        ·
          refine ⟨122590036658794482448852337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81726691105862988299234891 122590036658794482448852337)
          ·
            refine ⟨91942527494095861836639253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122590036658794482448852337 91942527494095861836639253)
            ·
              refine ⟨4309805976285743523592465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91942527494095861836639253 4309805976285743523592465)
              ·
                refine ⟨3232354482214307642694349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4309805976285743523592465 3232354482214307642694349)
                ·
                  refine ⟨1212132930830365366010381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3232354482214307642694349 1212132930830365366010381)
                  ·
                    refine ⟨454549849061387012253893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1212132930830365366010381 454549849061387012253893)
                    ·
                      rfl

theorem cell22_1327849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 3].length) (baseStart_1327849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327849 prefixEnd_1327849 := by exact prefixLift 1327849
  have htrace : WordTrace (prefixWord ++ tailWord_1327849) baseStart_1327849 baseEnd_1327849 := by
    simpa [prefixWord, tailWord_1327849, baseEnd_1327849] using wordTrace_append hprefix tailTrace_1327849
  have hstable : (prefixWord ++ tailWord_1327849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327849).length < 2 ^ (prefixWord ++ tailWord_1327849).sum := by decide
  have hdescent : baseEnd_1327849 < baseStart_1327849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327877 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_1327877 : Nat := 118140960795 + 1327877 * 2 ^ 59
def prefixEnd_1327877 : Nat := 4983230072969 + 3 ^ 40 * 1327877 * 2
def baseEnd_1327877 : Nat := 454559434033604272553807

theorem tailTrace_1327877 : CollatzResearch.WordTrace tailWord_1327877 prefixEnd_1327877 454559434033604272553807 := by
  unfold tailWord_1327877
  simp only [CollatzResearch.WordTrace]
  refine ⟨48431653010335887181565885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32287768673557258121043923 48431653010335887181565885)
  ·
    refine ⟨18161869878875957693087207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48431653010335887181565885 18161869878875957693087207)
    ·
      refine ⟨27242804818313936539630811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18161869878875957693087207 27242804818313936539630811)
      ·
        refine ⟨40864207227470904809446217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27242804818313936539630811 40864207227470904809446217)
        ·
          refine ⟨30648155420603178607084663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40864207227470904809446217 30648155420603178607084663)
          ·
            refine ⟨45972233130904767910626995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30648155420603178607084663 45972233130904767910626995)
            ·
              refine ⟨68958349696357151865940493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45972233130904767910626995 68958349696357151865940493)
              ·
                refine ⟨25859381136133931949727685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68958349696357151865940493 25859381136133931949727685)
                ·
                  refine ⟨4848633963025112240573941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25859381136133931949727685 4848633963025112240573941)
                  ·
                    refine ⟨454559434033604272553807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4848633963025112240573941 454559434033604272553807)
                    ·
                      rfl

theorem cell22_1327877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_1327877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327877 prefixEnd_1327877 := by exact prefixLift 1327877
  have htrace : WordTrace (prefixWord ++ tailWord_1327877) baseStart_1327877 baseEnd_1327877 := by
    simpa [prefixWord, tailWord_1327877, baseEnd_1327877] using wordTrace_append hprefix tailTrace_1327877
  have hstable : (prefixWord ++ tailWord_1327877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327877).length < 2 ^ (prefixWord ++ tailWord_1327877).sum := by decide
  have hdescent : baseEnd_1327877 < baseStart_1327877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327879 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 7]
def baseStart_1327879 : Nat := 118140960795 + 1327879 * 2 ^ 59
def prefixEnd_1327879 : Nat := 4983230072969 + 3 ^ 40 * 1327879 * 2
def baseEnd_1327879 : Nat := 151520039558158978001267

theorem tailTrace_1327879 : CollatzResearch.WordTrace tailWord_1327879 prefixEnd_1327879 151520039558158978001267 := by
  unfold tailWord_1327879
  simp only [CollatzResearch.WordTrace]
  refine ⟨48431725956328641523138691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32287817304219094348759127 48431725956328641523138691)
  ·
    refine ⟨72647588934492962284708037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48431725956328641523138691 72647588934492962284708037)
    ·
      refine ⟨13621422925217430428382757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72647588934492962284708037 13621422925217430428382757)
      ·
        refine ⟨2554016798478268205321767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13621422925217430428382757 2554016798478268205321767)
        ·
          refine ⟨3831025197717402307982651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2554016798478268205321767 3831025197717402307982651)
          ·
            refine ⟨5746537796576103461973977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831025197717402307982651 5746537796576103461973977)
            ·
              refine ⟨4309903347432077596480483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5746537796576103461973977 4309903347432077596480483)
              ·
                refine ⟨6464855021148116394720725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4309903347432077596480483 6464855021148116394720725)
                ·
                  refine ⟨151520039558158978001267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6464855021148116394720725 151520039558158978001267)
                  ·
                    rfl

theorem cell22_1327879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 7].length) (baseStart_1327879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327879 prefixEnd_1327879 := by exact prefixLift 1327879
  have htrace : WordTrace (prefixWord ++ tailWord_1327879) baseStart_1327879 baseEnd_1327879 := by
    simpa [prefixWord, tailWord_1327879, baseEnd_1327879] using wordTrace_append hprefix tailTrace_1327879
  have hstable : (prefixWord ++ tailWord_1327879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327879).length < 2 ^ (prefixWord ++ tailWord_1327879).sum := by decide
  have hdescent : baseEnd_1327879 < baseStart_1327879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327907 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 8]
def baseStart_1327907 : Nat := 118140960795 + 1327907 * 2 ^ 59
def prefixEnd_1327907 : Nat := 4983230072969 + 3 ^ 40 * 1327907 * 2
def baseEnd_1327907 : Nat := 151523234548898064767905

theorem tailTrace_1327907 : CollatzResearch.WordTrace tailWord_1327907 prefixEnd_1327907 151523234548898064767905 := by
  unfold tailWord_1327907
  simp only [CollatzResearch.WordTrace]
  refine ⟨48432747200227202305157975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32288498133484801536771983 48432747200227202305157975)
  ·
    refine ⟨72649120800340803457736963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48432747200227202305157975 72649120800340803457736963)
    ·
      refine ⟨108973681200511205186605445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72649120800340803457736963 108973681200511205186605445)
      ·
        refine ⟨20432565225095850972488521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108973681200511205186605445 20432565225095850972488521)
        ·
          refine ⟨15324423918821888229366391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20432565225095850972488521 15324423918821888229366391)
          ·
            refine ⟨22986635878232832344049587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15324423918821888229366391 22986635878232832344049587)
            ·
              refine ⟨34479953817349248516074381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22986635878232832344049587 34479953817349248516074381)
              ·
                refine ⟨12929982681505968193527893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34479953817349248516074381 12929982681505968193527893)
                ·
                  refine ⟨151523234548898064767905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12929982681505968193527893 151523234548898064767905)
                  ·
                    rfl

theorem cell22_1327907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 8].length) (baseStart_1327907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327907 prefixEnd_1327907 := by exact prefixLift 1327907
  have htrace : WordTrace (prefixWord ++ tailWord_1327907) baseStart_1327907 baseEnd_1327907 := by
    simpa [prefixWord, tailWord_1327907, baseEnd_1327907] using wordTrace_append hprefix tailTrace_1327907
  have hstable : (prefixWord ++ tailWord_1327907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327907).length < 2 ^ (prefixWord ++ tailWord_1327907).sum := by decide
  have hdescent : baseEnd_1327907 < baseStart_1327907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327909 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_1327909 : Nat := 118140960795 + 1327909 * 2 ^ 59
def prefixEnd_1327909 : Nat := 4983230072969 + 3 ^ 40 * 1327909 * 2
def baseEnd_1327909 : Nat := 454570388287566855753709

theorem tailTrace_1327909 : CollatzResearch.WordTrace tailWord_1327909 prefixEnd_1327909 454570388287566855753709 := by
  unfold tailWord_1327909
  simp only [CollatzResearch.WordTrace]
  refine ⟨48432820146219956646730781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32288546764146637764487187 48432820146219956646730781)
  ·
    refine ⟨18162307554832483742524043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48432820146219956646730781 18162307554832483742524043)
    ·
      refine ⟨27243461332248725613786065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18162307554832483742524043 27243461332248725613786065)
      ·
        refine ⟨20432595999186544210339549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27243461332248725613786065 20432595999186544210339549)
        ·
          refine ⟨7662223499694954078877331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20432595999186544210339549 7662223499694954078877331)
          ·
            refine ⟨11493335249542431118315997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7662223499694954078877331 11493335249542431118315997)
            ·
              refine ⟨4310000718578411669368499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11493335249542431118315997 4310000718578411669368499)
              ·
                refine ⟨6465001077867617504052749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4310000718578411669368499 6465001077867617504052749)
                ·
                  refine ⟨2424375404200356564019781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6465001077867617504052749 2424375404200356564019781)
                  ·
                    refine ⟨454570388287566855753709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2424375404200356564019781 454570388287566855753709)
                    ·
                      rfl

theorem cell22_1327909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_1327909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327909 prefixEnd_1327909 := by exact prefixLift 1327909
  have htrace : WordTrace (prefixWord ++ tailWord_1327909) baseStart_1327909 baseEnd_1327909 := by
    simpa [prefixWord, tailWord_1327909, baseEnd_1327909] using wordTrace_append hprefix tailTrace_1327909
  have hstable : (prefixWord ++ tailWord_1327909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327909).length < 2 ^ (prefixWord ++ tailWord_1327909).sum := by decide
  have hdescent : baseEnd_1327909 < baseStart_1327909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327934 : List Nat := [4, 2, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_1327934 : Nat := 118140960795 + 1327934 * 2 ^ 59
def prefixEnd_1327934 : Nat := 4983230072969 + 3 ^ 40 * 1327934 * 2
def baseEnd_1327934 : Nat := 454578946298475123878633

theorem tailTrace_1327934 : CollatzResearch.WordTrace tailWord_1327934 prefixEnd_1327934 454578946298475123878633 := by
  unfold tailWord_1327934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6054216496391173239548857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32289154647419590610927237 6054216496391173239548857)
  ·
    refine ⟨4540662372293379929661643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6054216496391173239548857 4540662372293379929661643)
    ·
      refine ⟨6810993558440069894492465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4540662372293379929661643 6810993558440069894492465)
      ·
        refine ⟨5108245168830052420869349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6810993558440069894492465 5108245168830052420869349)
        ·
          refine ⟨957795969155634828913003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5108245168830052420869349 957795969155634828913003)
          ·
            refine ⟨1436693953733452243369505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957795969155634828913003 1436693953733452243369505)
            ·
              refine ⟨1077520465300089182527129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1436693953733452243369505 1077520465300089182527129)
              ·
                refine ⟨808140348975066886895347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077520465300089182527129 808140348975066886895347)
                ·
                  refine ⟨1212210523462600330343021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808140348975066886895347 1212210523462600330343021)
                  ·
                    refine ⟨454578946298475123878633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1212210523462600330343021 454578946298475123878633)
                    ·
                      rfl

theorem cell22_1327934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_1327934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327934 prefixEnd_1327934 := by exact prefixLift 1327934
  have htrace : WordTrace (prefixWord ++ tailWord_1327934) baseStart_1327934 baseEnd_1327934 := by
    simpa [prefixWord, tailWord_1327934, baseEnd_1327934] using wordTrace_append hprefix tailTrace_1327934
  have hstable : (prefixWord ++ tailWord_1327934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327934).length < 2 ^ (prefixWord ++ tailWord_1327934).sum := by decide
  have hdescent : baseEnd_1327934 < baseStart_1327934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327954 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1327954 : Nat := 118140960795 + 1327954 * 2 ^ 59
def prefixEnd_1327954 : Nat := 4983230072969 + 3 ^ 40 * 1327954 * 2
def baseEnd_1327954 : Nat := 454585792707201738378571

theorem tailTrace_1327954 : CollatzResearch.WordTrace tailWord_1327954 prefixEnd_1327954 454585792707201738378571 := by
  unfold tailWord_1327954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12108615357764232333029729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32289640954037952888079277 12108615357764232333029729)
  ·
    refine ⟨9081461518323174249772297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12108615357764232333029729 9081461518323174249772297)
    ·
      refine ⟨6811096138742380687329223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9081461518323174249772297 6811096138742380687329223)
      ·
        refine ⟨10216644208113571030993835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6811096138742380687329223 10216644208113571030993835)
        ·
          refine ⟨15324966312170356546490753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10216644208113571030993835 15324966312170356546490753)
          ·
            refine ⟨11493724734127767409868065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15324966312170356546490753 11493724734127767409868065)
            ·
              refine ⟨8620293550595825557401049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11493724734127767409868065 8620293550595825557401049)
              ·
                refine ⟨6465220162946869168050787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8620293550595825557401049 6465220162946869168050787)
                ·
                  refine ⟨9697830244420303752076181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6465220162946869168050787 9697830244420303752076181)
                  ·
                    refine ⟨454585792707201738378571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9697830244420303752076181 454585792707201738378571)
                    ·
                      rfl

theorem cell22_1327954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1327954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327954 prefixEnd_1327954 := by exact prefixLift 1327954
  have htrace : WordTrace (prefixWord ++ tailWord_1327954) baseStart_1327954 baseEnd_1327954 := by
    simpa [prefixWord, tailWord_1327954, baseEnd_1327954] using wordTrace_append hprefix tailTrace_1327954
  have hstable : (prefixWord ++ tailWord_1327954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327954).length < 2 ^ (prefixWord ++ tailWord_1327954).sum := by decide
  have hdescent : baseEnd_1327954 < baseStart_1327954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327971 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 2, 4]
def baseStart_1327971 : Nat := 118140960795 + 1327971 * 2 ^ 59
def prefixEnd_1327971 : Nat := 4983230072969 + 3 ^ 40 * 1327971 * 2
def baseEnd_1327971 : Nat := 454591612154619360703519

theorem tailTrace_1327971 : CollatzResearch.WordTrace tailWord_1327971 prefixEnd_1327971 454591612154619360703519 := by
  unfold tailWord_1327971
  simp only [CollatzResearch.WordTrace]
  refine ⟨48435081471995341235487767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32290054314663560823658511 48435081471995341235487767)
  ·
    refine ⟨72652622207993011853231651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48435081471995341235487767 72652622207993011853231651)
    ·
      refine ⟨108978933311989517779847477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72652622207993011853231651 108978933311989517779847477)
      ·
        refine ⟨10216774997999017291860701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108978933311989517779847477 10216774997999017291860701)
        ·
          refine ⟨3831290624249631484447763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10216774997999017291860701 3831290624249631484447763)
          ·
            refine ⟨5746935936374447226671645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831290624249631484447763 5746935936374447226671645)
            ·
              refine ⟨2155100976140417710001867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5746935936374447226671645 2155100976140417710001867)
              ·
                refine ⟨3232651464210626565002801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155100976140417710001867 3232651464210626565002801)
                ·
                  refine ⟨2424488598157969923752101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3232651464210626565002801 2424488598157969923752101)
                  ·
                    refine ⟨454591612154619360703519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2424488598157969923752101 454591612154619360703519)
                    ·
                      rfl

theorem cell22_1327971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 4].length) (baseStart_1327971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327971 prefixEnd_1327971 := by exact prefixLift 1327971
  have htrace : WordTrace (prefixWord ++ tailWord_1327971) baseStart_1327971 baseEnd_1327971 := by
    simpa [prefixWord, tailWord_1327971, baseEnd_1327971] using wordTrace_append hprefix tailTrace_1327971
  have hstable : (prefixWord ++ tailWord_1327971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327971).length < 2 ^ (prefixWord ++ tailWord_1327971).sum := by decide
  have hdescent : baseEnd_1327971 < baseStart_1327971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327990 : List Nat := [5, 1, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_1327990 : Nat := 118140960795 + 1327990 * 2 ^ 59
def prefixEnd_1327990 : Nat := 4983230072969 + 3 ^ 40 * 1327990 * 2
def baseEnd_1327990 : Nat := 454598116242909644478461

theorem tailTrace_1327990 : CollatzResearch.WordTrace tailWord_1327990 prefixEnd_1327990 454598116242909644478461 := by
  unfold tailWord_1327990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3027235903682906717526839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32290516305951004986952949 3027235903682906717526839)
  ·
    refine ⟨4540853855524360076290259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3027235903682906717526839 4540853855524360076290259)
    ·
      refine ⟨6811280783286540114435389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4540853855524360076290259 6811280783286540114435389)
      ·
        refine ⟨2554230293732452542913271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6811280783286540114435389 2554230293732452542913271)
        ·
          refine ⟨3831345440598678814369907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2554230293732452542913271 3831345440598678814369907)
          ·
            refine ⟨5747018160898018221554861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831345440598678814369907 5747018160898018221554861)
            ·
              refine ⟨2155131810336756833083073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5747018160898018221554861 2155131810336756833083073)
              ·
                refine ⟨1616348857752567624812305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2155131810336756833083073 1616348857752567624812305)
                ·
                  refine ⟨1212261643314425718609229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1616348857752567624812305 1212261643314425718609229)
                  ·
                    refine ⟨454598116242909644478461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1212261643314425718609229 454598116242909644478461)
                    ·
                      rfl

theorem cell22_1327990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_1327990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1327990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1327990 prefixEnd_1327990 := by exact prefixLift 1327990
  have htrace : WordTrace (prefixWord ++ tailWord_1327990) baseStart_1327990 baseEnd_1327990 := by
    simpa [prefixWord, tailWord_1327990, baseEnd_1327990] using wordTrace_append hprefix tailTrace_1327990
  have hstable : (prefixWord ++ tailWord_1327990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327990).length < 2 ^ (prefixWord ++ tailWord_1327990).sum := by decide
  have hdescent : baseEnd_1327990 < baseStart_1327990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328052 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1328052 : Nat := 118140960795 + 1328052 * 2 ^ 59
def prefixEnd_1328052 : Nat := 4983230072969 + 3 ^ 40 * 1328052 * 2
def baseEnd_1328052 : Nat := 454619340109962149428271

theorem tailTrace_1328052 : CollatzResearch.WordTrace tailWord_1328052 prefixEnd_1328052 454619340109962149428271 := by
  unfold tailWord_1328052
  simp only [CollatzResearch.WordTrace]
  refine ⟨24219017892350946034593205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32292023856467928046124273 24219017892350946034593205)
  ·
    refine ⟨2270532927407901190743113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24219017892350946034593205 2270532927407901190743113)
    ·
      refine ⟨1702899695555925893057335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2270532927407901190743113 1702899695555925893057335)
      ·
        refine ⟨2554349543333888839586003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1702899695555925893057335 2554349543333888839586003)
        ·
          refine ⟨3831524315000833259379005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2554349543333888839586003 3831524315000833259379005)
          ·
            refine ⟨1436821618125312472267127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3831524315000833259379005 1436821618125312472267127)
            ·
              refine ⟨2155232427187968708400691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436821618125312472267127 2155232427187968708400691)
              ·
                refine ⟨3232848640781953062601037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155232427187968708400691 3232848640781953062601037)
                ·
                  refine ⟨1212318240293232398475389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3232848640781953062601037 1212318240293232398475389)
                  ·
                    refine ⟨454619340109962149428271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1212318240293232398475389 454619340109962149428271)
                    ·
                      rfl

theorem cell22_1328052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1328052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328052 prefixEnd_1328052 := by exact prefixLift 1328052
  have htrace : WordTrace (prefixWord ++ tailWord_1328052) baseStart_1328052 baseEnd_1328052 := by
    simpa [prefixWord, tailWord_1328052, baseEnd_1328052] using wordTrace_append hprefix tailTrace_1328052
  have hstable : (prefixWord ++ tailWord_1328052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328052).length < 2 ^ (prefixWord ++ tailWord_1328052).sum := by decide
  have hdescent : baseEnd_1328052 < baseStart_1328052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328078 : List Nat := [4, 1, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_1328078 : Nat := 118140960795 + 1328078 * 2 ^ 59
def prefixEnd_1328078 : Nat := 4983230072969 + 3 ^ 40 * 1328078 * 2
def baseEnd_1328078 : Nat := 454628240441306748278191

theorem tailTrace_1328078 : CollatzResearch.WordTrace tailWord_1328078 prefixEnd_1328078 454628240441306748278191 := by
  unfold tailWord_1328078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6054873010325962313704111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32292656055071799006421925 6054873010325962313704111)
  ·
    refine ⟨9082309515488943470556167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6054873010325962313704111 9082309515488943470556167)
    ·
      refine ⟨13623464273233415205834251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9082309515488943470556167 13623464273233415205834251)
      ·
        refine ⟨20435196409850122808751377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13623464273233415205834251 20435196409850122808751377)
        ·
          refine ⟨15326397307387592106563533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20435196409850122808751377 15326397307387592106563533)
          ·
            refine ⟨5747398990270347039961325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15326397307387592106563533 5747398990270347039961325)
            ·
              refine ⟨2155274621351380139985497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5747398990270347039961325 2155274621351380139985497)
              ·
                refine ⟨1616455966013535104989123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2155274621351380139985497 1616455966013535104989123)
                ·
                  refine ⟨2424683949020302657483685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616455966013535104989123 2424683949020302657483685)
                  ·
                    refine ⟨454628240441306748278191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2424683949020302657483685 454628240441306748278191)
                    ·
                      rfl

theorem cell22_1328078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_1328078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328078 prefixEnd_1328078 := by exact prefixLift 1328078
  have htrace : WordTrace (prefixWord ++ tailWord_1328078) baseStart_1328078 baseEnd_1328078 := by
    simpa [prefixWord, tailWord_1328078, baseEnd_1328078] using wordTrace_append hprefix tailTrace_1328078
  have hstable : (prefixWord ++ tailWord_1328078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328078).length < 2 ^ (prefixWord ++ tailWord_1328078).sum := by decide
  have hdescent : baseEnd_1328078 < baseStart_1328078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328095 : List Nat := [1, 1, 2, 3, 5, 1, 3, 1, 1, 4]
def baseStart_1328095 : Nat := 118140960795 + 1328095 * 2 ^ 59
def prefixEnd_1328095 : Nat := 4983230072969 + 3 ^ 40 * 1328095 * 2
def baseEnd_1328095 : Nat := 454634059888724370603139

theorem tailTrace_1328095 : CollatzResearch.WordTrace tailWord_1328095 prefixEnd_1328095 454634059888724370603139 := by
  unfold tailWord_1328095
  simp only [CollatzResearch.WordTrace]
  refine ⟨48439604123546110413001739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32293069415697406942001159 48439604123546110413001739)
  ·
    refine ⟨72659406185319165619502609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48439604123546110413001739 72659406185319165619502609)
    ·
      refine ⟨54494554638989374214626957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72659406185319165619502609 54494554638989374214626957)
      ·
        refine ⟨20435457989621015330485109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54494554638989374214626957 20435457989621015330485109)
        ·
          refine ⟨1915824186526970187232979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20435457989621015330485109 1915824186526970187232979)
          ·
            refine ⟨2873736279790455280849469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915824186526970187232979 2873736279790455280849469)
            ·
              refine ⟨1077651104921420730318551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2873736279790455280849469 1077651104921420730318551)
              ·
                refine ⟨1616476657382131095477827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077651104921420730318551 1616476657382131095477827)
                ·
                  refine ⟨2424714986073196643216741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616476657382131095477827 2424714986073196643216741)
                  ·
                    refine ⟨454634059888724370603139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2424714986073196643216741 454634059888724370603139)
                    ·
                      rfl

theorem cell22_1328095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 1, 4].length) (baseStart_1328095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328095 prefixEnd_1328095 := by exact prefixLift 1328095
  have htrace : WordTrace (prefixWord ++ tailWord_1328095) baseStart_1328095 baseEnd_1328095 := by
    simpa [prefixWord, tailWord_1328095, baseEnd_1328095] using wordTrace_append hprefix tailTrace_1328095
  have hstable : (prefixWord ++ tailWord_1328095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328095).length < 2 ^ (prefixWord ++ tailWord_1328095).sum := by decide
  have hdescent : baseEnd_1328095 < baseStart_1328095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328110 : List Nat := [4, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_1328110 : Nat := 118140960795 + 1328110 * 2 ^ 59
def prefixEnd_1328110 : Nat := 4983230072969 + 3 ^ 40 * 1328110 * 2
def baseEnd_1328110 : Nat := 151546398231756443826031

theorem tailTrace_1328110 : CollatzResearch.WordTrace tailWord_1328110 prefixEnd_1328110 151546398231756443826031 := by
  unfold tailWord_1328110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6055018902311470996849723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32293434145661178649865189 6055018902311470996849723)
  ·
    refine ⟨9082528353467206495274585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6055018902311470996849723 9082528353467206495274585)
    ·
      refine ⟨6811896265100404871455939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9082528353467206495274585 6811896265100404871455939)
      ·
        refine ⟨10217844397650607307183909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6811896265100404871455939 10217844397650607307183909)
        ·
          refine ⟨1915845824559488870096983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10217844397650607307183909 1915845824559488870096983)
          ·
            refine ⟨2873768736839233305145475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915845824559488870096983 2873768736839233305145475)
            ·
              refine ⟨4310653105258849957718213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873768736839233305145475 4310653105258849957718213)
              ·
                refine ⟨808247457236034367072165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4310653105258849957718213 808247457236034367072165)
                ·
                  refine ⟨151546398231756443826031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 808247457236034367072165 151546398231756443826031)
                  ·
                    rfl

theorem cell22_1328110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_1328110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328110 prefixEnd_1328110 := by exact prefixLift 1328110
  have htrace : WordTrace (prefixWord ++ tailWord_1328110) baseStart_1328110 baseEnd_1328110 := by
    simpa [prefixWord, tailWord_1328110, baseEnd_1328110] using wordTrace_append hprefix tailTrace_1328110
  have hstable : (prefixWord ++ tailWord_1328110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328110).length < 2 ^ (prefixWord ++ tailWord_1328110).sum := by decide
  have hdescent : baseEnd_1328110 < baseStart_1328110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328138 : List Nat := [3, 1, 2, 2, 3, 2, 3, 6]
def baseStart_1328138 : Nat := 118140960795 + 1328138 * 2 ^ 59
def prefixEnd_1328138 : Nat := 4983230072969 + 3 ^ 40 * 1328138 * 2
def baseEnd_1328138 : Nat := 50516531074165176864223

theorem tailTrace_1328138 : CollatzResearch.WordTrace tailWord_1328138 prefixEnd_1328138 50516531074165176864223 := by
  unfold tailWord_1328138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12110293115597582189204267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32294114974926885837878045 12110293115597582189204267)
  ·
    refine ⟨18165439673396373283806401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12110293115597582189204267 18165439673396373283806401)
    ·
      refine ⟨13624079755047279962854801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18165439673396373283806401 13624079755047279962854801)
      ·
        refine ⟨10218059816285459972141101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13624079755047279962854801 10218059816285459972141101)
        ·
          refine ⟨3831772431107047489552913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10218059816285459972141101 3831772431107047489552913)
          ·
            refine ⟨2873829323330285617164685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3831772431107047489552913 2873829323330285617164685)
            ·
              refine ⟨1077685996248857106436757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2873829323330285617164685 1077685996248857106436757)
              ·
                refine ⟨50516531074165176864223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1077685996248857106436757 50516531074165176864223)
                ·
                  rfl

theorem cell22_1328138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_1328138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328138 prefixEnd_1328138 := by exact prefixLift 1328138
  have htrace : WordTrace (prefixWord ++ tailWord_1328138) baseStart_1328138 baseEnd_1328138 := by
    simpa [prefixWord, tailWord_1328138, baseEnd_1328138] using wordTrace_append hprefix tailTrace_1328138
  have hstable : (prefixWord ++ tailWord_1328138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328138).length < 2 ^ (prefixWord ++ tailWord_1328138).sum := by decide
  have hdescent : baseEnd_1328138 < baseStart_1328138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328146 : List Nat := [3, 2, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1328146 : Nat := 118140960795 + 1328146 * 2 ^ 59
def prefixEnd_1328146 : Nat := 4983230072969 + 3 ^ 40 * 1328146 * 2
def baseEnd_1328146 : Nat := 454651518230977237577983

theorem tailTrace_1328146 : CollatzResearch.WordTrace tailWord_1328146 prefixEnd_1328146 454651518230977237577983 := by
  unfold tailWord_1328146
  simp only [CollatzResearch.WordTrace]
  refine ⟨12110366061590336530777073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32294309497574230748738861 12110366061590336530777073)
  ·
    refine ⟨9082774546192752398082805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12110366061590336530777073 9082774546192752398082805)
    ·
      refine ⟨851510113705570537320263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9082774546192752398082805 851510113705570537320263)
      ·
        refine ⟨1277265170558355805980395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851510113705570537320263 1277265170558355805980395)
        ·
          refine ⟨1915897755837533708970593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1277265170558355805980395 1915897755837533708970593)
          ·
            refine ⟨1436923316878150281727945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1915897755837533708970593 1436923316878150281727945)
            ·
              refine ⟨1077692487658612711295959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1436923316878150281727945 1077692487658612711295959)
              ·
                refine ⟨1616538731487919066943939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077692487658612711295959 1616538731487919066943939)
                ·
                  refine ⟨2424808097231878600415909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616538731487919066943939 2424808097231878600415909)
                  ·
                    refine ⟨454651518230977237577983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2424808097231878600415909 454651518230977237577983)
                    ·
                      rfl

theorem cell22_1328146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1328146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328146 prefixEnd_1328146 := by exact prefixLift 1328146
  have htrace : WordTrace (prefixWord ++ tailWord_1328146) baseStart_1328146 baseEnd_1328146 := by
    simpa [prefixWord, tailWord_1328146, baseEnd_1328146] using wordTrace_append hprefix tailTrace_1328146
  have hstable : (prefixWord ++ tailWord_1328146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328146).length < 2 ^ (prefixWord ++ tailWord_1328146).sum := by decide
  have hdescent : baseEnd_1328146 < baseStart_1328146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328213 : List Nat := [1, 3, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_1328213 : Nat := 118140960795 + 1328213 * 2 ^ 59
def prefixEnd_1328213 : Nat := 4983230072969 + 3 ^ 40 * 1328213 * 2
def baseEnd_1328213 : Nat := 454674453700211396152777

theorem tailTrace_1328213 : CollatzResearch.WordTrace tailWord_1328213 prefixEnd_1328213 454674453700211396152777 := by
  unfold tailWord_1328213
  simp only [CollatzResearch.WordTrace]
  refine ⟨48443907937118616565797293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32295938624745744377198195 48443907937118616565797293)
  ·
    refine ⟨18166465476419481212173985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48443907937118616565797293 18166465476419481212173985)
    ·
      refine ⟨13624849107314610909130489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18166465476419481212173985 13624849107314610909130489)
      ·
        refine ⟨10218636830485958181847867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13624849107314610909130489 10218636830485958181847867)
        ·
          refine ⟨15327955245728937272771801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10218636830485958181847867 15327955245728937272771801)
          ·
            refine ⟨11495966434296702954578851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15327955245728937272771801 11495966434296702954578851)
            ·
              refine ⟨17243949651445054431868277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11495966434296702954578851 17243949651445054431868277)
              ·
                refine ⟨1616620279822973852987651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17243949651445054431868277 1616620279822973852987651)
                ·
                  refine ⟨2424930419734460779481477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616620279822973852987651 2424930419734460779481477)
                  ·
                    refine ⟨454674453700211396152777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2424930419734460779481477 454674453700211396152777)
                    ·
                      rfl

theorem cell22_1328213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_1328213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328213 prefixEnd_1328213 := by exact prefixLift 1328213
  have htrace : WordTrace (prefixWord ++ tailWord_1328213) baseStart_1328213 baseEnd_1328213 := by
    simpa [prefixWord, tailWord_1328213, baseEnd_1328213] using wordTrace_append hprefix tailTrace_1328213
  have hstable : (prefixWord ++ tailWord_1328213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328213).length < 2 ^ (prefixWord ++ tailWord_1328213).sum := by decide
  have hdescent : baseEnd_1328213 < baseStart_1328213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328221 : List Nat := [1, 4, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1328221 : Nat := 118140960795 + 1328221 * 2 ^ 59
def prefixEnd_1328221 : Nat := 4983230072969 + 3 ^ 40 * 1328221 * 2
def baseEnd_1328221 : Nat := 454677192263702041952753

theorem tailTrace_1328221 : CollatzResearch.WordTrace tailWord_1328221 prefixEnd_1328221 454677192263702041952753 := by
  unfold tailWord_1328221
  simp only [CollatzResearch.WordTrace]
  refine ⟨48444199721089633932088517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32296133147393089288059011 48444199721089633932088517)
  ·
    refine ⟨9083287447704306362266597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48444199721089633932088517 9083287447704306362266597)
    ·
      refine ⟨1703116396444557442924987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9083287447704306362266597 1703116396444557442924987)
      ·
        refine ⟨2554674594666836164387481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1703116396444557442924987 2554674594666836164387481)
        ·
          refine ⟨1916005946000127123290611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2554674594666836164387481 1916005946000127123290611)
          ·
            refine ⟨2874008919000190684935917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916005946000127123290611 2874008919000190684935917)
            ·
              refine ⟨1077753344625071506850969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2874008919000190684935917 1077753344625071506850969)
              ·
                refine ⟨808315008468803630138227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077753344625071506850969 808315008468803630138227)
                ·
                  refine ⟨1212472512703205445207341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808315008468803630138227 1212472512703205445207341)
                  ·
                    refine ⟨454677192263702041952753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1212472512703205445207341 454677192263702041952753)
                    ·
                      rfl

theorem cell22_1328221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1328221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328221 prefixEnd_1328221 := by exact prefixLift 1328221
  have htrace : WordTrace (prefixWord ++ tailWord_1328221) baseStart_1328221 baseEnd_1328221 := by
    simpa [prefixWord, tailWord_1328221, baseEnd_1328221] using wordTrace_append hprefix tailTrace_1328221
  have hstable : (prefixWord ++ tailWord_1328221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328221).length < 2 ^ (prefixWord ++ tailWord_1328221).sum := by decide
  have hdescent : baseEnd_1328221 < baseStart_1328221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328241 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 1, 6]
def baseStart_1328241 : Nat := 118140960795 + 1328241 * 2 ^ 59
def prefixEnd_1328241 : Nat := 4983230072969 + 3 ^ 40 * 1328241 * 2
def baseEnd_1328241 : Nat := 454684038672428656452691

theorem tailTrace_1328241 : CollatzResearch.WordTrace tailWord_1328241 prefixEnd_1328241 454684038672428656452691 := by
  unfold tailWord_1328241
  simp only [CollatzResearch.WordTrace]
  refine ⟨48444929181017177347816577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32296619454011451565211051 48444929181017177347816577)
  ·
    refine ⟨36333696885762883010862433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48444929181017177347816577 36333696885762883010862433)
    ·
      refine ⟨27250272664322162258146825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36333696885762883010862433 27250272664322162258146825)
      ·
        refine ⟨20437704498241621693610119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27250272664322162258146825 20437704498241621693610119)
        ·
          refine ⟨30656556747362432540415179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20437704498241621693610119 30656556747362432540415179)
          ·
            refine ⟨45984835121043648810622769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30656556747362432540415179 45984835121043648810622769)
            ·
              refine ⟨34488626340782736607967077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45984835121043648810622769 34488626340782736607967077)
              ·
                refine ⟨6466617438896763113993827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34488626340782736607967077 6466617438896763113993827)
                ·
                  refine ⟨9699926158345144670990741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6466617438896763113993827 9699926158345144670990741)
                  ·
                    refine ⟨454684038672428656452691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9699926158345144670990741 454684038672428656452691)
                    ·
                      rfl

theorem cell22_1328241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_1328241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328241 prefixEnd_1328241 := by exact prefixLift 1328241
  have htrace : WordTrace (prefixWord ++ tailWord_1328241) baseStart_1328241 baseEnd_1328241 := by
    simpa [prefixWord, tailWord_1328241, baseEnd_1328241] using wordTrace_append hprefix tailTrace_1328241
  have hstable : (prefixWord ++ tailWord_1328241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328241).length < 2 ^ (prefixWord ++ tailWord_1328241).sum := by decide
  have hdescent : baseEnd_1328241 < baseStart_1328241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328256 : List Nat := [2, 1, 1, 2, 1, 3, 4, 8]
def baseStart_1328256 : Nat := 118140960795 + 1328256 * 2 ^ 59
def prefixEnd_1328256 : Nat := 4983230072969 + 3 ^ 40 * 1328256 * 2
def baseEnd_1328256 : Nat := 50521019275441513036405

theorem tailTrace_1328256 : CollatzResearch.WordTrace tailWord_1328256 prefixEnd_1328256 50521019275441513036405 := by
  unfold tailWord_1328256
  simp only [CollatzResearch.WordTrace]
  refine ⟨24222738137981417454806311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32296984183975223273075081 24222738137981417454806311)
  ·
    refine ⟨36334107206972126182209467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24222738137981417454806311 36334107206972126182209467)
    ·
      refine ⟨54501160810458189273314201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36334107206972126182209467 54501160810458189273314201)
      ·
        refine ⟨40875870607843641954985651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54501160810458189273314201 40875870607843641954985651)
        ·
          refine ⟨61313805911765462932478477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40875870607843641954985651 61313805911765462932478477)
          ·
            refine ⟨22992677216912048599679429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61313805911765462932478477 22992677216912048599679429)
            ·
              refine ⟨4311126978171009112439893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22992677216912048599679429 4311126978171009112439893)
              ·
                refine ⟨50521019275441513036405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4311126978171009112439893 50521019275441513036405)
                ·
                  rfl

theorem cell22_1328256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 8].length) (baseStart_1328256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328256 prefixEnd_1328256 := by exact prefixLift 1328256
  have htrace : WordTrace (prefixWord ++ tailWord_1328256) baseStart_1328256 baseEnd_1328256 := by
    simpa [prefixWord, tailWord_1328256, baseEnd_1328256] using wordTrace_append hprefix tailTrace_1328256
  have hstable : (prefixWord ++ tailWord_1328256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328256).length < 2 ^ (prefixWord ++ tailWord_1328256).sum := by decide
  have hdescent : baseEnd_1328256 < baseStart_1328256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328305 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 5, 3]
def baseStart_1328305 : Nat := 118140960795 + 1328305 * 2 ^ 59
def prefixEnd_1328305 : Nat := 4983230072969 + 3 ^ 40 * 1328305 * 2
def baseEnd_1328305 : Nat := 454705947180353822852495

theorem tailTrace_1328305 : CollatzResearch.WordTrace tailWord_1328305 prefixEnd_1328305 454705947180353822852495 := by
  unfold tailWord_1328305
  simp only [CollatzResearch.WordTrace]
  refine ⟨48447263452785316278146369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32298175635190210852097579 48447263452785316278146369)
  ·
    refine ⟨36335447589588987208609777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48447263452785316278146369 36335447589588987208609777)
    ·
      refine ⟨27251585692191740406457333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36335447589588987208609777 27251585692191740406457333)
      ·
        refine ⟨2554836158642975663105375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27251585692191740406457333 2554836158642975663105375)
        ·
          refine ⟨3832254237964463494658063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2554836158642975663105375 3832254237964463494658063)
          ·
            refine ⟨5748381356946695241987095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832254237964463494658063 5748381356946695241987095)
            ·
              refine ⟨8622572035420042862980643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5748381356946695241987095 8622572035420042862980643)
              ·
                refine ⟨12933858053130064294470965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8622572035420042862980643 12933858053130064294470965)
                ·
                  refine ⟨1212549192480943527606653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12933858053130064294470965 1212549192480943527606653)
                  ·
                    refine ⟨454705947180353822852495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1212549192480943527606653 454705947180353822852495)
                    ·
                      rfl

theorem cell22_1328305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_1328305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328305 prefixEnd_1328305 := by exact prefixLift 1328305
  have htrace : WordTrace (prefixWord ++ tailWord_1328305) baseStart_1328305 baseEnd_1328305 := by
    simpa [prefixWord, tailWord_1328305, baseEnd_1328305] using wordTrace_append hprefix tailTrace_1328305
  have hstable : (prefixWord ++ tailWord_1328305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328305).length < 2 ^ (prefixWord ++ tailWord_1328305).sum := by decide
  have hdescent : baseEnd_1328305 < baseStart_1328305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328363 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 6]
def baseStart_1328363 : Nat := 118140960795 + 1328363 * 2 ^ 59
def prefixEnd_1328363 : Nat := 4983230072969 + 3 ^ 40 * 1328363 * 2
def baseEnd_1328363 : Nat := 151575267255220334967439

theorem tailTrace_1328363 : CollatzResearch.WordTrace tailWord_1328363 prefixEnd_1328363 151575267255220334967439 := by
  unfold tailWord_1328363
  simp only [CollatzResearch.WordTrace]
  refine ⟨48449378886575192183757743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32299585924383461455838495 48449378886575192183757743)
  ·
    refine ⟨72674068329862788275636615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48449378886575192183757743 72674068329862788275636615)
    ·
      refine ⟨109011102494794182413454923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72674068329862788275636615 109011102494794182413454923)
      ·
        refine ⟨163516653742191273620182385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109011102494794182413454923 163516653742191273620182385)
        ·
          refine ⟨122637490306643455215136789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163516653742191273620182385 122637490306643455215136789)
          ·
            refine ⟨5748632358123911963209537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122637490306643455215136789 5748632358123911963209537)
            ·
              refine ⟨4311474268592933972407153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5748632358123911963209537 4311474268592933972407153)
              ·
                refine ⟨3233605701444700479305365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4311474268592933972407153 3233605701444700479305365)
                ·
                  refine ⟨151575267255220334967439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3233605701444700479305365 151575267255220334967439)
                  ·
                    rfl

theorem cell22_1328363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 6].length) (baseStart_1328363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328363 prefixEnd_1328363 := by exact prefixLift 1328363
  have htrace : WordTrace (prefixWord ++ tailWord_1328363) baseStart_1328363 baseEnd_1328363 := by
    simpa [prefixWord, tailWord_1328363, baseEnd_1328363] using wordTrace_append hprefix tailTrace_1328363
  have hstable : (prefixWord ++ tailWord_1328363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328363).length < 2 ^ (prefixWord ++ tailWord_1328363).sum := by decide
  have hdescent : baseEnd_1328363 < baseStart_1328363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328378 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_1328378 : Nat := 118140960795 + 1328378 * 2 ^ 59
def prefixEnd_1328378 : Nat := 4983230072969 + 3 ^ 40 * 1328378 * 2
def baseEnd_1328378 : Nat := 454730936572205965777271

theorem tailTrace_1328378 : CollatzResearch.WordTrace tailWord_1328378 prefixEnd_1328378 454730936572205965777271 := by
  unfold tailWord_1328378
  simp only [CollatzResearch.WordTrace]
  refine ⟨12112481495380212436388447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32299950654347233163702525 12112481495380212436388447)
  ·
    refine ⟨18168722243070318654582671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12112481495380212436388447 18168722243070318654582671)
    ·
      refine ⟨27253083364605477981874007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18168722243070318654582671 27253083364605477981874007)
      ·
        refine ⟨40879625046908216972811011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27253083364605477981874007 40879625046908216972811011)
        ·
          refine ⟨61319437570362325459216517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40879625046908216972811011 61319437570362325459216517)
          ·
            refine ⟨11497394544442936023603097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61319437570362325459216517 11497394544442936023603097)
            ·
              refine ⟨8623045908332202017702323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11497394544442936023603097 8623045908332202017702323)
              ·
                refine ⟨12934568862498303026553485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8623045908332202017702323 12934568862498303026553485)
                ·
                  refine ⟨4850463323436863634957557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12934568862498303026553485 4850463323436863634957557)
                  ·
                    refine ⟨454730936572205965777271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4850463323436863634957557 454730936572205965777271)
                    ·
                      rfl

theorem cell22_1328378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_1328378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328378 prefixEnd_1328378 := by exact prefixLift 1328378
  have htrace : WordTrace (prefixWord ++ tailWord_1328378) baseStart_1328378 baseEnd_1328378 := by
    simpa [prefixWord, tailWord_1328378, baseEnd_1328378] using wordTrace_append hprefix tailTrace_1328378
  have hstable : (prefixWord ++ tailWord_1328378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328378).length < 2 ^ (prefixWord ++ tailWord_1328378).sum := by decide
  have hdescent : baseEnd_1328378 < baseStart_1328378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328382 : List Nat := [4, 2, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1328382 : Nat := 118140960795 + 1328382 * 2 ^ 59
def prefixEnd_1328382 : Nat := 4983230072969 + 3 ^ 40 * 1328382 * 2
def baseEnd_1328382 : Nat := 454732305853951288677259

theorem tailTrace_1328382 : CollatzResearch.WordTrace tailWord_1328382 prefixEnd_1328382 454732305853951288677259 := by
  unfold tailWord_1328382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6056258984188294803587425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32300047915670905619132933 6056258984188294803587425)
  ·
    refine ⟨4542194238141221102690569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6056258984188294803587425 4542194238141221102690569)
    ·
      refine ⟨3406645678605915827017927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4542194238141221102690569 3406645678605915827017927)
      ·
        refine ⟨5109968517908873740526891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3406645678605915827017927 5109968517908873740526891)
        ·
          refine ⟨7664952776863310610790337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5109968517908873740526891 7664952776863310610790337)
          ·
            refine ⟨5748714582647482958092753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7664952776863310610790337 5748714582647482958092753)
            ·
              refine ⟨4311535936985612218569565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5748714582647482958092753 4311535936985612218569565)
              ·
                refine ⟨1616825976369604581963587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4311535936985612218569565 1616825976369604581963587)
                ·
                  refine ⟨2425238964554406872945381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616825976369604581963587 2425238964554406872945381)
                  ·
                    refine ⟨454732305853951288677259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2425238964554406872945381 454732305853951288677259)
                    ·
                      rfl

theorem cell22_1328382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1328382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328382 prefixEnd_1328382 := by exact prefixLift 1328382
  have htrace : WordTrace (prefixWord ++ tailWord_1328382) baseStart_1328382 baseEnd_1328382 := by
    simpa [prefixWord, tailWord_1328382, baseEnd_1328382] using wordTrace_append hprefix tailTrace_1328382
  have hstable : (prefixWord ++ tailWord_1328382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328382).length < 2 ^ (prefixWord ++ tailWord_1328382).sum := by decide
  have hdescent : baseEnd_1328382 < baseStart_1328382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328395 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 4, 3]
def baseStart_1328395 : Nat := 118140960795 + 1328395 * 2 ^ 59
def prefixEnd_1328395 : Nat := 4983230072969 + 3 ^ 40 * 1328395 * 2
def baseEnd_1328395 : Nat := 454736756019623588102219

theorem tailTrace_1328395 : CollatzResearch.WordTrace tailWord_1328395 prefixEnd_1328395 454736756019623588102219 := by
  unfold tailWord_1328395
  simp only [CollatzResearch.WordTrace]
  refine ⟨48450546022459261648922639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32300364014972841099281759 48450546022459261648922639)
  ·
    refine ⟨72675819033688892473383959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48450546022459261648922639 72675819033688892473383959)
    ·
      refine ⟨109013728550533338710075939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72675819033688892473383959 109013728550533338710075939)
      ·
        refine ⟨163520592825800008065113909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109013728550533338710075939 163520592825800008065113909)
        ·
          refine ⟨15330055577418750756104429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163520592825800008065113909 15330055577418750756104429)
          ·
            refine ⟨5748770841532031533539161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15330055577418750756104429 5748770841532031533539161)
            ·
              refine ⟨4311578131149023650154371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5748770841532031533539161 4311578131149023650154371)
              ·
                refine ⟨6467367196723535475231557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4311578131149023650154371 6467367196723535475231557)
                ·
                  refine ⟨1212631349385662901605917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6467367196723535475231557 1212631349385662901605917)
                  ·
                    refine ⟨454736756019623588102219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1212631349385662901605917 454736756019623588102219)
                    ·
                      rfl

theorem cell22_1328395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 3].length) (baseStart_1328395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328395 prefixEnd_1328395 := by exact prefixLift 1328395
  have htrace : WordTrace (prefixWord ++ tailWord_1328395) baseStart_1328395 baseEnd_1328395 := by
    simpa [prefixWord, tailWord_1328395, baseEnd_1328395] using wordTrace_append hprefix tailTrace_1328395
  have hstable : (prefixWord ++ tailWord_1328395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328395).length < 2 ^ (prefixWord ++ tailWord_1328395).sum := by decide
  have hdescent : baseEnd_1328395 < baseStart_1328395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328408 : List Nat := [2, 1, 2, 3, 1, 3, 1, 9]
def baseStart_1328408 : Nat := 118140960795 + 1328408 * 2 ^ 59
def prefixEnd_1328408 : Nat := 4983230072969 + 3 ^ 40 * 1328408 * 2
def baseEnd_1328408 : Nat := 50526800687255098614131

theorem tailTrace_1328408 : CollatzResearch.WordTrace tailWord_1328408 prefixEnd_1328408 50526800687255098614131 := by
  unfold tailWord_1328408
  simp only [CollatzResearch.WordTrace]
  refine ⟨24225510085706082434572939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32300680114274776579430585 24225510085706082434572939)
  ·
    refine ⟨36338265128559123651859409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24225510085706082434572939 36338265128559123651859409)
    ·
      refine ⟨27253698846419342738894557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36338265128559123651859409 27253698846419342738894557)
      ·
        refine ⟨10220137067407253527085459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27253698846419342738894557 10220137067407253527085459)
        ·
          refine ⟨15330205601110880290628189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10220137067407253527085459 15330205601110880290628189)
          ·
            refine ⟨5748827100416580108985571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15330205601110880290628189 5748827100416580108985571)
            ·
              refine ⟨8623240650624870163478357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5748827100416580108985571 8623240650624870163478357)
              ·
                refine ⟨50526800687255098614131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8623240650624870163478357 50526800687255098614131)
                ·
                  rfl

theorem cell22_1328408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 9].length) (baseStart_1328408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328408 prefixEnd_1328408 := by exact prefixLift 1328408
  have htrace : WordTrace (prefixWord ++ tailWord_1328408) baseStart_1328408 baseEnd_1328408 := by
    simpa [prefixWord, tailWord_1328408, baseEnd_1328408] using wordTrace_append hprefix tailTrace_1328408
  have hstable : (prefixWord ++ tailWord_1328408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328408).length < 2 ^ (prefixWord ++ tailWord_1328408).sum := by decide
  have hdescent : baseEnd_1328408 < baseStart_1328408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328453 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 7]
def baseStart_1328453 : Nat := 118140960795 + 1328453 * 2 ^ 59
def prefixEnd_1328453 : Nat := 4983230072969 + 3 ^ 40 * 1328453 * 2
def baseEnd_1328453 : Nat := 151585536868310256717347

theorem tailTrace_1328453 : CollatzResearch.WordTrace tailWord_1328453 prefixEnd_1328453 151585536868310256717347 := by
  unfold tailWord_1328453
  simp only [CollatzResearch.WordTrace]
  refine ⟨48452661456249137554534013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32301774304166091703022675 48452661456249137554534013)
  ·
    refine ⟨18169748046093426582950255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48452661456249137554534013 18169748046093426582950255)
    ·
      refine ⟨27254622069140139874425383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18169748046093426582950255 27254622069140139874425383)
      ·
        refine ⟨40881933103710209811638075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27254622069140139874425383 40881933103710209811638075)
        ·
          refine ⟨61322899655565314717457113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40881933103710209811638075 61322899655565314717457113)
          ·
            refine ⟨45992174741673986038092835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61322899655565314717457113 45992174741673986038092835)
            ·
              refine ⟨68988262112510979057139253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45992174741673986038092835 68988262112510979057139253)
              ·
                refine ⟨6467649573047904286606805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68988262112510979057139253 6467649573047904286606805)
                ·
                  refine ⟨151585536868310256717347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6467649573047904286606805 151585536868310256717347)
                  ·
                    rfl

theorem cell22_1328453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_1328453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328453 prefixEnd_1328453 := by exact prefixLift 1328453
  have htrace : WordTrace (prefixWord ++ tailWord_1328453) baseStart_1328453 baseEnd_1328453 := by
    simpa [prefixWord, tailWord_1328453, baseEnd_1328453] using wordTrace_append hprefix tailTrace_1328453
  have hstable : (prefixWord ++ tailWord_1328453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328453).length < 2 ^ (prefixWord ++ tailWord_1328453).sum := by decide
  have hdescent : baseEnd_1328453 < baseStart_1328453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328515 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 6]
def baseStart_1328515 : Nat := 118140960795 + 1328515 * 2 ^ 59
def prefixEnd_1328515 : Nat := 4983230072969 + 3 ^ 40 * 1328515 * 2
def baseEnd_1328515 : Nat := 151592611490661091700617

theorem tailTrace_1328515 : CollatzResearch.WordTrace tailWord_1328515 prefixEnd_1328515 151592611490661091700617 := by
  unfold tailWord_1328515
  simp only [CollatzResearch.WordTrace]
  refine ⟨48454922782024522143290999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32303281854683014762193999 48454922782024522143290999)
  ·
    refine ⟨72682384173036783214936499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48454922782024522143290999 72682384173036783214936499)
    ·
      refine ⟨109023576259555174822404749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72682384173036783214936499 109023576259555174822404749)
      ·
        refine ⟨40883841097333190558401781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109023576259555174822404749 40883841097333190558401781)
        ·
          refine ⟨3832860102874986614850167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40883841097333190558401781 3832860102874986614850167)
          ·
            refine ⟨5749290154312479922275251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832860102874986614850167 5749290154312479922275251)
            ·
              refine ⟨8623935231468719883412877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749290154312479922275251 8623935231468719883412877)
              ·
                refine ⟨3233975711800769956279829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8623935231468719883412877 3233975711800769956279829)
                ·
                  refine ⟨151592611490661091700617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3233975711800769956279829 151592611490661091700617)
                  ·
                    rfl

theorem cell22_1328515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 6].length) (baseStart_1328515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328515 prefixEnd_1328515 := by exact prefixLift 1328515
  have htrace : WordTrace (prefixWord ++ tailWord_1328515) baseStart_1328515 baseEnd_1328515 := by
    simpa [prefixWord, tailWord_1328515, baseEnd_1328515] using wordTrace_append hprefix tailTrace_1328515
  have hstable : (prefixWord ++ tailWord_1328515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328515).length < 2 ^ (prefixWord ++ tailWord_1328515).sum := by decide
  have hdescent : baseEnd_1328515 < baseStart_1328515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328532 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 6]
def baseStart_1328532 : Nat := 118140960795 + 1328532 * 2 ^ 59
def prefixEnd_1328532 : Nat := 4983230072969 + 3 ^ 40 * 1328532 * 2
def baseEnd_1328532 : Nat := 151594551306466965808933

theorem tailTrace_1328532 : CollatzResearch.WordTrace tailWord_1328532 prefixEnd_1328532 151594551306466965808933 := by
  unfold tailWord_1328532
  simp only [CollatzResearch.WordTrace]
  refine ⟨24227771411481467023329925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32303695215308622697773233 24227771411481467023329925)
  ·
    refine ⟨4542707139652775066874361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24227771411481467023329925 4542707139652775066874361)
    ·
      refine ⟨3407030354739581300155771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4542707139652775066874361 3407030354739581300155771)
      ·
        refine ⟨5110545532109371950233657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3407030354739581300155771 5110545532109371950233657)
        ·
          refine ⟨3832909149082028962675243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5110545532109371950233657 3832909149082028962675243)
          ·
            refine ⟨5749363723623043444012865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832909149082028962675243 5749363723623043444012865)
            ·
              refine ⟨4312022792717282583009649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5749363723623043444012865 4312022792717282583009649)
              ·
                refine ⟨3234017094537961937257237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4312022792717282583009649 3234017094537961937257237)
                ·
                  refine ⟨151594551306466965808933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3234017094537961937257237 151594551306466965808933)
                  ·
                    rfl

theorem cell22_1328532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_1328532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328532 prefixEnd_1328532 := by exact prefixLift 1328532
  have htrace : WordTrace (prefixWord ++ tailWord_1328532) baseStart_1328532 baseEnd_1328532 := by
    simpa [prefixWord, tailWord_1328532, baseEnd_1328532] using wordTrace_append hprefix tailTrace_1328532
  have hstable : (prefixWord ++ tailWord_1328532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328532).length < 2 ^ (prefixWord ++ tailWord_1328532).sum := by decide
  have hdescent : baseEnd_1328532 < baseStart_1328532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328637 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_1328637 : Nat := 118140960795 + 1328637 * 2 ^ 59
def prefixEnd_1328637 : Nat := 4983230072969 + 3 ^ 40 * 1328637 * 2
def baseEnd_1328637 : Nat := 454819597565215623551477

theorem tailTrace_1328637 : CollatzResearch.WordTrace tailWord_1328637 prefixEnd_1328637 454819597565215623551477 := by
  unfold tailWord_1328637
  simp only [CollatzResearch.WordTrace]
  refine ⟨48459372487582536979232165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32306248325055024652821443 48459372487582536979232165)
  ·
    refine ⟨9086132341421725683606031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48459372487582536979232165 9086132341421725683606031)
    ·
      refine ⟨13629198512132588525409047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9086132341421725683606031 13629198512132588525409047)
      ·
        refine ⟨20443797768198882788113571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13629198512132588525409047 20443797768198882788113571)
        ·
          refine ⟨30665696652298324182170357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20443797768198882788113571 30665696652298324182170357)
          ·
            refine ⟨2874909061152967892078471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30665696652298324182170357 2874909061152967892078471)
            ·
              refine ⟨4312363591729451838117707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2874909061152967892078471 4312363591729451838117707)
              ·
                refine ⟨6468545387594177757176561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312363591729451838117707 6468545387594177757176561)
                ·
                  refine ⟨4851409040695633317882421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6468545387594177757176561 4851409040695633317882421)
                  ·
                    refine ⟨454819597565215623551477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4851409040695633317882421 454819597565215623551477)
                    ·
                      rfl

theorem cell22_1328637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_1328637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328637 prefixEnd_1328637 := by exact prefixLift 1328637
  have htrace : WordTrace (prefixWord ++ tailWord_1328637) baseStart_1328637 baseEnd_1328637 := by
    simpa [prefixWord, tailWord_1328637, baseEnd_1328637] using wordTrace_append hprefix tailTrace_1328637
  have hstable : (prefixWord ++ tailWord_1328637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328637).length < 2 ^ (prefixWord ++ tailWord_1328637).sum := by decide
  have hdescent : baseEnd_1328637 < baseStart_1328637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328660 : List Nat := [2, 4, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1328660 : Nat := 118140960795 + 1328660 * 2 ^ 59
def prefixEnd_1328660 : Nat := 4983230072969 + 3 ^ 40 * 1328660 * 2
def baseEnd_1328660 : Nat := 454827470935251230226407

theorem tailTrace_1328660 : CollatzResearch.WordTrace tailWord_1328660 prefixEnd_1328660 454827470935251230226407 := by
  unfold tailWord_1328660
  simp only [CollatzResearch.WordTrace]
  refine ⟨24230105683249605953659717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32306807577666141271546289 24230105683249605953659717)
  ·
    refine ⟨4543144815609301116311197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24230105683249605953659717 4543144815609301116311197)
    ·
      refine ⟨1703679305853487918616699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4543144815609301116311197 1703679305853487918616699)
      ·
        refine ⟨2555518958780231877925049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1703679305853487918616699 2555518958780231877925049)
        ·
          refine ⟨1916639219085173908443787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2555518958780231877925049 1916639219085173908443787)
          ·
            refine ⟨2874958828627760862665681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916639219085173908443787 2874958828627760862665681)
            ·
              refine ⟨2156219121470820646999261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2874958828627760862665681 2156219121470820646999261)
              ·
                refine ⟨808582170551557742624723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2156219121470820646999261 808582170551557742624723)
                ·
                  refine ⟨1212873255827336613937085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808582170551557742624723 1212873255827336613937085)
                  ·
                    refine ⟨454827470935251230226407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1212873255827336613937085 454827470935251230226407)
                    ·
                      rfl

theorem cell22_1328660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1328660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328660 prefixEnd_1328660 := by exact prefixLift 1328660
  have htrace : WordTrace (prefixWord ++ tailWord_1328660) baseStart_1328660 baseEnd_1328660 := by
    simpa [prefixWord, tailWord_1328660, baseEnd_1328660] using wordTrace_append hprefix tailTrace_1328660
  have hstable : (prefixWord ++ tailWord_1328660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328660).length < 2 ^ (prefixWord ++ tailWord_1328660).sum := by decide
  have hdescent : baseEnd_1328660 < baseStart_1328660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328669 : List Nat := [1, 4, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_1328669 : Nat := 118140960795 + 1328669 * 2 ^ 59
def prefixEnd_1328669 : Nat := 4983230072969 + 3 ^ 40 * 1328669 * 2
def baseEnd_1328669 : Nat := 454830551819178206751379

theorem tailTrace_1328669 : CollatzResearch.WordTrace tailWord_1328669 prefixEnd_1328669 454830551819178206751379 := by
  unfold tailWord_1328669
  simp only [CollatzResearch.WordTrace]
  refine ⟨48460539623466606444397061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32307026415644404296264707 48460539623466606444397061)
  ·
    refine ⟨9086351179399988708324449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48460539623466606444397061 9086351179399988708324449)
    ·
      refine ⟨6814763384549991531243337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9086351179399988708324449 6814763384549991531243337)
      ·
        refine ⟨5111072538412493648432503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6814763384549991531243337 5111072538412493648432503)
        ·
          refine ⟨7666608807618740472648755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5111072538412493648432503 7666608807618740472648755)
          ·
            refine ⟨11499913211428110708973133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7666608807618740472648755 11499913211428110708973133)
            ·
              refine ⟨4312467454285541515864925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11499913211428110708973133 4312467454285541515864925)
              ·
                refine ⟨1617175295357078068449347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4312467454285541515864925 1617175295357078068449347)
                ·
                  refine ⟨2425762943035617102674021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617175295357078068449347 2425762943035617102674021)
                  ·
                    refine ⟨454830551819178206751379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2425762943035617102674021 454830551819178206751379)
                    ·
                      rfl

theorem cell22_1328669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_1328669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328669 prefixEnd_1328669 := by exact prefixLift 1328669
  have htrace : WordTrace (prefixWord ++ tailWord_1328669) baseStart_1328669 baseEnd_1328669 := by
    simpa [prefixWord, tailWord_1328669, baseEnd_1328669] using wordTrace_append hprefix tailTrace_1328669
  have hstable : (prefixWord ++ tailWord_1328669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328669).length < 2 ^ (prefixWord ++ tailWord_1328669).sum := by decide
  have hdescent : baseEnd_1328669 < baseStart_1328669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328697 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 1, 6]
def baseStart_1328697 : Nat := 118140960795 + 1328697 * 2 ^ 59
def prefixEnd_1328697 : Nat := 4983230072969 + 3 ^ 40 * 1328697 * 2
def baseEnd_1328697 : Nat := 454840136791395467051293

theorem tailTrace_1328697 : CollatzResearch.WordTrace tailWord_1328697 prefixEnd_1328697 454840136791395467051293 := by
  unfold tailWord_1328697
  simp only [CollatzResearch.WordTrace]
  refine ⟨48461560867365167226416345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32307707244910111484277563 48461560867365167226416345)
  ·
    refine ⟨36346170650523875419812259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48461560867365167226416345 36346170650523875419812259)
    ·
      refine ⟨54519255975785813129718389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36346170650523875419812259 54519255975785813129718389)
      ·
        refine ⟨5111180247729919980911099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54519255975785813129718389 5111180247729919980911099)
        ·
          refine ⟨7666770371594879971366649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5111180247729919980911099 7666770371594879971366649)
          ·
            refine ⟨5750077778696159978524987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7666770371594879971366649 5750077778696159978524987)
            ·
              refine ⟨8625116668044239967787481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750077778696159978524987 8625116668044239967787481)
              ·
                refine ⟨6468837501033179975840611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8625116668044239967787481 6468837501033179975840611)
                ·
                  refine ⟨9703256251549769963760917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6468837501033179975840611 9703256251549769963760917)
                  ·
                    refine ⟨454840136791395467051293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9703256251549769963760917 454840136791395467051293)
                    ·
                      rfl

theorem cell22_1328697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_1328697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328697 prefixEnd_1328697 := by exact prefixLift 1328697
  have htrace : WordTrace (prefixWord ++ tailWord_1328697) baseStart_1328697 baseEnd_1328697 := by
    simpa [prefixWord, tailWord_1328697, baseEnd_1328697] using wordTrace_append hprefix tailTrace_1328697
  have hstable : (prefixWord ++ tailWord_1328697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328697).length < 2 ^ (prefixWord ++ tailWord_1328697).sum := by decide
  have hdescent : baseEnd_1328697 < baseStart_1328697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328750 : List Nat := [4, 1, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_1328750 : Nat := 118140960795 + 1328750 * 2 ^ 59
def prefixEnd_1328750 : Nat := 4983230072969 + 3 ^ 40 * 1328750 * 2
def baseEnd_1328750 : Nat := 454858279774520995476131

theorem tailTrace_1328750 : CollatzResearch.WordTrace tailWord_1328750 prefixEnd_1328750 454858279774520995476131 := by
  unfold tailWord_1328750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6057936742021644659761963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32308995957448771518730469 6057936742021644659761963)
  ·
    refine ⟨9086905113032466989642945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6057936742021644659761963 9086905113032466989642945)
    ·
      refine ⟨6815178834774350242232209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9086905113032466989642945 6815178834774350242232209)
      ·
        refine ⟨5111384126080762681674157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6815178834774350242232209 5111384126080762681674157)
        ·
          refine ⟨1916769047280286005627809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5111384126080762681674157 1916769047280286005627809)
          ·
            refine ⟨1437576785460214504220857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1916769047280286005627809 1437576785460214504220857)
            ·
              refine ⟨1078182589095160878165643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1437576785460214504220857 1078182589095160878165643)
              ·
                refine ⟨1617273883642741317248465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078182589095160878165643 1617273883642741317248465)
                ·
                  refine ⟨1212955412732055987936349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1617273883642741317248465 1212955412732055987936349)
                  ·
                    refine ⟨454858279774520995476131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1212955412732055987936349 454858279774520995476131)
                    ·
                      rfl

theorem cell22_1328750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_1328750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328750 prefixEnd_1328750 := by exact prefixLift 1328750
  have htrace : WordTrace (prefixWord ++ tailWord_1328750) baseStart_1328750 baseEnd_1328750 := by
    simpa [prefixWord, tailWord_1328750, baseEnd_1328750] using wordTrace_append hprefix tailTrace_1328750
  have hstable : (prefixWord ++ tailWord_1328750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328750).length < 2 ^ (prefixWord ++ tailWord_1328750).sum := by decide
  have hdescent : baseEnd_1328750 < baseStart_1328750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328787 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 7, 4]
def baseStart_1328787 : Nat := 118140960795 + 1328787 * 2 ^ 59
def prefixEnd_1328787 : Nat := 4983230072969 + 3 ^ 40 * 1328787 * 2
def baseEnd_1328787 : Nat := 454870945630665232301017

theorem tailTrace_1328787 : CollatzResearch.WordTrace tailWord_1328787 prefixEnd_1328787 454870945630665232301017 := by
  unfold tailWord_1328787
  simp only [CollatzResearch.WordTrace]
  refine ⟨48464843437039112597192615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32309895624692741731461743 48464843437039112597192615)
  ·
    refine ⟨72697265155558668895788923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48464843437039112597192615 72697265155558668895788923)
    ·
      refine ⟨109045897733338003343683385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72697265155558668895788923 109045897733338003343683385)
      ·
        refine ⟨81784423300003502507762539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109045897733338003343683385 81784423300003502507762539)
        ·
          refine ⟨122676634950005253761643809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81784423300003502507762539 122676634950005253761643809)
          ·
            refine ⟨92007476212503940321232857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122676634950005253761643809 92007476212503940321232857)
            ·
              refine ⟨69005607159377955240924643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92007476212503940321232857 69005607159377955240924643)
              ·
                refine ⟨103508410739066932861386965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69005607159377955240924643 103508410739066932861386965)
                ·
                  refine ⟨2425978376696881238938757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 103508410739066932861386965 2425978376696881238938757)
                  ·
                    refine ⟨454870945630665232301017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2425978376696881238938757 454870945630665232301017)
                    ·
                      rfl

theorem cell22_1328787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 4].length) (baseStart_1328787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328787 prefixEnd_1328787 := by exact prefixLift 1328787
  have htrace : WordTrace (prefixWord ++ tailWord_1328787) baseStart_1328787 baseEnd_1328787 := by
    simpa [prefixWord, tailWord_1328787, baseEnd_1328787] using wordTrace_append hprefix tailTrace_1328787
  have hstable : (prefixWord ++ tailWord_1328787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328787).length < 2 ^ (prefixWord ++ tailWord_1328787).sum := by decide
  have hdescent : baseEnd_1328787 < baseStart_1328787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328804 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_1328804 : Nat := 118140960795 + 1328804 * 2 ^ 59
def prefixEnd_1328804 : Nat := 4983230072969 + 3 ^ 40 * 1328804 * 2
def baseEnd_1328804 : Nat := 454876765078082854625965

theorem tailTrace_1328804 : CollatzResearch.WordTrace tailWord_1328804 prefixEnd_1328804 454876765078082854625965 := by
  unfold tailWord_1328804
  simp only [CollatzResearch.WordTrace]
  refine ⟨24232731738988762250280733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32310308985318349667040977 24232731738988762250280733)
  ·
    refine ⟨9087274402120785843855275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24232731738988762250280733 9087274402120785843855275)
    ·
      refine ⟨13630911603181178765782913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9087274402120785843855275 13630911603181178765782913)
      ·
        refine ⟨10223183702385884074337185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13630911603181178765782913 10223183702385884074337185)
        ·
          refine ⟨7667387776789413055752889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10223183702385884074337185 7667387776789413055752889)
          ·
            refine ⟨5750540832592059791814667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7667387776789413055752889 5750540832592059791814667)
            ·
              refine ⟨8625811248888089687722001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750540832592059791814667 8625811248888089687722001)
              ·
                refine ⟨6469358436666067265791501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8625811248888089687722001 6469358436666067265791501)
                ·
                  refine ⟨2426009413749775224671813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6469358436666067265791501 2426009413749775224671813)
                  ·
                    refine ⟨454876765078082854625965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2426009413749775224671813 454876765078082854625965)
                    ·
                      rfl

theorem cell22_1328804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_1328804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328804 prefixEnd_1328804 := by exact prefixLift 1328804
  have htrace : WordTrace (prefixWord ++ tailWord_1328804) baseStart_1328804 baseEnd_1328804 := by
    simpa [prefixWord, tailWord_1328804, baseEnd_1328804] using wordTrace_append hprefix tailTrace_1328804
  have hstable : (prefixWord ++ tailWord_1328804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328804).length < 2 ^ (prefixWord ++ tailWord_1328804).sum := by decide
  have hdescent : baseEnd_1328804 < baseStart_1328804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328868 : List Nat := [2, 3, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_1328868 : Nat := 118140960795 + 1328868 * 2 ^ 59
def prefixEnd_1328868 : Nat := 4983230072969 + 3 ^ 40 * 1328868 * 2
def baseEnd_1328868 : Nat := 454898673586008021025769

theorem tailTrace_1328868 : CollatzResearch.WordTrace tailWord_1328868 prefixEnd_1328868 454898673586008021025769 := by
  unfold tailWord_1328868
  simp only [CollatzResearch.WordTrace]
  refine ⟨24233898874872831715445629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32311865166497108953927505 24233898874872831715445629)
  ·
    refine ⟨9087712078077311893292111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24233898874872831715445629 9087712078077311893292111)
    ·
      refine ⟨13631568117115967839938167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9087712078077311893292111 13631568117115967839938167)
      ·
        refine ⟨20447352175673951759907251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13631568117115967839938167 20447352175673951759907251)
        ·
          refine ⟨30671028263510927639860877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20447352175673951759907251 30671028263510927639860877)
          ·
            refine ⟨11501635598816597864947829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30671028263510927639860877 11501635598816597864947829)
            ·
              refine ⟨1078278337389056049838859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11501635598816597864947829 1078278337389056049838859)
              ·
                refine ⟨1617417506083584074758289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078278337389056049838859 1617417506083584074758289)
                ·
                  refine ⟨1213063129562688056068717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1617417506083584074758289 1213063129562688056068717)
                  ·
                    refine ⟨454898673586008021025769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1213063129562688056068717 454898673586008021025769)
                    ·
                      rfl

theorem cell22_1328868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_1328868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328868 prefixEnd_1328868 := by exact prefixLift 1328868
  have htrace : WordTrace (prefixWord ++ tailWord_1328868) baseStart_1328868 baseEnd_1328868 := by
    simpa [prefixWord, tailWord_1328868, baseEnd_1328868] using wordTrace_append hprefix tailTrace_1328868
  have hstable : (prefixWord ++ tailWord_1328868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328868).length < 2 ^ (prefixWord ++ tailWord_1328868).sum := by decide
  have hdescent : baseEnd_1328868 < baseStart_1328868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328881 : List Nat := [1, 2, 2, 2, 2, 5, 2, 6]
def baseStart_1328881 : Nat := 118140960795 + 1328881 * 2 ^ 59
def prefixEnd_1328881 : Nat := 4983230072969 + 3 ^ 40 * 1328881 * 2
def baseEnd_1328881 : Nat := 50544791527964480050081

theorem tailTrace_1328881 : CollatzResearch.WordTrace tailWord_1328881 prefixEnd_1328881 50544791527964480050081 := by
  unfold tailWord_1328881
  simp only [CollatzResearch.WordTrace]
  refine ⟨48468271898698566651114497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32312181265799044434076331 48468271898698566651114497)
  ·
    refine ⟨36351203924023924988335873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48468271898698566651114497 36351203924023924988335873)
    ·
      refine ⟨27263402943017943741251905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36351203924023924988335873 27263402943017943741251905)
      ·
        refine ⟨20447552207263457805938929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27263402943017943741251905 20447552207263457805938929)
        ·
          refine ⟨15335664155447593354454197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20447552207263457805938929 15335664155447593354454197)
          ·
            refine ⟨1437718514573211876980081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15335664155447593354454197 1437718514573211876980081)
            ·
              refine ⟨1078288885929908907735061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1437718514573211876980081 1078288885929908907735061)
              ·
                refine ⟨50544791527964480050081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1078288885929908907735061 50544791527964480050081)
                ·
                  rfl

theorem cell22_1328881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 6].length) (baseStart_1328881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328881 prefixEnd_1328881 := by exact prefixLift 1328881
  have htrace : WordTrace (prefixWord ++ tailWord_1328881) baseStart_1328881 baseEnd_1328881 := by
    simpa [prefixWord, tailWord_1328881, baseEnd_1328881] using wordTrace_append hprefix tailTrace_1328881
  have hstable : (prefixWord ++ tailWord_1328881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328881).length < 2 ^ (prefixWord ++ tailWord_1328881).sum := by decide
  have hdescent : baseEnd_1328881 < baseStart_1328881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328924 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1328924 : Nat := 118140960795 + 1328924 * 2 ^ 59
def prefixEnd_1328924 : Nat := 4983230072969 + 3 ^ 40 * 1328924 * 2
def baseEnd_1328924 : Nat := 454917843530442541625597

theorem tailTrace_1328924 : CollatzResearch.WordTrace tailWord_1328924 prefixEnd_1328924 454917843530442541625597 := by
  unfold tailWord_1328924
  simp only [CollatzResearch.WordTrace]
  refine ⟨24234920118771392497464913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32313226825028523329953217 24234920118771392497464913)
  ·
    refine ⟨18176190089078544373098685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24234920118771392497464913 18176190089078544373098685)
    ·
      refine ⟨6816071283404454139912007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18176190089078544373098685 6816071283404454139912007)
      ·
        refine ⟨10224106925106681209868011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6816071283404454139912007 10224106925106681209868011)
        ·
          refine ⟨15336160387660021814802017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10224106925106681209868011 15336160387660021814802017)
          ·
            refine ⟨11502120290745016361101513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15336160387660021814802017 11502120290745016361101513)
            ·
              refine ⟨8626590218058762270826135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11502120290745016361101513 8626590218058762270826135)
              ·
                refine ⟨12939885327088143406239203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8626590218058762270826135 12939885327088143406239203)
                ·
                  refine ⟨19409827990632215109358805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12939885327088143406239203 19409827990632215109358805)
                  ·
                    refine ⟨454917843530442541625597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19409827990632215109358805 454917843530442541625597)
                    ·
                      rfl

theorem cell22_1328924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1328924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328924 prefixEnd_1328924 := by exact prefixLift 1328924
  have htrace : WordTrace (prefixWord ++ tailWord_1328924) baseStart_1328924 baseEnd_1328924 := by
    simpa [prefixWord, tailWord_1328924, baseEnd_1328924] using wordTrace_append hprefix tailTrace_1328924
  have hstable : (prefixWord ++ tailWord_1328924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328924).length < 2 ^ (prefixWord ++ tailWord_1328924).sum := by decide
  have hdescent : baseEnd_1328924 < baseStart_1328924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328956 : List Nat := [2, 2, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_1328956 : Nat := 118140960795 + 1328956 * 2 ^ 59
def prefixEnd_1328956 : Nat := 4983230072969 + 3 ^ 40 * 1328956 * 2
def baseEnd_1328956 : Nat := 454928797784405124825499

theorem tailTrace_1328956 : CollatzResearch.WordTrace tailWord_1328956 prefixEnd_1328956 454928797784405124825499 := by
  unfold tailWord_1328956
  simp only [CollatzResearch.WordTrace]
  refine ⟨24235503686713427230047361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32314004915617902973396481 24235503686713427230047361)
  ·
    refine ⟨18176627765035070422535521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24235503686713427230047361 18176627765035070422535521)
    ·
      refine ⟨13632470823776302816901641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18176627765035070422535521 13632470823776302816901641)
      ·
        refine ⟨10224353117832227112676231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13632470823776302816901641 10224353117832227112676231)
        ·
          refine ⟨15336529676748340669014347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10224353117832227112676231 15336529676748340669014347)
          ·
            refine ⟨23004794515122511003521521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15336529676748340669014347 23004794515122511003521521)
            ·
              refine ⟨17253595886341883252641141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23004794515122511003521521 17253595886341883252641141)
              ·
                refine ⟨1617524614344551554935107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17253595886341883252641141 1617524614344551554935107)
                ·
                  refine ⟨2426286921516827332402661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617524614344551554935107 2426286921516827332402661)
                  ·
                    refine ⟨454928797784405124825499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2426286921516827332402661 454928797784405124825499)
                    ·
                      rfl

theorem cell22_1328956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_1328956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328956 prefixEnd_1328956 := by exact prefixLift 1328956
  have htrace : WordTrace (prefixWord ++ tailWord_1328956) baseStart_1328956 baseEnd_1328956 := by
    simpa [prefixWord, tailWord_1328956, baseEnd_1328956] using wordTrace_append hprefix tailTrace_1328956
  have hstable : (prefixWord ++ tailWord_1328956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328956).length < 2 ^ (prefixWord ++ tailWord_1328956).sum := by decide
  have hdescent : baseEnd_1328956 < baseStart_1328956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328969 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 3, 5]
def baseStart_1328969 : Nat := 118140960795 + 1328969 * 2 ^ 59
def prefixEnd_1328969 : Nat := 4983230072969 + 3 ^ 40 * 1328969 * 2
def baseEnd_1328969 : Nat := 454933247950077424250459

theorem tailTrace_1328969 : CollatzResearch.WordTrace tailWord_1328969 prefixEnd_1328969 454933247950077424250459 := by
  unfold tailWord_1328969
  simp only [CollatzResearch.WordTrace]
  refine ⟨48471481522379757680317961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32314321014919838453545307 48471481522379757680317961)
  ·
    refine ⟨36353611141784818260238471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48471481522379757680317961 36353611141784818260238471)
    ·
      refine ⟨54530416712677227390357707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36353611141784818260238471 54530416712677227390357707)
      ·
        refine ⟨81795625069015841085536561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54530416712677227390357707 81795625069015841085536561)
        ·
          refine ⟨61346718801761880814152421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81795625069015841085536561 61346718801761880814152421)
          ·
            refine ⟨11502509775330352652653579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61346718801761880814152421 11502509775330352652653579)
            ·
              refine ⟨17253764662995528978980369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11502509775330352652653579 17253764662995528978980369)
              ·
                refine ⟨12940323497246646734235277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17253764662995528978980369 12940323497246646734235277)
                ·
                  refine ⟨4852621311467492525338229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12940323497246646734235277 4852621311467492525338229)
                  ·
                    refine ⟨454933247950077424250459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4852621311467492525338229 454933247950077424250459)
                    ·
                      rfl

theorem cell22_1328969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_1328969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328969 prefixEnd_1328969 := by exact prefixLift 1328969
  have htrace : WordTrace (prefixWord ++ tailWord_1328969) baseStart_1328969 baseEnd_1328969 := by
    simpa [prefixWord, tailWord_1328969, baseEnd_1328969] using wordTrace_append hprefix tailTrace_1328969
  have hstable : (prefixWord ++ tailWord_1328969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328969).length < 2 ^ (prefixWord ++ tailWord_1328969).sum := by decide
  have hdescent : baseEnd_1328969 < baseStart_1328969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328973 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1328973 : Nat := 118140960795 + 1328973 * 2 ^ 59
def prefixEnd_1328973 : Nat := 4983230072969 + 3 ^ 40 * 1328973 * 2
def baseEnd_1328973 : Nat := 454934617231822747150447

theorem tailTrace_1328973 : CollatzResearch.WordTrace tailWord_1328973 prefixEnd_1328973 454934617231822747150447 := by
  unfold tailWord_1328973
  simp only [CollatzResearch.WordTrace]
  refine ⟨48471627414365266363463573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32314418276243510908975715 48471627414365266363463573)
  ·
    refine ⟨2272107535048371860787355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48471627414365266363463573 2272107535048371860787355)
    ·
      refine ⟨3408161302572557791181033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2272107535048371860787355 3408161302572557791181033)
      ·
        refine ⟨2556120976929418343385775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3408161302572557791181033 2556120976929418343385775)
        ·
          refine ⟨3834181465394127515078663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2556120976929418343385775 3834181465394127515078663)
          ·
            refine ⟨5751272198091191272617995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834181465394127515078663 5751272198091191272617995)
            ·
              refine ⟨8626908297136786908926993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5751272198091191272617995 8626908297136786908926993)
              ·
                refine ⟨6470181222852590181695245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8626908297136786908926993 6470181222852590181695245)
                ·
                  refine ⟨2426317958569721318135717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6470181222852590181695245 2426317958569721318135717)
                  ·
                    refine ⟨454934617231822747150447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2426317958569721318135717 454934617231822747150447)
                    ·
                      rfl

theorem cell22_1328973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1328973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328973 prefixEnd_1328973 := by exact prefixLift 1328973
  have htrace : WordTrace (prefixWord ++ tailWord_1328973) baseStart_1328973 baseEnd_1328973 := by
    simpa [prefixWord, tailWord_1328973, baseEnd_1328973] using wordTrace_append hprefix tailTrace_1328973
  have hstable : (prefixWord ++ tailWord_1328973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328973).length < 2 ^ (prefixWord ++ tailWord_1328973).sum := by decide
  have hdescent : baseEnd_1328973 < baseStart_1328973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328986 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_1328986 : Nat := 118140960795 + 1328986 * 2 ^ 59
def prefixEnd_1328986 : Nat := 4983230072969 + 3 ^ 40 * 1328986 * 2
def baseEnd_1328986 : Nat := 454939067397495046575407

theorem tailTrace_1328986 : CollatzResearch.WordTrace tailWord_1328986 prefixEnd_1328986 454939067397495046575407 := by
  unfold tailWord_1328986
  simp only [CollatzResearch.WordTrace]
  refine ⟨12118025390829542395921703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32314734375545446389124541 12118025390829542395921703)
  ·
    refine ⟨18177038086244313593882555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12118025390829542395921703 18177038086244313593882555)
    ·
      refine ⟨27265557129366470390823833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18177038086244313593882555 27265557129366470390823833)
      ·
        refine ⟨20449167847024852793117875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27265557129366470390823833 20449167847024852793117875)
        ·
          refine ⟨30673751770537279189676813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20449167847024852793117875 30673751770537279189676813)
          ·
            refine ⟨11502656913951479696128805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30673751770537279189676813 11502656913951479696128805)
            ·
              refine ⟨2156748171365902443024151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11502656913951479696128805 2156748171365902443024151)
              ·
                refine ⟨3235122257048853664536227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156748171365902443024151 3235122257048853664536227)
                ·
                  refine ⟨4852683385573280496804341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3235122257048853664536227 4852683385573280496804341)
                  ·
                    refine ⟨454939067397495046575407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4852683385573280496804341 454939067397495046575407)
                    ·
                      rfl

theorem cell22_1328986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_1328986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328986 prefixEnd_1328986 := by exact prefixLift 1328986
  have htrace : WordTrace (prefixWord ++ tailWord_1328986) baseStart_1328986 baseEnd_1328986 := by
    simpa [prefixWord, tailWord_1328986, baseEnd_1328986] using wordTrace_append hprefix tailTrace_1328986
  have hstable : (prefixWord ++ tailWord_1328986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328986).length < 2 ^ (prefixWord ++ tailWord_1328986).sum := by decide
  have hdescent : baseEnd_1328986 < baseStart_1328986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328988 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 6]
def baseStart_1328988 : Nat := 118140960795 + 1328988 * 2 ^ 59
def prefixEnd_1328988 : Nat := 4983230072969 + 3 ^ 40 * 1328988 * 2
def baseEnd_1328988 : Nat := 151646584012789236008467

theorem tailTrace_1328988 : CollatzResearch.WordTrace tailWord_1328988 prefixEnd_1328988 151646584012789236008467 := by
  unfold tailWord_1328988
  simp only [CollatzResearch.WordTrace]
  refine ⟨24236087254655461962629809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32314783006207282616839745 24236087254655461962629809)
  ·
    refine ⟨18177065440991596471972357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24236087254655461962629809 18177065440991596471972357)
    ·
      refine ⟨3408199770185924338494817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18177065440991596471972357 3408199770185924338494817)
      ·
        refine ⟨2556149827639443253871113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3408199770185924338494817 2556149827639443253871113)
        ·
          refine ⟨1917112370729582440403335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2556149827639443253871113 1917112370729582440403335)
          ·
            refine ⟨2875668556094373660605003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917112370729582440403335 2875668556094373660605003)
            ·
              refine ⟨4313502834141560490907505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875668556094373660605003 4313502834141560490907505)
              ·
                refine ⟨3235127125606170368180629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4313502834141560490907505 3235127125606170368180629)
                ·
                  refine ⟨151646584012789236008467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3235127125606170368180629 151646584012789236008467)
                  ·
                    rfl

theorem cell22_1328988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_1328988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1328988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1328988 prefixEnd_1328988 := by exact prefixLift 1328988
  have htrace : WordTrace (prefixWord ++ tailWord_1328988) baseStart_1328988 baseEnd_1328988 := by
    simpa [prefixWord, tailWord_1328988, baseEnd_1328988] using wordTrace_append hprefix tailTrace_1328988
  have hstable : (prefixWord ++ tailWord_1328988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328988).length < 2 ^ (prefixWord ++ tailWord_1328988).sum := by decide
  have hdescent : baseEnd_1328988 < baseStart_1328988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329108 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1329108 : Nat := 118140960795 + 1329108 * 2 ^ 59
def prefixEnd_1329108 : Nat := 4983230072969 + 3 ^ 40 * 1329108 * 2
def baseEnd_1329108 : Nat := 454980830490727395025033

theorem tailTrace_1329108 : CollatzResearch.WordTrace tailWord_1329108 prefixEnd_1329108 454980830490727395025033 := by
  unfold tailWord_1329108
  simp only [CollatzResearch.WordTrace]
  refine ⟨24238275634438092209813989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32317700845917456279751985 24238275634438092209813989)
  ·
    refine ⟨4544676681457142289340123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24238275634438092209813989 4544676681457142289340123)
    ·
      refine ⟨6817015022185713434010185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4544676681457142289340123 6817015022185713434010185)
      ·
        refine ⟨5112761266639285075507639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6817015022185713434010185 5112761266639285075507639)
        ·
          refine ⟨7669141899958927613261459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5112761266639285075507639 7669141899958927613261459)
          ·
            refine ⟨11503712849938391419892189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7669141899958927613261459 11503712849938391419892189)
            ·
              refine ⟨4313892318726896782459571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11503712849938391419892189 4313892318726896782459571)
              ·
                refine ⟨6470838478090345173689357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4313892318726896782459571 6470838478090345173689357)
                ·
                  refine ⟨2426564429283879440133509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6470838478090345173689357 2426564429283879440133509)
                  ·
                    refine ⟨454980830490727395025033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2426564429283879440133509 454980830490727395025033)
                    ·
                      rfl

theorem cell22_1329108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1329108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329108 prefixEnd_1329108 := by exact prefixLift 1329108
  have htrace : WordTrace (prefixWord ++ tailWord_1329108) baseStart_1329108 baseEnd_1329108 := by
    simpa [prefixWord, tailWord_1329108, baseEnd_1329108] using wordTrace_append hprefix tailTrace_1329108
  have hstable : (prefixWord ++ tailWord_1329108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329108).length < 2 ^ (prefixWord ++ tailWord_1329108).sum := by decide
  have hdescent : baseEnd_1329108 < baseStart_1329108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329121 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 3, 5]
def baseStart_1329121 : Nat := 118140960795 + 1329121 * 2 ^ 59
def prefixEnd_1329121 : Nat := 4983230072969 + 3 ^ 40 * 1329121 * 2
def baseEnd_1329121 : Nat := 454985280656399694449993

theorem tailTrace_1329121 : CollatzResearch.WordTrace tailWord_1329121 prefixEnd_1329121 454985280656399694449993 := by
  unfold tailWord_1329121
  simp only [CollatzResearch.WordTrace]
  refine ⟨48477025417829087639851217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32318016945219391759900811 48477025417829087639851217)
  ·
    refine ⟨36357769063371815729888413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48477025417829087639851217 36357769063371815729888413)
    ·
      refine ⟨13634163398764430898708155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36357769063371815729888413 13634163398764430898708155)
      ·
        refine ⟨20451245098146646348062233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13634163398764430898708155 20451245098146646348062233)
        ·
          refine ⟨15338433823609984761046675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20451245098146646348062233 15338433823609984761046675)
          ·
            refine ⟨23007650735414977141570013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15338433823609984761046675 23007650735414977141570013)
            ·
              refine ⟨8627869025780616428088755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23007650735414977141570013 8627869025780616428088755)
              ·
                refine ⟨12941803538670924642133133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8627869025780616428088755 12941803538670924642133133)
                ·
                  refine ⟨4853176327001596740799925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12941803538670924642133133 4853176327001596740799925)
                  ·
                    refine ⟨454985280656399694449993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4853176327001596740799925 454985280656399694449993)
                    ·
                      rfl

theorem cell22_1329121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_1329121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329121 prefixEnd_1329121 := by exact prefixLift 1329121
  have htrace : WordTrace (prefixWord ++ tailWord_1329121) baseStart_1329121 baseEnd_1329121 := by
    simpa [prefixWord, tailWord_1329121, baseEnd_1329121] using wordTrace_append hprefix tailTrace_1329121
  have hstable : (prefixWord ++ tailWord_1329121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329121).length < 2 ^ (prefixWord ++ tailWord_1329121).sum := by decide
  have hdescent : baseEnd_1329121 < baseStart_1329121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329133 : List Nat := [1, 5, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_1329133 : Nat := 118140960795 + 1329133 * 2 ^ 59
def prefixEnd_1329133 : Nat := 4983230072969 + 3 ^ 40 * 1329133 * 2
def baseEnd_1329133 : Nat := 454989388501635663149957

theorem tailTrace_1329133 : CollatzResearch.WordTrace tailWord_1329133 prefixEnd_1329133 454989388501635663149957 := by
  unfold tailWord_1329133
  simp only [CollatzResearch.WordTrace]
  refine ⟨48477463093785613689288053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32318308729190409126192035 48477463093785613689288053)
  ·
    refine ⟨4544762165042401283370755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48477463093785613689288053 4544762165042401283370755)
    ·
      refine ⟨6817143247563601925056133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4544762165042401283370755 6817143247563601925056133)
      ·
        refine ⟨1278214358918175360948025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6817143247563601925056133 1278214358918175360948025)
        ·
          refine ⟨958660769188631520711019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1278214358918175360948025 958660769188631520711019)
          ·
            refine ⟨1437991153782947281066529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958660769188631520711019 1437991153782947281066529)
            ·
              refine ⟨1078493365337210460799897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1437991153782947281066529 1078493365337210460799897)
              ·
                refine ⟨808870024002907845599923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078493365337210460799897 808870024002907845599923)
                ·
                  refine ⟨1213305036004361768399885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808870024002907845599923 1213305036004361768399885)
                  ·
                    refine ⟨454989388501635663149957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1213305036004361768399885 454989388501635663149957)
                    ·
                      rfl

theorem cell22_1329133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_1329133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329133 prefixEnd_1329133 := by exact prefixLift 1329133
  have htrace : WordTrace (prefixWord ++ tailWord_1329133) baseStart_1329133 baseEnd_1329133 := by
    simpa [prefixWord, tailWord_1329133, baseEnd_1329133] using wordTrace_append hprefix tailTrace_1329133
  have hstable : (prefixWord ++ tailWord_1329133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329133).length < 2 ^ (prefixWord ++ tailWord_1329133).sum := by decide
  have hdescent : baseEnd_1329133 < baseStart_1329133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329183 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 5, 3]
def baseStart_1329183 : Nat := 118140960795 + 1329183 * 2 ^ 59
def prefixEnd_1329183 : Nat := 4983230072969 + 3 ^ 40 * 1329183 * 2
def baseEnd_1329183 : Nat := 455006504523452199399803

theorem tailTrace_1329183 : CollatzResearch.WordTrace tailWord_1329183 prefixEnd_1329183 455006504523452199399803 := by
  unfold tailWord_1329183
  simp only [CollatzResearch.WordTrace]
  refine ⟨48479286743604472228608203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32319524495736314819072135 48479286743604472228608203)
  ·
    refine ⟨72718930115406708342912305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48479286743604472228608203 72718930115406708342912305)
    ·
      refine ⟨54539197586555031257184229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72718930115406708342912305 54539197586555031257184229)
      ·
        refine ⟨10226099547479068360722043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54539197586555031257184229 10226099547479068360722043)
        ·
          refine ⟨15339149321218602541083065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10226099547479068360722043 15339149321218602541083065)
          ·
            refine ⟨11504361990913951905812299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15339149321218602541083065 11504361990913951905812299)
            ·
              refine ⟨17256542986370927858718449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11504361990913951905812299 17256542986370927858718449)
              ·
                refine ⟨12942407239778195894038837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17256542986370927858718449 12942407239778195894038837)
                ·
                  refine ⟨1213350678729205865066141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12942407239778195894038837 1213350678729205865066141)
                  ·
                    refine ⟨455006504523452199399803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1213350678729205865066141 455006504523452199399803)
                    ·
                      rfl

theorem cell22_1329183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 3].length) (baseStart_1329183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329183 prefixEnd_1329183 := by exact prefixLift 1329183
  have htrace : WordTrace (prefixWord ++ tailWord_1329183) baseStart_1329183 baseEnd_1329183 := by
    simpa [prefixWord, tailWord_1329183, baseEnd_1329183] using wordTrace_append hprefix tailTrace_1329183
  have hstable : (prefixWord ++ tailWord_1329183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329183).length < 2 ^ (prefixWord ++ tailWord_1329183).sum := by decide
  have hdescent : baseEnd_1329183 < baseStart_1329183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329200 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 3, 3]
def baseStart_1329200 : Nat := 118140960795 + 1329200 * 2 ^ 59
def prefixEnd_1329200 : Nat := 4983230072969 + 3 ^ 40 * 1329200 * 2
def baseEnd_1329200 : Nat := 455012323970869821724751

theorem tailTrace_1329200 : CollatzResearch.WordTrace tailWord_1329200 prefixEnd_1329200 455012323970869821724751 := by
  unfold tailWord_1329200
  simp only [CollatzResearch.WordTrace]
  refine ⟨24239953392271442065988527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32319937856361922754651369 24239953392271442065988527)
  ·
    refine ⟨36359930088407163098982791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24239953392271442065988527 36359930088407163098982791)
    ·
      refine ⟨54539895132610744648474187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36359930088407163098982791 54539895132610744648474187)
      ·
        refine ⟨81809842698916116972711281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54539895132610744648474187 81809842698916116972711281)
        ·
          refine ⟨61357382024187087729533461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81809842698916116972711281 61357382024187087729533461)
          ·
            refine ⟨2876127282383769737321881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61357382024187087729533461 2876127282383769737321881)
            ·
              refine ⟨2157095461787827302991411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2876127282383769737321881 2157095461787827302991411)
              ·
                refine ⟨3235643192681740954487117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2157095461787827302991411 3235643192681740954487117)
                ·
                  refine ⟨1213366197255652857932669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3235643192681740954487117 1213366197255652857932669)
                  ·
                    refine ⟨455012323970869821724751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1213366197255652857932669 455012323970869821724751)
                    ·
                      rfl

theorem cell22_1329200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 3, 3].length) (baseStart_1329200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329200 prefixEnd_1329200 := by exact prefixLift 1329200
  have htrace : WordTrace (prefixWord ++ tailWord_1329200) baseStart_1329200 baseEnd_1329200 := by
    simpa [prefixWord, tailWord_1329200, baseEnd_1329200] using wordTrace_append hprefix tailTrace_1329200
  have hstable : (prefixWord ++ tailWord_1329200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329200).length < 2 ^ (prefixWord ++ tailWord_1329200).sum := by decide
  have hdescent : baseEnd_1329200 < baseStart_1329200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329277 : List Nat := [1, 4, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_1329277 : Nat := 118140960795 + 1329277 * 2 ^ 59
def prefixEnd_1329277 : Nat := 4983230072969 + 3 ^ 40 * 1329277 * 2
def baseEnd_1329277 : Nat := 455038682644467287549515

theorem tailTrace_1329277 : CollatzResearch.WordTrace tailWord_1329277 prefixEnd_1329277 455038682644467287549515 := by
  unfold tailWord_1329277
  simp only [CollatzResearch.WordTrace]
  refine ⟨48482715205263926282530085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32321810136842617521686723 48482715205263926282530085)
  ·
    refine ⟨9090509100986986177974391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48482715205263926282530085 9090509100986986177974391)
    ·
      refine ⟨13635763651480479266961587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9090509100986986177974391 13635763651480479266961587)
      ·
        refine ⟨20453645477220718900442381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13635763651480479266961587 20453645477220718900442381)
        ·
          refine ⟨7670117053957769587665893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20453645477220718900442381 7670117053957769587665893)
          ·
            refine ⟨1438146947617081797687355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7670117053957769587665893 1438146947617081797687355)
            ·
              refine ⟨2157220421425622696531033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438146947617081797687355 2157220421425622696531033)
              ·
                refine ⟨1617915316069217022398275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2157220421425622696531033 1617915316069217022398275)
                ·
                  refine ⟨2426872974103825533597413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617915316069217022398275 2426872974103825533597413)
                  ·
                    refine ⟨455038682644467287549515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2426872974103825533597413 455038682644467287549515)
                    ·
                      rfl

theorem cell22_1329277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_1329277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329277 prefixEnd_1329277 := by exact prefixLift 1329277
  have htrace : WordTrace (prefixWord ++ tailWord_1329277) baseStart_1329277 baseEnd_1329277 := by
    simpa [prefixWord, tailWord_1329277, baseEnd_1329277] using wordTrace_append hprefix tailTrace_1329277
  have hstable : (prefixWord ++ tailWord_1329277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329277).length < 2 ^ (prefixWord ++ tailWord_1329277).sum := by decide
  have hdescent : baseEnd_1329277 < baseStart_1329277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329290 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_1329290 : Nat := 118140960795 + 1329290 * 2 ^ 59
def prefixEnd_1329290 : Nat := 4983230072969 + 3 ^ 40 * 1329290 * 2
def baseEnd_1329290 : Nat := 455043132810139586974475

theorem tailTrace_1329290 : CollatzResearch.WordTrace tailWord_1329290 prefixEnd_1329290 455043132810139586974475 := by
  unfold tailWord_1329290
  simp only [CollatzResearch.WordTrace]
  refine ⟨12120797338554207375688331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32322126236144553001835549 12120797338554207375688331)
  ·
    refine ⟨18181196007831311063532497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12120797338554207375688331 18181196007831311063532497)
    ·
      refine ⟨13635897005873483297649373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18181196007831311063532497 13635897005873483297649373)
      ·
        refine ⟨5113461377202556236618515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13635897005873483297649373 5113461377202556236618515)
        ·
          refine ⟨7670192065803834354927773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5113461377202556236618515 7670192065803834354927773)
          ·
            refine ⟨2876322024676437883097915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7670192065803834354927773 2876322024676437883097915)
            ·
              refine ⟨4314483037014656824646873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2876322024676437883097915 4314483037014656824646873)
              ·
                refine ⟨3235862277760992618485155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4314483037014656824646873 3235862277760992618485155)
                ·
                  refine ⟨4853793416641488927727733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3235862277760992618485155 4853793416641488927727733)
                  ·
                    refine ⟨455043132810139586974475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4853793416641488927727733 455043132810139586974475)
                    ·
                      rfl

theorem cell22_1329290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_1329290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329290 prefixEnd_1329290 := by exact prefixLift 1329290
  have htrace : WordTrace (prefixWord ++ tailWord_1329290) baseStart_1329290 baseEnd_1329290 := by
    simpa [prefixWord, tailWord_1329290, baseEnd_1329290] using wordTrace_append hprefix tailTrace_1329290
  have hstable : (prefixWord ++ tailWord_1329290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329290).length < 2 ^ (prefixWord ++ tailWord_1329290).sum := by decide
  have hdescent : baseEnd_1329290 < baseStart_1329290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329294 : List Nat := [4, 1, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_1329294 : Nat := 118140960795 + 1329294 * 2 ^ 59
def prefixEnd_1329294 : Nat := 4983230072969 + 3 ^ 40 * 1329294 * 2
def baseEnd_1329294 : Nat := 455044502091884909874463

theorem tailTrace_1329294 : CollatzResearch.WordTrace tailWord_1329294 prefixEnd_1329294 455044502091884909874463 := by
  unfold tailWord_1329294
  simp only [CollatzResearch.WordTrace]
  refine ⟨6060416905775292273237367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32322223497468225457265957 6060416905775292273237367)
  ·
    refine ⟨9090625358662938409856051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6060416905775292273237367 9090625358662938409856051)
    ·
      refine ⟨13635938037994407614784077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9090625358662938409856051 13635938037994407614784077)
      ·
        refine ⟨5113476764247902855544029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13635938037994407614784077 5113476764247902855544029)
        ·
          refine ⟨1917553786592963570829011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5113476764247902855544029 1917553786592963570829011)
          ·
            refine ⟨2876330679889445356243517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917553786592963570829011 2876330679889445356243517)
            ·
              refine ⟨1078624004958542008591319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2876330679889445356243517 1078624004958542008591319)
              ·
                refine ⟨1617936007437813012886979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078624004958542008591319 1617936007437813012886979)
                ·
                  refine ⟨2426904011156719519330469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617936007437813012886979 2426904011156719519330469)
                  ·
                    refine ⟨455044502091884909874463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2426904011156719519330469 455044502091884909874463)
                    ·
                      rfl

theorem cell22_1329294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_1329294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329294 prefixEnd_1329294 := by exact prefixLift 1329294
  have htrace : WordTrace (prefixWord ++ tailWord_1329294) baseStart_1329294 baseEnd_1329294 := by
    simpa [prefixWord, tailWord_1329294, baseEnd_1329294] using wordTrace_append hprefix tailTrace_1329294
  have hstable : (prefixWord ++ tailWord_1329294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329294).length < 2 ^ (prefixWord ++ tailWord_1329294).sum := by decide
  have hdescent : baseEnd_1329294 < baseStart_1329294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329303 : List Nat := [1, 1, 3, 3, 4, 10]
def baseStart_1329303 : Nat := 118140960795 + 1329303 * 2 ^ 59
def prefixEnd_1329303 : Nat := 4983230072969 + 3 ^ 40 * 1329303 * 2
def baseEnd_1329303 : Nat := 5617871394763109708635

theorem tailTrace_1329303 : CollatzResearch.WordTrace tailWord_1329303 prefixEnd_1329303 5617871394763109708635 := by
  unfold tailWord_1329303
  simp only [CollatzResearch.WordTrace]
  refine ⟨48483663503169732722976563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32322442335446488481984375 48483663503169732722976563)
  ·
    refine ⟨72725495254754599084464845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48483663503169732722976563 72725495254754599084464845)
    ·
      refine ⟨27272060720532974656674317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72725495254754599084464845 27272060720532974656674317)
      ·
        refine ⟨10227022770199865496252869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27272060720532974656674317 10227022770199865496252869)
        ·
          refine ⟨1917566769412474780547413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10227022770199865496252869 1917566769412474780547413)
          ·
            refine ⟨5617871394763109708635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1917566769412474780547413 5617871394763109708635)
            ·
              rfl

theorem cell22_1329303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 10].length) (baseStart_1329303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329303 prefixEnd_1329303 := by exact prefixLift 1329303
  have htrace : WordTrace (prefixWord ++ tailWord_1329303) baseStart_1329303 baseEnd_1329303 := by
    simpa [prefixWord, tailWord_1329303, baseEnd_1329303] using wordTrace_append hprefix tailTrace_1329303
  have hstable : (prefixWord ++ tailWord_1329303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329303).length < 2 ^ (prefixWord ++ tailWord_1329303).sum := by decide
  have hdescent : baseEnd_1329303 < baseStart_1329303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329309 : List Nat := [1, 4, 2, 1, 1, 5, 2, 2, 4]
def baseStart_1329309 : Nat := 118140960795 + 1329309 * 2 ^ 59
def prefixEnd_1329309 : Nat := 4983230072969 + 3 ^ 40 * 1329309 * 2
def baseEnd_1329309 : Nat := 151683212299476623583139

theorem tailTrace_1329309 : CollatzResearch.WordTrace tailWord_1329309 prefixEnd_1329309 151683212299476623583139 := by
  unfold tailWord_1329309
  simp only [CollatzResearch.WordTrace]
  refine ⟨48483882341147995747694981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32322588227431997165129987 48483882341147995747694981)
  ·
    refine ⟨9090727938965249202692809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48483882341147995747694981 9090727938965249202692809)
    ·
      refine ⟨6818045954223936902019607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9090727938965249202692809 6818045954223936902019607)
      ·
        refine ⟨10227068931335905353029411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6818045954223936902019607 10227068931335905353029411)
        ·
          refine ⟨15340603397003858029544117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10227068931335905353029411 15340603397003858029544117)
          ·
            refine ⟨1438181568469111690269761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15340603397003858029544117 1438181568469111690269761)
            ·
              refine ⟨1078636176351833767702321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1438181568469111690269761 1078636176351833767702321)
              ·
                refine ⟨808977132263875325776741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078636176351833767702321 808977132263875325776741)
                ·
                  refine ⟨151683212299476623583139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 808977132263875325776741 151683212299476623583139)
                  ·
                    rfl

theorem cell22_1329309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_1329309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329309 prefixEnd_1329309 := by exact prefixLift 1329309
  have htrace : WordTrace (prefixWord ++ tailWord_1329309) baseStart_1329309 baseEnd_1329309 := by
    simpa [prefixWord, tailWord_1329309, baseEnd_1329309] using wordTrace_append hprefix tailTrace_1329309
  have hstable : (prefixWord ++ tailWord_1329309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329309).length < 2 ^ (prefixWord ++ tailWord_1329309).sum := by decide
  have hdescent : baseEnd_1329309 < baseStart_1329309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329335 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 5, 3]
def baseStart_1329335 : Nat := 118140960795 + 1329335 * 2 ^ 59
def prefixEnd_1329335 : Nat := 4983230072969 + 3 ^ 40 * 1329335 * 2
def baseEnd_1329335 : Nat := 455058537229774469599337

theorem tailTrace_1329335 : CollatzResearch.WordTrace tailWord_1329335 prefixEnd_1329335 455058537229774469599337 := by
  unfold tailWord_1329335
  simp only [CollatzResearch.WordTrace]
  refine ⟨48484830639053802188141459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32323220426035868125427639 48484830639053802188141459)
  ·
    refine ⟨72727245958580703282212189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48484830639053802188141459 72727245958580703282212189)
    ·
      refine ⟨27272717234467763730829571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72727245958580703282212189 27272717234467763730829571)
      ·
        refine ⟨40909075851701645596244357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27272717234467763730829571 40909075851701645596244357)
        ·
          refine ⟨7670451722194058549295817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40909075851701645596244357 7670451722194058549295817)
          ·
            refine ⟨5752838791645543911971863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7670451722194058549295817 5752838791645543911971863)
            ·
              refine ⟨8629258187468315867957795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5752838791645543911971863 8629258187468315867957795)
              ·
                refine ⟨12943887281202473801936693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8629258187468315867957795 12943887281202473801936693)
                ·
                  refine ⟨1213489432612731918931565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12943887281202473801936693 1213489432612731918931565)
                  ·
                    refine ⟨455058537229774469599337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1213489432612731918931565 455058537229774469599337)
                    ·
                      rfl

theorem cell22_1329335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_1329335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329335 prefixEnd_1329335 := by exact prefixLift 1329335
  have htrace : WordTrace (prefixWord ++ tailWord_1329335) baseStart_1329335 baseEnd_1329335 := by
    simpa [prefixWord, tailWord_1329335, baseEnd_1329335] using wordTrace_append hprefix tailTrace_1329335
  have hstable : (prefixWord ++ tailWord_1329335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329335).length < 2 ^ (prefixWord ++ tailWord_1329335).sum := by decide
  have hdescent : baseEnd_1329335 < baseStart_1329335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329504 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 3, 3]
def baseStart_1329504 : Nat := 118140960795 + 1329504 * 2 ^ 59
def prefixEnd_1329504 : Nat := 4983230072969 + 3 ^ 40 * 1329504 * 2
def baseEnd_1329504 : Nat := 455116389383514362123819

theorem tailTrace_1329504 : CollatzResearch.WordTrace tailWord_1329504 prefixEnd_1329504 455116389383514362123819 := by
  unfold tailWord_1329504
  simp only [CollatzResearch.WordTrace]
  refine ⟨24245497287720772025521783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32327329716961029367362377 24245497287720772025521783)
  ·
    refine ⟨36368245931581158038282675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24245497287720772025521783 36368245931581158038282675)
    ·
      refine ⟨54552368897371737057424013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36368245931581158038282675 54552368897371737057424013)
      ·
        refine ⟨20457138336514401396534005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54552368897371737057424013 20457138336514401396534005)
        ·
          refine ⟨1917856719048225130925063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20457138336514401396534005 1917856719048225130925063)
          ·
            refine ⟨2876785078572337696387595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917856719048225130925063 2876785078572337696387595)
            ·
              refine ⟨4315177617858506544581393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2876785078572337696387595 4315177617858506544581393)
              ·
                refine ⟨3236383213393879908436045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4315177617858506544581393 3236383213393879908436045)
                ·
                  refine ⟨1213643705022704965663517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3236383213393879908436045 1213643705022704965663517)
                  ·
                    refine ⟨455116389383514362123819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1213643705022704965663517 455116389383514362123819)
                    ·
                      rfl

theorem cell22_1329504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 3, 3].length) (baseStart_1329504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329504 prefixEnd_1329504 := by exact prefixLift 1329504
  have htrace : WordTrace (prefixWord ++ tailWord_1329504) baseStart_1329504 baseEnd_1329504 := by
    simpa [prefixWord, tailWord_1329504, baseEnd_1329504] using wordTrace_append hprefix tailTrace_1329504
  have hstable : (prefixWord ++ tailWord_1329504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329504).length < 2 ^ (prefixWord ++ tailWord_1329504).sum := by decide
  have hdescent : baseEnd_1329504 < baseStart_1329504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329538 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1329538 : Nat := 118140960795 + 1329538 * 2 ^ 59
def prefixEnd_1329538 : Nat := 4983230072969 + 3 ^ 40 * 1329538 * 2
def baseEnd_1329538 : Nat := 455128028278349606773715

theorem tailTrace_1329538 : CollatzResearch.WordTrace tailWord_1329538 prefixEnd_1329538 455128028278349606773715 := by
  unfold tailWord_1329538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12123058664329591964445317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32328156438212245238520845 12123058664329591964445317)
  ·
    refine ⟨2273073499561798493333497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12123058664329591964445317 2273073499561798493333497)
    ·
      refine ⟨1704805124671348870000123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2273073499561798493333497 1704805124671348870000123)
      ·
        refine ⟨2557207687007023305000185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1704805124671348870000123 2557207687007023305000185)
        ·
          refine ⟨1917905765255267478750139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2557207687007023305000185 1917905765255267478750139)
          ·
            refine ⟨2876858647882901218125209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917905765255267478750139 2876858647882901218125209)
            ·
              refine ⟨2157643985912175913593907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2876858647882901218125209 2157643985912175913593907)
              ·
                refine ⟨3236465978868263870390861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2157643985912175913593907 3236465978868263870390861)
                ·
                  refine ⟨1213674742075598951396573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3236465978868263870390861 1213674742075598951396573)
                  ·
                    refine ⟨455128028278349606773715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1213674742075598951396573 455128028278349606773715)
                    ·
                      rfl

theorem cell22_1329538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1329538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329538 prefixEnd_1329538 := by exact prefixLift 1329538
  have htrace : WordTrace (prefixWord ++ tailWord_1329538) baseStart_1329538 baseEnd_1329538 := by
    simpa [prefixWord, tailWord_1329538, baseEnd_1329538] using wordTrace_append hprefix tailTrace_1329538
  have hstable : (prefixWord ++ tailWord_1329538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329538).length < 2 ^ (prefixWord ++ tailWord_1329538).sum := by decide
  have hdescent : baseEnd_1329538 < baseStart_1329538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329562 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 6]
def baseStart_1329562 : Nat := 118140960795 + 1329562 * 2 ^ 59
def prefixEnd_1329562 : Nat := 4983230072969 + 3 ^ 40 * 1329562 * 2
def baseEnd_1329562 : Nat := 151712081322940514724547

theorem tailTrace_1329562 : CollatzResearch.WordTrace tailWord_1329562 prefixEnd_1329562 151712081322940514724547 := by
  unfold tailWord_1329562
  simp only [CollatzResearch.WordTrace]
  refine ⟨12123277502307854989163735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32328740006154279971103293 12123277502307854989163735)
  ·
    refine ⟨18184916253461782483745603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12123277502307854989163735 18184916253461782483745603)
    ·
      refine ⟨27277374380192673725618405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18184916253461782483745603 27277374380192673725618405)
      ·
        refine ⟨5114507696286126323553451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27277374380192673725618405 5114507696286126323553451)
        ·
          refine ⟨7671761544429189485330177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5114507696286126323553451 7671761544429189485330177)
          ·
            refine ⟨5753821158321892113997633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7671761544429189485330177 5753821158321892113997633)
            ·
              refine ⟨4315365868741419085498225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5753821158321892113997633 4315365868741419085498225)
              ·
                refine ⟨3236524401556064314123669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4315365868741419085498225 3236524401556064314123669)
                ·
                  refine ⟨151712081322940514724547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3236524401556064314123669 151712081322940514724547)
                  ·
                    rfl

theorem cell22_1329562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_1329562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329562 prefixEnd_1329562 := by exact prefixLift 1329562
  have htrace : WordTrace (prefixWord ++ tailWord_1329562) baseStart_1329562 baseEnd_1329562 := by
    simpa [prefixWord, tailWord_1329562, baseEnd_1329562] using wordTrace_append hprefix tailTrace_1329562
  have hstable : (prefixWord ++ tailWord_1329562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329562).length < 2 ^ (prefixWord ++ tailWord_1329562).sum := by decide
  have hdescent : baseEnd_1329562 < baseStart_1329562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329607 : List Nat := [1, 1, 4, 1, 1, 5, 2, 7]
def baseStart_1329607 : Nat := 118140960795 + 1329607 * 2 ^ 59
def prefixEnd_1329607 : Nat := 4983230072969 + 3 ^ 40 * 1329607 * 2
def baseEnd_1329607 : Nat := 50572405376495158533167

theorem tailTrace_1329607 : CollatzResearch.WordTrace tailWord_1329607 prefixEnd_1329607 50572405376495158533167 := by
  unfold tailWord_1329607
  simp only [CollatzResearch.WordTrace]
  refine ⟨48494751294068392642043075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32329834196045595094695383 48494751294068392642043075)
  ·
    refine ⟨72742126941102588963064613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48494751294068392642043075 72742126941102588963064613)
    ·
      refine ⟨13639148801456735430574615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72742126941102588963064613 13639148801456735430574615)
      ·
        refine ⟨20458723202185103145861923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13639148801456735430574615 20458723202185103145861923)
        ·
          refine ⟨30688084803277654718792885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20458723202185103145861923 30688084803277654718792885)
          ·
            refine ⟨2877007950307280129886833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30688084803277654718792885 2877007950307280129886833)
            ·
              refine ⟨2157755962730460097415125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2877007950307280129886833 2157755962730460097415125)
              ·
                refine ⟨50572405376495158533167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2157755962730460097415125 50572405376495158533167)
                ·
                  rfl

theorem cell22_1329607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 7].length) (baseStart_1329607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329607 prefixEnd_1329607 := by exact prefixLift 1329607
  have htrace : WordTrace (prefixWord ++ tailWord_1329607) baseStart_1329607 baseEnd_1329607 := by
    simpa [prefixWord, tailWord_1329607, baseEnd_1329607] using wordTrace_append hprefix tailTrace_1329607
  have hstable : (prefixWord ++ tailWord_1329607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329607).length < 2 ^ (prefixWord ++ tailWord_1329607).sum := by decide
  have hdescent : baseEnd_1329607 < baseStart_1329607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329656 : List Nat := [2, 1, 2, 1, 1, 4, 3, 4, 1, 3]
def baseStart_1329656 : Nat := 118140960795 + 1329656 * 2 ^ 59
def prefixEnd_1329656 : Nat := 4983230072969 + 3 ^ 40 * 1329656 * 2
def baseEnd_1329656 : Nat := 455168422089836632323353

theorem tailTrace_1329656 : CollatzResearch.WordTrace tailWord_1329656 prefixEnd_1329656 455168422089836632323353 := by
  unfold tailWord_1329656
  simp only [CollatzResearch.WordTrace]
  refine ⟨24248269235445437005288411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32331025647260582673717881 24248269235445437005288411)
  ·
    refine ⟨36372403853168155507932617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24248269235445437005288411 36372403853168155507932617)
    ·
      refine ⟨27279302889876116630949463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36372403853168155507932617 27279302889876116630949463)
      ·
        refine ⟨40918954334814174946424195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27279302889876116630949463 40918954334814174946424195)
        ·
          refine ⟨61378431502221262419636293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40918954334814174946424195 61378431502221262419636293)
          ·
            refine ⟨11508455906666486703681805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61378431502221262419636293 11508455906666486703681805)
            ·
              refine ⟨4315670964999932513880677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11508455906666486703681805 4315670964999932513880677)
              ·
                refine ⟨809188305937487346352627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4315670964999932513880677 809188305937487346352627)
                ·
                  refine ⟨1213782458906231019528941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 809188305937487346352627 1213782458906231019528941)
                  ·
                    refine ⟨455168422089836632323353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1213782458906231019528941 455168422089836632323353)
                    ·
                      rfl

theorem cell22_1329656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_1329656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329656 prefixEnd_1329656 := by exact prefixLift 1329656
  have htrace : WordTrace (prefixWord ++ tailWord_1329656) baseStart_1329656 baseEnd_1329656 := by
    simpa [prefixWord, tailWord_1329656, baseEnd_1329656] using wordTrace_append hprefix tailTrace_1329656
  have hstable : (prefixWord ++ tailWord_1329656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329656).length < 2 ^ (prefixWord ++ tailWord_1329656).sum := by decide
  have hdescent : baseEnd_1329656 < baseStart_1329656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329667 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 2, 5]
def baseStart_1329667 : Nat := 118140960795 + 1329667 * 2 ^ 59
def prefixEnd_1329667 : Nat := 4983230072969 + 3 ^ 40 * 1329667 * 2
def baseEnd_1329667 : Nat := 455172187614636270298319

theorem tailTrace_1329667 : CollatzResearch.WordTrace tailWord_1329667 prefixEnd_1329667 455172187614636270298319 := by
  unfold tailWord_1329667
  simp only [CollatzResearch.WordTrace]
  refine ⟨48496939673851022889227255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32331293115900681926151503 48496939673851022889227255)
  ·
    refine ⟨72745409510776534333840883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48496939673851022889227255 72745409510776534333840883)
    ·
      refine ⟨109118114266164801500761325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72745409510776534333840883 109118114266164801500761325)
      ·
        refine ⟨40919292849811800562785497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109118114266164801500761325 40919292849811800562785497)
        ·
          refine ⟨30689469637358850422089123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40919292849811800562785497 30689469637358850422089123)
          ·
            refine ⟨46034204456038275633133685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30689469637358850422089123 46034204456038275633133685)
            ·
              refine ⟨4315706667753588340606283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46034204456038275633133685 4315706667753588340606283)
              ·
                refine ⟨6473560001630382510909425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4315706667753588340606283 6473560001630382510909425)
                ·
                  refine ⟨4855170001222786883182069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6473560001630382510909425 4855170001222786883182069)
                  ·
                    refine ⟨455172187614636270298319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4855170001222786883182069 455172187614636270298319)
                    ·
                      rfl

theorem cell22_1329667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 5].length) (baseStart_1329667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329667 prefixEnd_1329667 := by exact prefixLift 1329667
  have htrace : WordTrace (prefixWord ++ tailWord_1329667) baseStart_1329667 baseEnd_1329667 := by
    simpa [prefixWord, tailWord_1329667, baseEnd_1329667] using wordTrace_append hprefix tailTrace_1329667
  have hstable : (prefixWord ++ tailWord_1329667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329667).length < 2 ^ (prefixWord ++ tailWord_1329667).sum := by decide
  have hdescent : baseEnd_1329667 < baseStart_1329667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329697 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 8]
def baseStart_1329697 : Nat := 118140960795 + 1329697 * 2 ^ 59
def prefixEnd_1329697 : Nat := 4983230072969 + 3 ^ 40 * 1329697 * 2
def baseEnd_1329697 : Nat := 151727485742575397349409

theorem tailTrace_1329697 : CollatzResearch.WordTrace tailWord_1329697 prefixEnd_1329697 151727485742575397349409 := by
  unfold tailWord_1329697
  simp only [CollatzResearch.WordTrace]
  refine ⟨48498033863742338012819345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32332022575828225341879563 48498033863742338012819345)
  ·
    refine ⟨36373525397806753509614509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48498033863742338012819345 36373525397806753509614509)
    ·
      refine ⟨13640072024177532566105441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36373525397806753509614509 13640072024177532566105441)
      ·
        refine ⟨10230054018133149424579081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13640072024177532566105441 10230054018133149424579081)
        ·
          refine ⟨7672540513599862068434311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10230054018133149424579081 7672540513599862068434311)
          ·
            refine ⟨11508810770399793102651467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7672540513599862068434311 11508810770399793102651467)
            ·
              refine ⟨17263216155599689653977201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11508810770399793102651467 17263216155599689653977201)
              ·
                refine ⟨12947412116699767240482901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17263216155599689653977201 12947412116699767240482901)
                ·
                  refine ⟨151727485742575397349409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12947412116699767240482901 151727485742575397349409)
                  ·
                    rfl

theorem cell22_1329697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_1329697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329697 prefixEnd_1329697 := by exact prefixLift 1329697
  have htrace : WordTrace (prefixWord ++ tailWord_1329697) baseStart_1329697 baseEnd_1329697 := by
    simpa [prefixWord, tailWord_1329697, baseEnd_1329697] using wordTrace_append hprefix tailTrace_1329697
  have hstable : (prefixWord ++ tailWord_1329697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329697).length < 2 ^ (prefixWord ++ tailWord_1329697).sum := by decide
  have hdescent : baseEnd_1329697 < baseStart_1329697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329712 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 3, 5]
def baseStart_1329712 : Nat := 118140960795 + 1329712 * 2 ^ 59
def prefixEnd_1329712 : Nat := 4983230072969 + 3 ^ 40 * 1329712 * 2
def baseEnd_1329712 : Nat := 455187592034271152923181

theorem tailTrace_1329712 : CollatzResearch.WordTrace tailWord_1329712 prefixEnd_1329712 455187592034271152923181 := by
  unfold tailWord_1329712
  simp only [CollatzResearch.WordTrace]
  refine ⟨24249290479343997787307695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32332387305791997049743593 24249290479343997787307695)
  ·
    refine ⟨36373935719015996680961543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24249290479343997787307695 36373935719015996680961543)
    ·
      refine ⟨54560903578523995021442315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36373935719015996680961543 54560903578523995021442315)
      ·
        refine ⟨81841355367785992532163473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54560903578523995021442315 81841355367785992532163473)
        ·
          refine ⟨61381016525839494399122605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81841355367785992532163473 61381016525839494399122605)
          ·
            refine ⟨23017881197189810399670977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61381016525839494399122605 23017881197189810399670977)
            ·
              refine ⟨17263410897892357799753233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23017881197189810399670977 17263410897892357799753233)
              ·
                refine ⟨12947558173419268349814925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17263410897892357799753233 12947558173419268349814925)
                ·
                  refine ⟨4855334315032225631180597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12947558173419268349814925 4855334315032225631180597)
                  ·
                    refine ⟨455187592034271152923181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4855334315032225631180597 455187592034271152923181)
                    ·
                      rfl

theorem cell22_1329712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_1329712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329712 prefixEnd_1329712 := by exact prefixLift 1329712
  have htrace : WordTrace (prefixWord ++ tailWord_1329712) baseStart_1329712 baseEnd_1329712 := by
    simpa [prefixWord, tailWord_1329712, baseEnd_1329712] using wordTrace_append hprefix tailTrace_1329712
  have hstable : (prefixWord ++ tailWord_1329712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329712).length < 2 ^ (prefixWord ++ tailWord_1329712).sum := by decide
  have hdescent : baseEnd_1329712 < baseStart_1329712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329727 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 3, 6]
def baseStart_1329727 : Nat := 118140960795 + 1329727 * 2 ^ 59
def prefixEnd_1329727 : Nat := 4983230072969 + 3 ^ 40 * 1329727 * 2
def baseEnd_1329727 : Nat := 455192726840816113798135

theorem tailTrace_1329727 : CollatzResearch.WordTrace tailWord_1329727 prefixEnd_1329727 455192726840816113798135 := by
  unfold tailWord_1329727
  simp only [CollatzResearch.WordTrace]
  refine ⟨48499128053633653136411435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32332752035755768757607623 48499128053633653136411435)
  ·
    refine ⟨72748692080450479704617153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48499128053633653136411435 72748692080450479704617153)
    ·
      refine ⟨54561519060337859778462865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72748692080450479704617153 54561519060337859778462865)
      ·
        refine ⟨40921139295253394833847149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54561519060337859778462865 40921139295253394833847149)
        ·
          refine ⟨15345427235720023062692681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40921139295253394833847149 15345427235720023062692681)
          ·
            refine ⟨11509070426790017297019511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15345427235720023062692681 11509070426790017297019511)
            ·
              refine ⟨17263605640185025945529267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11509070426790017297019511 17263605640185025945529267)
              ·
                refine ⟨25895408460277538918293901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17263605640185025945529267 25895408460277538918293901)
                ·
                  refine ⟨9710778172604077094360213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25895408460277538918293901 9710778172604077094360213)
                  ·
                    refine ⟨455192726840816113798135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9710778172604077094360213 455192726840816113798135)
                    ·
                      rfl

theorem cell22_1329727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_1329727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329727 prefixEnd_1329727 := by exact prefixLift 1329727
  have htrace : WordTrace (prefixWord ++ tailWord_1329727) baseStart_1329727 baseEnd_1329727 := by
    simpa [prefixWord, tailWord_1329727, baseEnd_1329727] using wordTrace_append hprefix tailTrace_1329727
  have hstable : (prefixWord ++ tailWord_1329727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329727).length < 2 ^ (prefixWord ++ tailWord_1329727).sum := by decide
  have hdescent : baseEnd_1329727 < baseStart_1329727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329748 : List Nat := [2, 4, 1, 1, 1, 5, 1, 3, 4]
def baseStart_1329748 : Nat := 118140960795 + 1329748 * 2 ^ 59
def prefixEnd_1329748 : Nat := 4983230072969 + 3 ^ 40 * 1329748 * 2
def baseEnd_1329748 : Nat := 151733305189993019674357

theorem tailTrace_1329748 : CollatzResearch.WordTrace tailWord_1329748 prefixEnd_1329748 151733305189993019674357 := by
  unfold tailWord_1329748
  simp only [CollatzResearch.WordTrace]
  refine ⟨24249946993278786861462949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32333262657705049148617265 24249946993278786861462949)
  ·
    refine ⟨4546865061239772536524303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24249946993278786861462949 4546865061239772536524303)
    ·
      refine ⟨6820297591859658804786455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4546865061239772536524303 6820297591859658804786455)
      ·
        refine ⟨10230446387789488207179683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6820297591859658804786455 10230446387789488207179683)
        ·
          refine ⟨15345669581684232310769525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10230446387789488207179683 15345669581684232310769525)
          ·
            refine ⟨1438656523282896779134643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15345669581684232310769525 1438656523282896779134643)
            ·
              refine ⟨2157984784924345168701965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438656523282896779134643 2157984784924345168701965)
              ·
                refine ⟨809244294346629438263237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2157984784924345168701965 809244294346629438263237)
                ·
                  refine ⟨151733305189993019674357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 809244294346629438263237 151733305189993019674357)
                  ·
                    rfl

theorem cell22_1329748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_1329748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329748 prefixEnd_1329748 := by exact prefixLift 1329748
  have htrace : WordTrace (prefixWord ++ tailWord_1329748) baseStart_1329748 baseEnd_1329748 := by
    simpa [prefixWord, tailWord_1329748, baseEnd_1329748] using wordTrace_append hprefix tailTrace_1329748
  have hstable : (prefixWord ++ tailWord_1329748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329748).length < 2 ^ (prefixWord ++ tailWord_1329748).sum := by decide
  have hdescent : baseEnd_1329748 < baseStart_1329748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329787 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 9]
def baseStart_1329787 : Nat := 118140960795 + 1329787 * 2 ^ 59
def prefixEnd_1329787 : Nat := 4983230072969 + 3 ^ 40 * 1329787 * 2
def baseEnd_1329787 : Nat := 151737755355665319099317

theorem tailTrace_1329787 : CollatzResearch.WordTrace tailWord_1329787 prefixEnd_1329787 151737755355665319099317 := by
  unfold tailWord_1329787
  simp only [CollatzResearch.WordTrace]
  refine ⟨48501316433416283383595615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32334210955610855589063743 48501316433416283383595615)
  ·
    refine ⟨72751974650124425075393423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48501316433416283383595615 72751974650124425075393423)
    ·
      refine ⟨109127961975186637613090135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72751974650124425075393423 109127961975186637613090135)
      ·
        refine ⟨163691942962779956419635203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109127961975186637613090135 163691942962779956419635203)
        ·
          refine ⟨245537914444169934629452805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163691942962779956419635203 245537914444169934629452805)
          ·
            refine ⟨46038358958281862743022401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245537914444169934629452805 46038358958281862743022401)
            ·
              refine ⟨34528769218711397057266801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46038358958281862743022401 34528769218711397057266801)
              ·
                refine ⟨25896576914033547792950101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34528769218711397057266801 25896576914033547792950101)
                ·
                  refine ⟨151737755355665319099317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25896576914033547792950101 151737755355665319099317)
                  ·
                    rfl

theorem cell22_1329787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 9].length) (baseStart_1329787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329787 prefixEnd_1329787 := by exact prefixLift 1329787
  have htrace : WordTrace (prefixWord ++ tailWord_1329787) baseStart_1329787 baseEnd_1329787 := by
    simpa [prefixWord, tailWord_1329787, baseEnd_1329787] using wordTrace_append hprefix tailTrace_1329787
  have hstable : (prefixWord ++ tailWord_1329787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329787).length < 2 ^ (prefixWord ++ tailWord_1329787).sum := by decide
  have hdescent : baseEnd_1329787 < baseStart_1329787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329825 : List Nat := [1, 2, 3, 3, 3, 1, 1, 4, 1, 3]
def baseStart_1329825 : Nat := 118140960795 + 1329825 * 2 ^ 59
def prefixEnd_1329825 : Nat := 4983230072969 + 3 ^ 40 * 1329825 * 2
def baseEnd_1329825 : Nat := 455226274243576524847835

theorem tailTrace_1329825 : CollatzResearch.WordTrace tailWord_1329825 prefixEnd_1329825 455226274243576524847835 := by
  unfold tailWord_1329825
  simp only [CollatzResearch.WordTrace]
  refine ⟨48502702407278615873478929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32335134938185743915652619 48502702407278615873478929)
  ·
    refine ⟨36377026805458961905109197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48502702407278615873478929 36377026805458961905109197)
    ·
      refine ⟨13641385052047110714415949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36377026805458961905109197 13641385052047110714415949)
      ·
        refine ⟨5115519394517666517905981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13641385052047110714415949 5115519394517666517905981)
        ·
          refine ⟨1918319772944124944214743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5115519394517666517905981 1918319772944124944214743)
          ·
            refine ⟨2877479659416187416322115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918319772944124944214743 2877479659416187416322115)
            ·
              refine ⟨4316219489124281124483173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877479659416187416322115 4316219489124281124483173)
              ·
                refine ⟨809291154210802710840595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4316219489124281124483173 809291154210802710840595)
                ·
                  refine ⟨1213936731316204066260893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 809291154210802710840595 1213936731316204066260893)
                  ·
                    refine ⟨455226274243576524847835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1213936731316204066260893 455226274243576524847835)
                    ·
                      rfl

theorem cell22_1329825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_1329825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329825 prefixEnd_1329825 := by exact prefixLift 1329825
  have htrace : WordTrace (prefixWord ++ tailWord_1329825) baseStart_1329825 baseEnd_1329825 := by
    simpa [prefixWord, tailWord_1329825, baseEnd_1329825] using wordTrace_append hprefix tailTrace_1329825
  have hstable : (prefixWord ++ tailWord_1329825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329825).length < 2 ^ (prefixWord ++ tailWord_1329825).sum := by decide
  have hdescent : baseEnd_1329825 < baseStart_1329825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329838 : List Nat := [4, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_1329838 : Nat := 118140960795 + 1329838 * 2 ^ 59
def prefixEnd_1329838 : Nat := 4983230072969 + 3 ^ 40 * 1329838 * 2
def baseEnd_1329838 : Nat := 151743574803082941424265

theorem tailTrace_1329838 : CollatzResearch.WordTrace tailWord_1329838 prefixEnd_1329838 151743574803082941424265 := by
  unfold tailWord_1329838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6062897069528939886712771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32335451037487679395801445 6062897069528939886712771)
  ·
    refine ⟨9094345604293409830069157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6062897069528939886712771 9094345604293409830069157)
    ·
      refine ⟨1705189800805014343137967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9094345604293409830069157 1705189800805014343137967)
      ·
        refine ⟨2557784701207521514706951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705189800805014343137967 2557784701207521514706951)
        ·
          refine ⟨3836677051811282272060427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2557784701207521514706951 3836677051811282272060427)
          ·
            refine ⟨5755015577716923408090641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3836677051811282272060427 5755015577716923408090641)
            ·
              refine ⟨4316261683287692556067981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5755015577716923408090641 4316261683287692556067981)
              ·
                refine ⟨1618598131232884708525493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4316261683287692556067981 1618598131232884708525493)
                ·
                  refine ⟨151743574803082941424265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1618598131232884708525493 151743574803082941424265)
                  ·
                    rfl

theorem cell22_1329838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_1329838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329838 prefixEnd_1329838 := by exact prefixLift 1329838
  have htrace : WordTrace (prefixWord ++ tailWord_1329838) baseStart_1329838 baseEnd_1329838 := by
    simpa [prefixWord, tailWord_1329838, baseEnd_1329838] using wordTrace_append hprefix tailTrace_1329838
  have hstable : (prefixWord ++ tailWord_1329838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329838).length < 2 ^ (prefixWord ++ tailWord_1329838).sum := by decide
  have hdescent : baseEnd_1329838 < baseStart_1329838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329868 : List Nat := [2, 2, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_1329868 : Nat := 118140960795 + 1329868 * 2 ^ 59
def prefixEnd_1329868 : Nat := 4983230072969 + 3 ^ 40 * 1329868 * 2
def baseEnd_1329868 : Nat := 455240994022338746022703

theorem tailTrace_1329868 : CollatzResearch.WordTrace tailWord_1329868 prefixEnd_1329868 455240994022338746022703 := by
  unfold tailWord_1329868
  simp only [CollatzResearch.WordTrace]
  refine ⟨24252135373061417108647129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32336180497415222811529505 24252135373061417108647129)
  ·
    refine ⟨18189101529796062831485347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24252135373061417108647129 18189101529796062831485347)
    ·
      refine ⟨27283652294694094247228021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18189101529796062831485347 27283652294694094247228021)
      ·
        refine ⟨2557842402627571335677627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27283652294694094247228021 2557842402627571335677627)
        ·
          refine ⟨3836763603941357003516441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2557842402627571335677627 3836763603941357003516441)
          ·
            refine ⟨2877572702956017752637331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3836763603941357003516441 2877572702956017752637331)
            ·
              refine ⟨4316359054434026628955997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877572702956017752637331 4316359054434026628955997)
              ·
                refine ⟨1618634645412759985858499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4316359054434026628955997 1618634645412759985858499)
                ·
                  refine ⟨2427951968119139978787749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618634645412759985858499 2427951968119139978787749)
                  ·
                    refine ⟨455240994022338746022703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2427951968119139978787749 455240994022338746022703)
                    ·
                      rfl

theorem cell22_1329868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_1329868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329868 prefixEnd_1329868 := by exact prefixLift 1329868
  have htrace : WordTrace (prefixWord ++ tailWord_1329868) baseStart_1329868 baseEnd_1329868 := by
    simpa [prefixWord, tailWord_1329868, baseEnd_1329868] using wordTrace_append hprefix tailTrace_1329868
  have hstable : (prefixWord ++ tailWord_1329868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329868).length < 2 ^ (prefixWord ++ tailWord_1329868).sum := by decide
  have hdescent : baseEnd_1329868 < baseStart_1329868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329881 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 4, 3]
def baseStart_1329881 : Nat := 118140960795 + 1329881 * 2 ^ 59
def prefixEnd_1329881 : Nat := 4983230072969 + 3 ^ 40 * 1329881 * 2
def baseEnd_1329881 : Nat := 455245444188011045447663

theorem tailTrace_1329881 : CollatzResearch.WordTrace tailWord_1329881 prefixEnd_1329881 455245444188011045447663 := by
  unfold tailWord_1329881
  simp only [CollatzResearch.WordTrace]
  refine ⟨48504744895075737437517497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32336496596717158291678331 48504744895075737437517497)
  ·
    refine ⟨36378558671306803078138123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48504744895075737437517497 36378558671306803078138123)
    ·
      refine ⟨54567838006960204617207185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36378558671306803078138123 54567838006960204617207185)
      ·
        refine ⟨40925878505220153462905389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54567838006960204617207185 40925878505220153462905389)
        ·
          refine ⟨15347204439457557548589521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40925878505220153462905389 15347204439457557548589521)
          ·
            refine ⟨11510403329593168161442141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15347204439457557548589521 11510403329593168161442141)
            ·
              refine ⟨4316401248597438060540803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11510403329593168161442141 4316401248597438060540803)
              ·
                refine ⟨6474601872896157090811205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4316401248597438060540803 6474601872896157090811205)
                ·
                  refine ⟨1213987851168029454527101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6474601872896157090811205 1213987851168029454527101)
                  ·
                    refine ⟨455245444188011045447663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1213987851168029454527101 455245444188011045447663)
                    ·
                      rfl

theorem cell22_1329881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 3].length) (baseStart_1329881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329881 prefixEnd_1329881 := by exact prefixLift 1329881
  have htrace : WordTrace (prefixWord ++ tailWord_1329881) baseStart_1329881 baseEnd_1329881 := by
    simpa [prefixWord, tailWord_1329881, baseEnd_1329881] using wordTrace_append hprefix tailTrace_1329881
  have hstable : (prefixWord ++ tailWord_1329881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329881).length < 2 ^ (prefixWord ++ tailWord_1329881).sum := by decide
  have hdescent : baseEnd_1329881 < baseStart_1329881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329939 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 7]
def baseStart_1329939 : Nat := 118140960795 + 1329939 * 2 ^ 59
def prefixEnd_1329939 : Nat := 4983230072969 + 3 ^ 40 * 1329939 * 2
def baseEnd_1329939 : Nat := 151755099591106075832495

theorem tailTrace_1329939 : CollatzResearch.WordTrace tailWord_1329939 prefixEnd_1329939 151755099591106075832495 := by
  unfold tailWord_1329939
  simp only [CollatzResearch.WordTrace]
  refine ⟨48506860328865613343128871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32337906885910408895419247 48506860328865613343128871)
  ·
    refine ⟨72760290493298420014693307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48506860328865613343128871 72760290493298420014693307)
    ·
      refine ⟨109140435739947630022039961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72760290493298420014693307 109140435739947630022039961)
      ·
        refine ⟨81855326804960722516529971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109140435739947630022039961 81855326804960722516529971)
        ·
          refine ⟨122782990207441083774794957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81855326804960722516529971 122782990207441083774794957)
          ·
            refine ⟨46043621327790406415548109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122782990207441083774794957 46043621327790406415548109)
            ·
              refine ⟨17266357997921402405830541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46043621327790406415548109 17266357997921402405830541)
              ·
                refine ⟨6474884249220525902186453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17266357997921402405830541 6474884249220525902186453)
                ·
                  refine ⟨151755099591106075832495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6474884249220525902186453 151755099591106075832495)
                  ·
                    rfl

theorem cell22_1329939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 7].length) (baseStart_1329939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329939 prefixEnd_1329939 := by exact prefixLift 1329939
  have htrace : WordTrace (prefixWord ++ tailWord_1329939) baseStart_1329939 baseEnd_1329939 := by
    simpa [prefixWord, tailWord_1329939, baseEnd_1329939] using wordTrace_append hprefix tailTrace_1329939
  have hstable : (prefixWord ++ tailWord_1329939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329939).length < 2 ^ (prefixWord ++ tailWord_1329939).sum := by decide
  have hdescent : baseEnd_1329939 < baseStart_1329939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329949 : List Nat := [1, 4, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_1329949 : Nat := 118140960795 + 1329949 * 2 ^ 59
def prefixEnd_1329949 : Nat := 4983230072969 + 3 ^ 40 * 1329949 * 2
def baseEnd_1329949 : Nat := 455268721977681534747455

theorem tailTrace_1329949 : CollatzResearch.WordTrace tailWord_1329949 prefixEnd_1329949 455268721977681534747455 := by
  unfold tailWord_1329949
  simp only [CollatzResearch.WordTrace]
  refine ⟨48507225058829385050992901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32338150039219590033995267 48507225058829385050992901)
  ·
    refine ⟨9095104698530509697061169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48507225058829385050992901 9095104698530509697061169)
    ·
      refine ⟨6821328523897882272795877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9095104698530509697061169 6821328523897882272795877)
      ·
        refine ⟨1278999098230852926149227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6821328523897882272795877 1278999098230852926149227)
        ·
          refine ⟨1918498647346279389223841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278999098230852926149227 1918498647346279389223841)
          ·
            refine ⟨1438873985509709541917881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1918498647346279389223841 1438873985509709541917881)
            ·
              refine ⟨1079155489132282156438411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1438873985509709541917881 1079155489132282156438411)
              ·
                refine ⟨1618733233698423234657617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079155489132282156438411 1618733233698423234657617)
                ·
                  refine ⟨1214049925273817425993213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1618733233698423234657617 1214049925273817425993213)
                  ·
                    refine ⟨455268721977681534747455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1214049925273817425993213 455268721977681534747455)
                    ·
                      rfl

theorem cell22_1329949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_1329949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1329949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1329949 prefixEnd_1329949 := by exact prefixLift 1329949
  have htrace : WordTrace (prefixWord ++ tailWord_1329949) baseStart_1329949 baseEnd_1329949 := by
    simpa [prefixWord, tailWord_1329949, baseEnd_1329949] using wordTrace_append hprefix tailTrace_1329949
  have hstable : (prefixWord ++ tailWord_1329949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329949).length < 2 ^ (prefixWord ++ tailWord_1329949).sum := by decide
  have hdescent : baseEnd_1329949 < baseStart_1329949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330037 : List Nat := [1, 3, 4, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1330037 : Nat := 118140960795 + 1330037 * 2 ^ 59
def prefixEnd_1330037 : Nat := 4983230072969 + 3 ^ 40 * 1330037 * 2
def baseEnd_1330037 : Nat := 455298846176078638547185

theorem tailTrace_1330037 : CollatzResearch.WordTrace tailWord_1330037 prefixEnd_1330037 455298846176078638547185 := by
  unfold tailWord_1330037
  simp only [CollatzResearch.WordTrace]
  refine ⟨48510434682510576080196365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32340289788340384053464243 48510434682510576080196365)
  ·
    refine ⟨18191413005941466030073637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48510434682510576080196365 18191413005941466030073637)
    ·
      refine ⟨3410889938614024880638807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18191413005941466030073637 3410889938614024880638807)
      ·
        refine ⟨5116334907921037320958211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3410889938614024880638807 5116334907921037320958211)
        ·
          refine ⟨7674502361881555981437317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5116334907921037320958211 7674502361881555981437317)
          ·
            refine ⟨1438969192852791746519497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7674502361881555981437317 1438969192852791746519497)
            ·
              refine ⟨1079226894639593809889623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1438969192852791746519497 1079226894639593809889623)
              ·
                refine ⟨1618840341959390714834435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079226894639593809889623 1618840341959390714834435)
                ·
                  refine ⟨2428260512939086072251653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618840341959390714834435 2428260512939086072251653)
                  ·
                    refine ⟨455298846176078638547185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2428260512939086072251653 455298846176078638547185)
                    ·
                      rfl

theorem cell22_1330037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1330037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330037 prefixEnd_1330037 := by exact prefixLift 1330037
  have htrace : WordTrace (prefixWord ++ tailWord_1330037) baseStart_1330037 baseEnd_1330037 := by
    simpa [prefixWord, tailWord_1330037, baseEnd_1330037] using wordTrace_append hprefix tailTrace_1330037
  have hstable : (prefixWord ++ tailWord_1330037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330037).length < 2 ^ (prefixWord ++ tailWord_1330037).sum := by decide
  have hdescent : baseEnd_1330037 < baseStart_1330037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330095 : List Nat := [1, 1, 2, 1, 2, 2, 2, 7, 1, 3]
def baseStart_1330095 : Nat := 118140960795 + 1330095 * 2 ^ 59
def prefixEnd_1330095 : Nat := 4983230072969 + 3 ^ 40 * 1330095 * 2
def baseEnd_1330095 : Nat := 455318700761385820597007

theorem tailTrace_1330095 : CollatzResearch.WordTrace tailWord_1330095 prefixEnd_1330095 455318700761385820597007 := by
  unfold tailWord_1330095
  simp only [CollatzResearch.WordTrace]
  refine ⟨48512550116300451985807739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32341700077533634657205159 48512550116300451985807739)
  ·
    refine ⟨72768825174450677978711609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48512550116300451985807739 72768825174450677978711609)
    ·
      refine ⟨54576618880838008484033707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72768825174450677978711609 54576618880838008484033707)
      ·
        refine ⟨81864928321257012726050561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54576618880838008484033707 81864928321257012726050561)
        ·
          refine ⟨61398696240942759544537921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81864928321257012726050561 61398696240942759544537921)
          ·
            refine ⟨46049022180707069658403441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61398696240942759544537921 46049022180707069658403441)
            ·
              refine ⟨34536766635530302243802581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46049022180707069658403441 34536766635530302243802581)
              ·
                refine ⟨809455468020241458839123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 34536766635530302243802581 809455468020241458839123)
                ·
                  refine ⟨1214183202030362188258685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 809455468020241458839123 1214183202030362188258685)
                  ·
                    refine ⟨455318700761385820597007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1214183202030362188258685 455318700761385820597007)
                    ·
                      rfl

theorem cell22_1330095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 1, 3].length) (baseStart_1330095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330095 prefixEnd_1330095 := by exact prefixLift 1330095
  have htrace : WordTrace (prefixWord ++ tailWord_1330095) baseStart_1330095 baseEnd_1330095 := by
    simpa [prefixWord, tailWord_1330095, baseEnd_1330095] using wordTrace_append hprefix tailTrace_1330095
  have hstable : (prefixWord ++ tailWord_1330095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330095).length < 2 ^ (prefixWord ++ tailWord_1330095).sum := by decide
  have hdescent : baseEnd_1330095 < baseStart_1330095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330118 : List Nat := [6, 1, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1330118 : Nat := 118140960795 + 1330118 * 2 ^ 59
def prefixEnd_1330118 : Nat := 4983230072969 + 3 ^ 40 * 1330118 * 2
def baseEnd_1330118 : Nat := 455326574131421427271937

theorem tailTrace_1330118 : CollatzResearch.WordTrace tailWord_1330118 prefixEnd_1330118 455326574131421427271937 := by
  unfold tailWord_1330118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516043406100535216059219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32342259330144751275930005 1516043406100535216059219)
  ·
    refine ⟨2274065109150802824088829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1516043406100535216059219 2274065109150802824088829)
    ·
      refine ⟨852774415931551059033311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2274065109150802824088829 852774415931551059033311)
      ·
        refine ⟨1279161623897326588549967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852774415931551059033311 1279161623897326588549967)
        ·
          refine ⟨1918742435845989882824951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279161623897326588549967 1918742435845989882824951)
          ·
            refine ⟨2878113653768984824237427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918742435845989882824951 2878113653768984824237427)
            ·
              refine ⟨4317170480653477236356141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2878113653768984824237427 4317170480653477236356141)
              ·
                refine ⟨1618938930245053963633553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4317170480653477236356141 1618938930245053963633553)
                ·
                  refine ⟨1214204197683790472725165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1618938930245053963633553 1214204197683790472725165)
                  ·
                    refine ⟨455326574131421427271937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1214204197683790472725165 455326574131421427271937)
                    ·
                      rfl

theorem cell22_1330118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1330118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330118 prefixEnd_1330118 := by exact prefixLift 1330118
  have htrace : WordTrace (prefixWord ++ tailWord_1330118) baseStart_1330118 baseEnd_1330118 := by
    simpa [prefixWord, tailWord_1330118, baseEnd_1330118] using wordTrace_append hprefix tailTrace_1330118
  have hstable : (prefixWord ++ tailWord_1330118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330118).length < 2 ^ (prefixWord ++ tailWord_1330118).sum := by decide
  have hdescent : baseEnd_1330118 < baseStart_1330118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330183 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1330183 : Nat := 118140960795 + 1330183 * 2 ^ 59
def prefixEnd_1330183 : Nat := 4983230072969 + 3 ^ 40 * 1330183 * 2
def baseEnd_1330183 : Nat := 455348824959782924396737

theorem tailTrace_1330183 : CollatzResearch.WordTrace tailWord_1330183 prefixEnd_1330183 455348824959782924396737 := by
  unfold tailWord_1330183
  simp only [CollatzResearch.WordTrace]
  refine ⟨48515759739981643015011203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32343839826654428676674135 48515759739981643015011203)
  ·
    refine ⟨72773639609972464522516805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48515759739981643015011203 72773639609972464522516805)
    ·
      refine ⟨13645057426869837097971901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72773639609972464522516805 13645057426869837097971901)
      ·
        refine ⟨5116896535076188911739463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13645057426869837097971901 5116896535076188911739463)
        ·
          refine ⟨7675344802614283367609195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5116896535076188911739463 7675344802614283367609195)
          ·
            refine ⟨11513017203921425051413793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7675344802614283367609195 11513017203921425051413793)
            ·
              refine ⟨8634762902941068788560345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11513017203921425051413793 8634762902941068788560345)
              ·
                refine ⟨6476072177205801591420259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8634762902941068788560345 6476072177205801591420259)
                ·
                  refine ⟨9714108265808702387130389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6476072177205801591420259 9714108265808702387130389)
                  ·
                    refine ⟨455348824959782924396737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9714108265808702387130389 455348824959782924396737)
                    ·
                      rfl

theorem cell22_1330183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1330183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330183 prefixEnd_1330183 := by exact prefixLift 1330183
  have htrace : WordTrace (prefixWord ++ tailWord_1330183) baseStart_1330183 baseEnd_1330183 := by
    simpa [prefixWord, tailWord_1330183, baseEnd_1330183] using wordTrace_append hprefix tailTrace_1330183
  have hstable : (prefixWord ++ tailWord_1330183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330183).length < 2 ^ (prefixWord ++ tailWord_1330183).sum := by decide
  have hdescent : baseEnd_1330183 < baseStart_1330183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330200 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 2, 4]
def baseStart_1330200 : Nat := 118140960795 + 1330200 * 2 ^ 59
def prefixEnd_1330200 : Nat := 4983230072969 + 3 ^ 40 * 1330200 * 2
def baseEnd_1330200 : Nat := 455354644407200546721685

theorem tailTrace_1330200 : CollatzResearch.WordTrace tailWord_1330200 prefixEnd_1330200 455354644407200546721685 := by
  unfold tailWord_1330200
  simp only [CollatzResearch.WordTrace]
  refine ⟨24258189890460027459190027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32344253187280036612253369 24258189890460027459190027)
  ·
    refine ⟨36387284835690041188785041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24258189890460027459190027 36387284835690041188785041)
    ·
      refine ⟨27290463626767530891588781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36387284835690041188785041 27290463626767530891588781)
      ·
        refine ⟨10233923860037824084345793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27290463626767530891588781 10233923860037824084345793)
        ·
          refine ⟨7675442895028368063259345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10233923860037824084345793 7675442895028368063259345)
          ·
            refine ⟨5756582171271276047444509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7675442895028368063259345 5756582171271276047444509)
            ·
              refine ⟨2158718314226728517791691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5756582171271276047444509 2158718314226728517791691)
              ·
                refine ⟨3238077471340092776687537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158718314226728517791691 3238077471340092776687537)
                ·
                  refine ⟨2428558103505069582515653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3238077471340092776687537 2428558103505069582515653)
                  ·
                    refine ⟨455354644407200546721685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2428558103505069582515653 455354644407200546721685)
                    ·
                      rfl

theorem cell22_1330200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_1330200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330200 prefixEnd_1330200 := by exact prefixLift 1330200
  have htrace : WordTrace (prefixWord ++ tailWord_1330200) baseStart_1330200 baseEnd_1330200 := by
    simpa [prefixWord, tailWord_1330200, baseEnd_1330200] using wordTrace_append hprefix tailTrace_1330200
  have hstable : (prefixWord ++ tailWord_1330200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330200).length < 2 ^ (prefixWord ++ tailWord_1330200).sum := by decide
  have hdescent : baseEnd_1330200 < baseStart_1330200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330215 : List Nat := [1, 1, 7, 1, 1, 2, 9]
def baseStart_1330215 : Nat := 118140960795 + 1330215 * 2 ^ 59
def prefixEnd_1330215 : Nat := 4983230072969 + 3 ^ 40 * 1330215 * 2
def baseEnd_1330215 : Nat := 16865177007916500281357

theorem tailTrace_1330215 : CollatzResearch.WordTrace tailWord_1330215 prefixEnd_1330215 16865177007916500281357 := by
  unfold tailWord_1330215
  simp only [CollatzResearch.WordTrace]
  refine ⟨48516926875865712480176099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32344617917243808320117399 48516926875865712480176099)
  ·
    refine ⟨72775390313798568720264149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48516926875865712480176099 72775390313798568720264149)
    ·
      refine ⟨1705673210479653954381191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 72775390313798568720264149 1705673210479653954381191)
      ·
        refine ⟨2558509815719480931571787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705673210479653954381191 2558509815719480931571787)
        ·
          refine ⟨3837764723579221397357681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558509815719480931571787 3837764723579221397357681)
          ·
            refine ⟨2878323542684416048018261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3837764723579221397357681 2878323542684416048018261)
            ·
              refine ⟨16865177007916500281357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2878323542684416048018261 16865177007916500281357)
              ·
                rfl

theorem cell22_1330215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 9].length) (baseStart_1330215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330215 prefixEnd_1330215 := by exact prefixLift 1330215
  have htrace : WordTrace (prefixWord ++ tailWord_1330215) baseStart_1330215 baseEnd_1330215 := by
    simpa [prefixWord, tailWord_1330215, baseEnd_1330215] using wordTrace_append hprefix tailTrace_1330215
  have hstable : (prefixWord ++ tailWord_1330215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330215).length < 2 ^ (prefixWord ++ tailWord_1330215).sum := by decide
  have hdescent : baseEnd_1330215 < baseStart_1330215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330290 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_1330290 : Nat := 118140960795 + 1330290 * 2 ^ 59
def prefixEnd_1330290 : Nat := 4983230072969 + 3 ^ 40 * 1330290 * 2
def baseEnd_1330290 : Nat := 455385453246470311971409

theorem tailTrace_1330290 : CollatzResearch.WordTrace tailWord_1330290 prefixEnd_1330290 455385453246470311971409 := by
  unfold tailWord_1330290
  simp only [CollatzResearch.WordTrace]
  refine ⟨12129915587648500072289081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32346441567062666859437549 12129915587648500072289081)
  ·
    refine ⟨9097436690736375054216811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12129915587648500072289081 9097436690736375054216811)
    ·
      refine ⟨13646155036104562581325217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9097436690736375054216811 13646155036104562581325217)
      ·
        refine ⟨10234616277078421935993913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13646155036104562581325217 10234616277078421935993913)
        ·
          refine ⟨7675962207808816451995435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10234616277078421935993913 7675962207808816451995435)
          ·
            refine ⟨11513943311713224677993153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7675962207808816451995435 11513943311713224677993153)
            ·
              refine ⟨8635457483784918508494865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11513943311713224677993153 8635457483784918508494865)
              ·
                refine ⟨6476593112838688881371149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8635457483784918508494865 6476593112838688881371149)
                ·
                  refine ⟨2428722417314508330514181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6476593112838688881371149 2428722417314508330514181)
                  ·
                    refine ⟨455385453246470311971409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2428722417314508330514181 455385453246470311971409)
                    ·
                      rfl

theorem cell22_1330290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_1330290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330290 prefixEnd_1330290 := by exact prefixLift 1330290
  have htrace : WordTrace (prefixWord ++ tailWord_1330290) baseStart_1330290 baseEnd_1330290 := by
    simpa [prefixWord, tailWord_1330290, baseEnd_1330290] using wordTrace_append hprefix tailTrace_1330290
  have hstable : (prefixWord ++ tailWord_1330290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330290).length < 2 ^ (prefixWord ++ tailWord_1330290).sum := by decide
  have hdescent : baseEnd_1330290 < baseStart_1330290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330303 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 7, 5]
def baseStart_1330303 : Nat := 118140960795 + 1330303 * 2 ^ 59
def prefixEnd_1330303 : Nat := 4983230072969 + 3 ^ 40 * 1330303 * 2
def baseEnd_1330303 : Nat := 455389903412142611396369

theorem tailTrace_1330303 : CollatzResearch.WordTrace tailWord_1330303 prefixEnd_1330303 455389903412142611396369 := by
  unfold tailWord_1330303
  simp only [CollatzResearch.WordTrace]
  refine ⟨48520136499546903509379563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32346757666364602339586375 48520136499546903509379563)
  ·
    refine ⟨72780204749320355264069345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48520136499546903509379563 72780204749320355264069345)
    ·
      refine ⟨54585153561990266448052009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72780204749320355264069345 54585153561990266448052009)
      ·
        refine ⟨40938865171492699836039007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54585153561990266448052009 40938865171492699836039007)
        ·
          refine ⟨61408297757239049754058511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40938865171492699836039007 61408297757239049754058511)
          ·
            refine ⟨92112446635858574631087767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61408297757239049754058511 92112446635858574631087767)
            ·
              refine ⟨138168669953787861946631651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92112446635858574631087767 138168669953787861946631651)
              ·
                refine ⟨207253004930681792919947477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138168669953787861946631651 207253004930681792919947477)
                ·
                  refine ⟨4857492303062854521561269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 207253004930681792919947477 4857492303062854521561269)
                  ·
                    refine ⟨455389903412142611396369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4857492303062854521561269 455389903412142611396369)
                    ·
                      rfl

theorem cell22_1330303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_1330303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330303 prefixEnd_1330303 := by exact prefixLift 1330303
  have htrace : WordTrace (prefixWord ++ tailWord_1330303) baseStart_1330303 baseEnd_1330303 := by
    simpa [prefixWord, tailWord_1330303, baseEnd_1330303] using wordTrace_append hprefix tailTrace_1330303
  have hstable : (prefixWord ++ tailWord_1330303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330303).length < 2 ^ (prefixWord ++ tailWord_1330303).sum := by decide
  have hdescent : baseEnd_1330303 < baseStart_1330303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330320 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 4, 3]
def baseStart_1330320 : Nat := 118140960795 + 1330320 * 2 ^ 59
def prefixEnd_1330320 : Nat := 4983230072969 + 3 ^ 40 * 1330320 * 2
def baseEnd_1330320 : Nat := 455395722859560233721317

theorem tailTrace_1330320 : CollatzResearch.WordTrace tailWord_1330320 prefixEnd_1330320 455395722859560233721317 := by
  unfold tailWord_1330320
  simp only [CollatzResearch.WordTrace]
  refine ⟨24260378270242657706374207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32347171026990210275165609 24260378270242657706374207)
  ·
    refine ⟨36390567405363986559561311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24260378270242657706374207 36390567405363986559561311)
    ·
      refine ⟨54585851108045979839341967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36390567405363986559561311 54585851108045979839341967)
      ·
        refine ⟨81878776662068969759012951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54585851108045979839341967 81878776662068969759012951)
        ·
          refine ⟨122818164993103454638519427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81878776662068969759012951 122818164993103454638519427)
          ·
            refine ⟨184227247489655181957779141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122818164993103454638519427 184227247489655181957779141)
            ·
              refine ⟨34542608904310346617083589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184227247489655181957779141 34542608904310346617083589)
              ·
                refine ⟨6476739169558189990703173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34542608904310346617083589 6476739169558189990703173)
                ·
                  refine ⟨1214388594292160623256845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6476739169558189990703173 1214388594292160623256845)
                  ·
                    refine ⟨455395722859560233721317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1214388594292160623256845 455395722859560233721317)
                    ·
                      rfl

theorem cell22_1330320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 4, 3].length) (baseStart_1330320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330320 prefixEnd_1330320 := by exact prefixLift 1330320
  have htrace : WordTrace (prefixWord ++ tailWord_1330320) baseStart_1330320 baseEnd_1330320 := by
    simpa [prefixWord, tailWord_1330320, baseEnd_1330320] using wordTrace_append hprefix tailTrace_1330320
  have hstable : (prefixWord ++ tailWord_1330320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330320).length < 2 ^ (prefixWord ++ tailWord_1330320).sum := by decide
  have hdescent : baseEnd_1330320 < baseStart_1330320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330369 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1330369 : Nat := 118140960795 + 1330369 * 2 ^ 59
def prefixEnd_1330369 : Nat := 4983230072969 + 3 ^ 40 * 1330369 * 2
def baseEnd_1330369 : Nat := 455412496560940439246167

theorem tailTrace_1330369 : CollatzResearch.WordTrace tailWord_1330369 prefixEnd_1330369 455412496560940439246167 := by
  unfold tailWord_1330369
  simp only [CollatzResearch.WordTrace]
  refine ⟨48522543717307796781282161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32348362478205197854188107 48522543717307796781282161)
  ·
    refine ⟨36391907787980847585961621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48522543717307796781282161 36391907787980847585961621)
    ·
      refine ⟨1705870677561602230591951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36391907787980847585961621 1705870677561602230591951)
      ·
        refine ⟨2558806016342403345887927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705870677561602230591951 2558806016342403345887927)
        ·
          refine ⟨3838209024513605018831891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558806016342403345887927 3838209024513605018831891)
          ·
            refine ⟨5757313536770407528247837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3838209024513605018831891 5757313536770407528247837)
            ·
              refine ⟨2158992576288902823092939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5757313536770407528247837 2158992576288902823092939)
              ·
                refine ⟨3238488864433354234639409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158992576288902823092939 3238488864433354234639409)
                ·
                  refine ⟨2428866648325015675979557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3238488864433354234639409 2428866648325015675979557)
                  ·
                    refine ⟨455412496560940439246167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2428866648325015675979557 455412496560940439246167)
                    ·
                      rfl

theorem cell22_1330369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1330369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330369 prefixEnd_1330369 := by exact prefixLift 1330369
  have htrace : WordTrace (prefixWord ++ tailWord_1330369) baseStart_1330369 baseEnd_1330369 := by
    simpa [prefixWord, tailWord_1330369, baseEnd_1330369] using wordTrace_append hprefix tailTrace_1330369
  have hstable : (prefixWord ++ tailWord_1330369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330369).length < 2 ^ (prefixWord ++ tailWord_1330369).sum := by decide
  have hdescent : baseEnd_1330369 < baseStart_1330369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330388 : List Nat := [2, 4, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1330388 : Nat := 118140960795 + 1330388 * 2 ^ 59
def prefixEnd_1330388 : Nat := 4983230072969 + 3 ^ 40 * 1330388 * 2
def baseEnd_1330388 : Nat := 455419000649230723021109

theorem tailTrace_1330388 : CollatzResearch.WordTrace tailWord_1330388 prefixEnd_1330388 455419000649230723021109 := by
  unfold tailWord_1330388
  simp only [CollatzResearch.WordTrace]
  refine ⟨24261618352119481513111909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32348824469492642017482545 24261618352119481513111909)
  ·
    refine ⟨4549053441022402783708483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24261618352119481513111909 4549053441022402783708483)
    ·
      refine ⟨6823580161533604175562725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4549053441022402783708483 6823580161533604175562725)
      ·
        refine ⟨1279421280287550782918011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6823580161533604175562725 1279421280287550782918011)
        ·
          refine ⟨1919131920431326174377017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279421280287550782918011 1919131920431326174377017)
          ·
            refine ⟨1439348940323494630782763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1919131920431326174377017 1439348940323494630782763)
            ·
              refine ⟨2159023410485241946174145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439348940323494630782763 2159023410485241946174145)
              ·
                refine ⟨1619267557863931459630609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2159023410485241946174145 1619267557863931459630609)
                ·
                  refine ⟨1214450668397948594722957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1619267557863931459630609 1214450668397948594722957)
                  ·
                    refine ⟨455419000649230723021109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1214450668397948594722957 455419000649230723021109)
                    ·
                      rfl

theorem cell22_1330388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1330388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330388 prefixEnd_1330388 := by exact prefixLift 1330388
  have htrace : WordTrace (prefixWord ++ tailWord_1330388) baseStart_1330388 baseEnd_1330388 := by
    simpa [prefixWord, tailWord_1330388, baseEnd_1330388] using wordTrace_append hprefix tailTrace_1330388
  have hstable : (prefixWord ++ tailWord_1330388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330388).length < 2 ^ (prefixWord ++ tailWord_1330388).sum := by decide
  have hdescent : baseEnd_1330388 < baseStart_1330388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330399 : List Nat := [1, 1, 2, 3, 2, 1, 4, 4, 1, 3]
def baseStart_1330399 : Nat := 118140960795 + 1330399 * 2 ^ 59
def prefixEnd_1330399 : Nat := 4983230072969 + 3 ^ 40 * 1330399 * 2
def baseEnd_1330399 : Nat := 455422766174030360996075

theorem tailTrace_1330399 : CollatzResearch.WordTrace tailWord_1330399 prefixEnd_1330399 455422766174030360996075 := by
  unfold tailWord_1330399
  simp only [CollatzResearch.WordTrace]
  refine ⟨48523637907199111904874251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32349091938132741269916167 48523637907199111904874251)
  ·
    refine ⟨72785456860798667857311377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48523637907199111904874251 72785456860798667857311377)
    ·
      refine ⟨54589092645599000892983533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72785456860798667857311377 54589092645599000892983533)
      ·
        refine ⟨20470909742099625334868825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54589092645599000892983533 20470909742099625334868825)
        ·
          refine ⟨15353182306574719001151619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20470909742099625334868825 15353182306574719001151619)
          ·
            refine ⟨23029773459862078501727429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15353182306574719001151619 23029773459862078501727429)
            ·
              refine ⟨4318082523724139719073893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23029773459862078501727429 4318082523724139719073893)
              ·
                refine ⟨809640473198276197326355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4318082523724139719073893 809640473198276197326355)
                ·
                  refine ⟨1214460709797414295989533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 809640473198276197326355 1214460709797414295989533)
                  ·
                    refine ⟨455422766174030360996075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1214460709797414295989533 455422766174030360996075)
                    ·
                      rfl

theorem cell22_1330399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 1, 3].length) (baseStart_1330399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330399 prefixEnd_1330399 := by exact prefixLift 1330399
  have htrace : WordTrace (prefixWord ++ tailWord_1330399) baseStart_1330399 baseEnd_1330399 := by
    simpa [prefixWord, tailWord_1330399, baseEnd_1330399] using wordTrace_append hprefix tailTrace_1330399
  have hstable : (prefixWord ++ tailWord_1330399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330399).length < 2 ^ (prefixWord ++ tailWord_1330399).sum := by decide
  have hdescent : baseEnd_1330399 < baseStart_1330399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330450 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_1330450 : Nat := 118140960795 + 1330450 * 2 ^ 59
def prefixEnd_1330450 : Nat := 4983230072969 + 3 ^ 40 * 1330450 * 2
def baseEnd_1330450 : Nat := 455440224516283227970919

theorem tailTrace_1330450 : CollatzResearch.WordTrace tailWord_1330450 prefixEnd_1330450 455440224516283227970919 := by
  unfold tailWord_1330450
  simp only [CollatzResearch.WordTrace]
  refine ⟨12131374507503586903745201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32350332020009565076653869 12131374507503586903745201)
  ·
    refine ⟨9098530880627690177808901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12131374507503586903745201 9098530880627690177808901)
    ·
      refine ⟨1705974540117691908339169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9098530880627690177808901 1705974540117691908339169)
      ·
        refine ⟨1279480905088268931254377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1705974540117691908339169 1279480905088268931254377)
        ·
          refine ⟨959610678816201698440783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1279480905088268931254377 959610678816201698440783)
          ·
            refine ⟨1439416018224302547661175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959610678816201698440783 1439416018224302547661175)
            ·
              refine ⟨2159124027336453821491763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439416018224302547661175 2159124027336453821491763)
              ·
                refine ⟨3238686041004680732237645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159124027336453821491763 3238686041004680732237645)
                ·
                  refine ⟨1214507265376755274589117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3238686041004680732237645 1214507265376755274589117)
                  ·
                    refine ⟨455440224516283227970919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1214507265376755274589117 455440224516283227970919)
                    ·
                      rfl

theorem cell22_1330450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_1330450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330450 prefixEnd_1330450 := by exact prefixLift 1330450
  have htrace : WordTrace (prefixWord ++ tailWord_1330450) baseStart_1330450 baseEnd_1330450 := by
    simpa [prefixWord, tailWord_1330450, baseEnd_1330450] using wordTrace_append hprefix tailTrace_1330450
  have hstable : (prefixWord ++ tailWord_1330450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330450).length < 2 ^ (prefixWord ++ tailWord_1330450).sum := by decide
  have hdescent : baseEnd_1330450 < baseStart_1330450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330489 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 1, 5]
def baseStart_1330489 : Nat := 118140960795 + 1330489 * 2 ^ 59
def prefixEnd_1330489 : Nat := 4983230072969 + 3 ^ 40 * 1330489 * 2
def baseEnd_1330489 : Nat := 455453575013300126245799

theorem tailTrace_1330489 : CollatzResearch.WordTrace tailWord_1330489 prefixEnd_1330489 455453575013300126245799 := by
  unfold tailWord_1330489
  simp only [CollatzResearch.WordTrace]
  refine ⟨48526920476873057275650521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32351280317915371517100347 48526920476873057275650521)
  ·
    refine ⟨36395190357654792956737891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48526920476873057275650521 36395190357654792956737891)
    ·
      refine ⟨54592785536482189435106837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36395190357654792956737891 54592785536482189435106837)
      ·
        refine ⟨2559036822022602629770633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54592785536482189435106837 2559036822022602629770633)
        ·
          refine ⟨1919277616516951972327975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2559036822022602629770633 1919277616516951972327975)
          ·
            refine ⟨2878916424775427958491963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919277616516951972327975 2878916424775427958491963)
            ·
              refine ⟨4318374637163141937737945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2878916424775427958491963 4318374637163141937737945)
              ·
                refine ⟨3238780977872356453303459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4318374637163141937737945 3238780977872356453303459)
                ·
                  refine ⟨4858171466808534679955189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238780977872356453303459 4858171466808534679955189)
                  ·
                    refine ⟨455453575013300126245799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4858171466808534679955189 455453575013300126245799)
                    ·
                      rfl

theorem cell22_1330489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_1330489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330489 prefixEnd_1330489 := by exact prefixLift 1330489
  have htrace : WordTrace (prefixWord ++ tailWord_1330489) baseStart_1330489 baseEnd_1330489 := by
    simpa [prefixWord, tailWord_1330489, baseEnd_1330489] using wordTrace_append hprefix tailTrace_1330489
  have hstable : (prefixWord ++ tailWord_1330489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330489).length < 2 ^ (prefixWord ++ tailWord_1330489).sum := by decide
  have hdescent : baseEnd_1330489 < baseStart_1330489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330493 : List Nat := [1, 4, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_1330493 : Nat := 118140960795 + 1330493 * 2 ^ 59
def prefixEnd_1330493 : Nat := 4983230072969 + 3 ^ 40 * 1330493 * 2
def baseEnd_1330493 : Nat := 455454944295045449145787

theorem tailTrace_1330493 : CollatzResearch.WordTrace tailWord_1330493 prefixEnd_1330493 455454944295045449145787 := by
  unfold tailWord_1330493
  simp only [CollatzResearch.WordTrace]
  refine ⟨48527066368858565958796133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32351377579239043972530755 48527066368858565958796133)
  ·
    refine ⟨9098824944160981117274275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48527066368858565958796133 9098824944160981117274275)
    ·
      refine ⟨13648237416241471675911413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9098824944160981117274275 13648237416241471675911413)
      ·
        refine ⟨1279522257772637969616695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13648237416241471675911413 1279522257772637969616695)
        ·
          refine ⟨1919283386658956954425043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279522257772637969616695 1919283386658956954425043)
          ·
            refine ⟨2878925079988435431637565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919283386658956954425043 2878925079988435431637565)
            ·
              refine ⟨1079596904995663286864087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2878925079988435431637565 1079596904995663286864087)
              ·
                refine ⟨1619395357493494930296131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079596904995663286864087 1619395357493494930296131)
                ·
                  refine ⟨2429093036240242395444197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619395357493494930296131 2429093036240242395444197)
                  ·
                    refine ⟨455454944295045449145787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2429093036240242395444197 455454944295045449145787)
                    ·
                      rfl

theorem cell22_1330493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_1330493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330493 prefixEnd_1330493 := by exact prefixLift 1330493
  have htrace : WordTrace (prefixWord ++ tailWord_1330493) baseStart_1330493 baseEnd_1330493 := by
    simpa [prefixWord, tailWord_1330493, baseEnd_1330493] using wordTrace_append hprefix tailTrace_1330493
  have hstable : (prefixWord ++ tailWord_1330493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330493).length < 2 ^ (prefixWord ++ tailWord_1330493).sum := by decide
  have hdescent : baseEnd_1330493 < baseStart_1330493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330515 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 1, 8]
def baseStart_1330515 : Nat := 118140960795 + 1330515 * 2 ^ 59
def prefixEnd_1330515 : Nat := 4983230072969 + 3 ^ 40 * 1330515 * 2
def baseEnd_1330515 : Nat := 455462475344644725095719

theorem tailTrace_1330515 : CollatzResearch.WordTrace tailWord_1330515 prefixEnd_1330515 455462475344644725095719 := by
  unfold tailWord_1330515
  simp only [CollatzResearch.WordTrace]
  refine ⟨48527868774778863716096999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32351912516519242477397999 48527868774778863716096999)
  ·
    refine ⟨72791803162168295574145499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48527868774778863716096999 72791803162168295574145499)
    ·
      refine ⟨109187704743252443361218249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72791803162168295574145499 109187704743252443361218249)
      ·
        refine ⟨81890778557439332520913687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109187704743252443361218249 81890778557439332520913687)
        ·
          refine ⟨122836167836158998781370531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81890778557439332520913687 122836167836158998781370531)
          ·
            refine ⟨184254251754238498172055797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122836167836158998781370531 184254251754238498172055797)
            ·
              refine ⟨17273836101959859203630231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184254251754238498172055797 17273836101959859203630231)
              ·
                refine ⟨25910754152939788805445347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17273836101959859203630231 25910754152939788805445347)
                ·
                  refine ⟨38866131229409683208168021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25910754152939788805445347 38866131229409683208168021)
                  ·
                    refine ⟨455462475344644725095719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38866131229409683208168021 455462475344644725095719)
                    ·
                      rfl

theorem cell22_1330515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_1330515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330515 prefixEnd_1330515 := by exact prefixLift 1330515
  have htrace : WordTrace (prefixWord ++ tailWord_1330515) baseStart_1330515 baseEnd_1330515 := by
    simpa [prefixWord, tailWord_1330515, baseEnd_1330515] using wordTrace_append hprefix tailTrace_1330515
  have hstable : (prefixWord ++ tailWord_1330515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330515).length < 2 ^ (prefixWord ++ tailWord_1330515).sum := by decide
  have hdescent : baseEnd_1330515 < baseStart_1330515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330538 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 2, 4]
def baseStart_1330538 : Nat := 118140960795 + 1330538 * 2 ^ 59
def prefixEnd_1330538 : Nat := 4983230072969 + 3 ^ 40 * 1330538 * 2
def baseEnd_1330538 : Nat := 455470348714680331770649

theorem tailTrace_1330538 : CollatzResearch.WordTrace tailWord_1330538 prefixEnd_1330538 455470348714680331770649 := by
  unfold tailWord_1330538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12132176913423884661046067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32352471769130359096122845 12132176913423884661046067)
  ·
    refine ⟨18198265370135826991569101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12132176913423884661046067 18198265370135826991569101)
    ·
      refine ⟨6824349513800935121838413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18198265370135826991569101 6824349513800935121838413)
      ·
        refine ⟨2559131067675350670689405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6824349513800935121838413 2559131067675350670689405)
        ·
          refine ⟨959674150378256501508527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2559131067675350670689405 959674150378256501508527)
          ·
            refine ⟨1439511225567384752262791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959674150378256501508527 1439511225567384752262791)
            ·
              refine ⟨2159266838351077128394187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439511225567384752262791 2159266838351077128394187)
              ·
                refine ⟨3238900257526615692591281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159266838351077128394187 3238900257526615692591281)
                ·
                  refine ⟨2429175193144961769443461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3238900257526615692591281 2429175193144961769443461)
                  ·
                    refine ⟨455470348714680331770649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2429175193144961769443461 455470348714680331770649)
                    ·
                      rfl

theorem cell22_1330538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_1330538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330538 prefixEnd_1330538 := by exact prefixLift 1330538
  have htrace : WordTrace (prefixWord ++ tailWord_1330538) baseStart_1330538 baseEnd_1330538 := by
    simpa [prefixWord, tailWord_1330538, baseEnd_1330538] using wordTrace_append hprefix tailTrace_1330538
  have hstable : (prefixWord ++ tailWord_1330538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330538).length < 2 ^ (prefixWord ++ tailWord_1330538).sum := by decide
  have hdescent : baseEnd_1330538 < baseStart_1330538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330551 : List Nat := [1, 1, 3, 1, 1, 2, 6, 3, 1, 3]
def baseStart_1330551 : Nat := 118140960795 + 1330551 * 2 ^ 59
def prefixEnd_1330551 : Nat := 4983230072969 + 3 ^ 40 * 1330551 * 2
def baseEnd_1330551 : Nat := 455474798880352631195609

theorem tailTrace_1330551 : CollatzResearch.WordTrace tailWord_1330551 prefixEnd_1330551 455474798880352631195609 := by
  unfold tailWord_1330551
  simp only [CollatzResearch.WordTrace]
  refine ⟨48529181802648441864407507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32352787868432294576271671 48529181802648441864407507)
  ·
    refine ⟨72793772703972662796611261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48529181802648441864407507 72793772703972662796611261)
    ·
      refine ⟨27297664763989748548729223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72793772703972662796611261 27297664763989748548729223)
      ·
        refine ⟨40946497145984622823093835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27297664763989748548729223 40946497145984622823093835)
        ·
          refine ⟨61419745718976934234640753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40946497145984622823093835 61419745718976934234640753)
          ·
            refine ⟨46064809289232700675980565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61419745718976934234640753 46064809289232700675980565)
            ·
              refine ⟨2159287935432782844186589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46064809289232700675980565 2159287935432782844186589)
              ·
                refine ⟨809732975787293566569971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2159287935432782844186589 809732975787293566569971)
                ·
                  refine ⟨1214599463680940349854957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 809732975787293566569971 1214599463680940349854957)
                  ·
                    refine ⟨455474798880352631195609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1214599463680940349854957 455474798880352631195609)
                    ·
                      rfl

theorem cell22_1330551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_1330551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330551 prefixEnd_1330551 := by exact prefixLift 1330551
  have htrace : WordTrace (prefixWord ++ tailWord_1330551) baseStart_1330551 baseEnd_1330551 := by
    simpa [prefixWord, tailWord_1330551, baseEnd_1330551] using wordTrace_append hprefix tailTrace_1330551
  have hstable : (prefixWord ++ tailWord_1330551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330551).length < 2 ^ (prefixWord ++ tailWord_1330551).sum := by decide
  have hdescent : baseEnd_1330551 < baseStart_1330551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330564 : List Nat := [2, 3, 2, 1, 1, 3, 3, 2, 5]
def baseStart_1330564 : Nat := 118140960795 + 1330564 * 2 ^ 59
def prefixEnd_1330564 : Nat := 4983230072969 + 3 ^ 40 * 1330564 * 2
def baseEnd_1330564 : Nat := 151826416348674976873523

theorem tailTrace_1330564 : CollatzResearch.WordTrace tailWord_1330564 prefixEnd_1330564 151826416348674976873523 := by
  unfold tailWord_1330564
  simp only [CollatzResearch.WordTrace]
  refine ⟨24264827975800672542315373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32353103967734230056420497 24264827975800672542315373)
  ·
    refine ⟨9099310490925252203368265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24264827975800672542315373 9099310490925252203368265)
    ·
      refine ⟨6824482868193939152526199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9099310490925252203368265 6824482868193939152526199)
      ·
        refine ⟨10236724302290908728789299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6824482868193939152526199 10236724302290908728789299)
        ·
          refine ⟨15355086453436363093183949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10236724302290908728789299 15355086453436363093183949)
          ·
            refine ⟨5758157420038636159943981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15355086453436363093183949 5758157420038636159943981)
            ·
              refine ⟨2159309032514488559978993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5758157420038636159943981 2159309032514488559978993)
              ·
                refine ⟨1619481774385866419984245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2159309032514488559978993 1619481774385866419984245)
                ·
                  refine ⟨151826416348674976873523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1619481774385866419984245 151826416348674976873523)
                  ·
                    rfl

theorem cell22_1330564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_1330564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330564 prefixEnd_1330564 := by exact prefixLift 1330564
  have htrace : WordTrace (prefixWord ++ tailWord_1330564) baseStart_1330564 baseEnd_1330564 := by
    simpa [prefixWord, tailWord_1330564, baseEnd_1330564] using wordTrace_append hprefix tailTrace_1330564
  have hstable : (prefixWord ++ tailWord_1330564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330564).length < 2 ^ (prefixWord ++ tailWord_1330564).sum := by decide
  have hdescent : baseEnd_1330564 < baseStart_1330564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330592 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 6]
def baseStart_1330592 : Nat := 118140960795 + 1330592 * 2 ^ 59
def prefixEnd_1330592 : Nat := 4983230072969 + 3 ^ 40 * 1330592 * 2
def baseEnd_1330592 : Nat := 151829611339414063640161

theorem tailTrace_1330592 : CollatzResearch.WordTrace tailWord_1330592 prefixEnd_1330592 151829611339414063640161 := by
  unfold tailWord_1330592
  simp only [CollatzResearch.WordTrace]
  refine ⟨24265338597749952933325015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32353784796999937244433353 24265338597749952933325015)
  ·
    refine ⟨36398007896624929399987523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24265338597749952933325015 36398007896624929399987523)
    ·
      refine ⟨54597011844937394099981285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36398007896624929399987523 54597011844937394099981285)
      ·
        refine ⟨10236939720925761393746491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54597011844937394099981285 10236939720925761393746491)
        ·
          refine ⟨15355409581388642090619737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10236939720925761393746491 15355409581388642090619737)
          ·
            refine ⟨11516557186041481567964803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15355409581388642090619737 11516557186041481567964803)
            ·
              refine ⟨17274835779062222351947205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11516557186041481567964803 17274835779062222351947205)
              ·
                refine ⟨3239031708574166690990101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17274835779062222351947205 3239031708574166690990101)
                ·
                  refine ⟨151829611339414063640161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3239031708574166690990101 151829611339414063640161)
                  ·
                    rfl

theorem cell22_1330592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_1330592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330592 prefixEnd_1330592 := by exact prefixLift 1330592
  have htrace : WordTrace (prefixWord ++ tailWord_1330592) baseStart_1330592 baseEnd_1330592 := by
    simpa [prefixWord, tailWord_1330592, baseEnd_1330592] using wordTrace_append hprefix tailTrace_1330592
  have hstable : (prefixWord ++ tailWord_1330592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330592).length < 2 ^ (prefixWord ++ tailWord_1330592).sum := by decide
  have hdescent : baseEnd_1330592 < baseStart_1330592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330607 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 1, 5]
def baseStart_1330607 : Nat := 118140960795 + 1330607 * 2 ^ 59
def prefixEnd_1330607 : Nat := 4983230072969 + 3 ^ 40 * 1330607 * 2
def baseEnd_1330607 : Nat := 455493968824787151795437

theorem tailTrace_1330607 : CollatzResearch.WordTrace tailWord_1330607 prefixEnd_1330607 455493968824787151795437 := by
  unfold tailWord_1330607
  simp only [CollatzResearch.WordTrace]
  refine ⟨48531224290445563428446075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32354149526963708952297383 48531224290445563428446075)
  ·
    refine ⟨72796836435668345142669113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48531224290445563428446075 72796836435668345142669113)
    ·
      refine ⟨54597627326751258857001835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72796836435668345142669113 54597627326751258857001835)
      ·
        refine ⟨81896440990126888285502753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54597627326751258857001835 81896440990126888285502753)
        ·
          refine ⟨61422330742595166214127065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81896440990126888285502753 61422330742595166214127065)
          ·
            refine ⟨46066748056946374660595299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61422330742595166214127065 46066748056946374660595299)
            ·
              refine ⟨69100122085419561990892949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46066748056946374660595299 69100122085419561990892949)
              ·
                refine ⟨3239068222754041968323107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69100122085419561990892949 3239068222754041968323107)
                ·
                  refine ⟨4858602334131062952484661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3239068222754041968323107 4858602334131062952484661)
                  ·
                    refine ⟨455493968824787151795437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4858602334131062952484661 455493968824787151795437)
                    ·
                      rfl

theorem cell22_1330607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_1330607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330607 prefixEnd_1330607 := by exact prefixLift 1330607
  have htrace : WordTrace (prefixWord ++ tailWord_1330607) baseStart_1330607 baseEnd_1330607 := by
    simpa [prefixWord, tailWord_1330607, baseEnd_1330607] using wordTrace_append hprefix tailTrace_1330607
  have hstable : (prefixWord ++ tailWord_1330607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330607).length < 2 ^ (prefixWord ++ tailWord_1330607).sum := by decide
  have hdescent : baseEnd_1330607 < baseStart_1330607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330624 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 4, 3]
def baseStart_1330624 : Nat := 118140960795 + 1330624 * 2 ^ 59
def prefixEnd_1330624 : Nat := 4983230072969 + 3 ^ 40 * 1330624 * 2
def baseEnd_1330624 : Nat := 455499788272204774120385

theorem tailTrace_1330624 : CollatzResearch.WordTrace tailWord_1330624 prefixEnd_1330624 455499788272204774120385 := by
  unfold tailWord_1330624
  simp only [CollatzResearch.WordTrace]
  refine ⟨24265922165691987665907463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32354562887589316887876617 24265922165691987665907463)
  ·
    refine ⟨36398883248537981498861195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24265922165691987665907463 36398883248537981498861195)
    ·
      refine ⟨54598324872806972248291793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36398883248537981498861195 54598324872806972248291793)
      ·
        refine ⟨40948743654605229186218845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54598324872806972248291793 40948743654605229186218845)
        ·
          refine ⟨15355778870476960944832067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40948743654605229186218845 15355778870476960944832067)
          ·
            refine ⟨23033668305715441417248101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15355778870476960944832067 23033668305715441417248101)
            ·
              refine ⟨4318812807321645265734019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23033668305715441417248101 4318812807321645265734019)
              ·
                refine ⟨6478219210982467898601029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4318812807321645265734019 6478219210982467898601029)
                ·
                  refine ⟨1214666102059212730987693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6478219210982467898601029 1214666102059212730987693)
                  ·
                    refine ⟨455499788272204774120385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1214666102059212730987693 455499788272204774120385)
                    ·
                      rfl

theorem cell22_1330624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 4, 3].length) (baseStart_1330624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330624 prefixEnd_1330624 := by exact prefixLift 1330624
  have htrace : WordTrace (prefixWord ++ tailWord_1330624) baseStart_1330624 baseEnd_1330624 := by
    simpa [prefixWord, tailWord_1330624, baseEnd_1330624] using wordTrace_append hprefix tailTrace_1330624
  have hstable : (prefixWord ++ tailWord_1330624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330624).length < 2 ^ (prefixWord ++ tailWord_1330624).sum := by decide
  have hdescent : baseEnd_1330624 < baseStart_1330624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330720 : List Nat := [2, 1, 1, 6, 1, 2, 2, 3, 1, 3]
def baseStart_1330720 : Nat := 118140960795 + 1330720 * 2 ^ 59
def prefixEnd_1330720 : Nat := 4983230072969 + 3 ^ 40 * 1330720 * 2
def baseEnd_1330720 : Nat := 455532651034092523720091

theorem tailTrace_1330720 : CollatzResearch.WordTrace tailWord_1330720 prefixEnd_1330720 455532651034092523720091 := by
  unfold tailWord_1330720
  simp only [CollatzResearch.WordTrace]
  refine ⟨24267672869518091863654807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32356897159357455818206409 24267672869518091863654807)
  ·
    refine ⟨36401509304277137795482211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24267672869518091863654807 36401509304277137795482211)
    ·
      refine ⟨54602263956415706693223317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36401509304277137795482211 54602263956415706693223317)
      ·
        refine ⟨2559481122956986251244843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54602263956415706693223317 2559481122956986251244843)
        ·
          refine ⟨3839221684435479376867265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2559481122956986251244843 3839221684435479376867265)
          ·
            refine ⟨2879416263326609532650449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3839221684435479376867265 2879416263326609532650449)
            ·
              refine ⟨2159562197494957149487837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2879416263326609532650449 2159562197494957149487837)
              ·
                refine ⟨809835824060608931057939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2159562197494957149487837 809835824060608931057939)
                ·
                  refine ⟨1214753736090913396586909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 809835824060608931057939 1214753736090913396586909)
                  ·
                    refine ⟨455532651034092523720091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1214753736090913396586909 455532651034092523720091)
                    ·
                      rfl

theorem cell22_1330720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 1, 3].length) (baseStart_1330720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330720 prefixEnd_1330720 := by exact prefixLift 1330720
  have htrace : WordTrace (prefixWord ++ tailWord_1330720) baseStart_1330720 baseEnd_1330720 := by
    simpa [prefixWord, tailWord_1330720, baseEnd_1330720] using wordTrace_append hprefix tailTrace_1330720
  have hstable : (prefixWord ++ tailWord_1330720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330720).length < 2 ^ (prefixWord ++ tailWord_1330720).sum := by decide
  have hdescent : baseEnd_1330720 < baseStart_1330720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330744 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 6]
def baseStart_1330744 : Nat := 118140960795 + 1330744 * 2 ^ 59
def prefixEnd_1330744 : Nat := 4983230072969 + 3 ^ 40 * 1330744 * 2
def baseEnd_1330744 : Nat := 151846955574854820373339

theorem tailTrace_1330744 : CollatzResearch.WordTrace tailWord_1330744 prefixEnd_1330744 151846955574854820373339 := by
  unfold tailWord_1330744
  simp only [CollatzResearch.WordTrace]
  refine ⟨24268110545474617913091643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32357480727299490550788857 24268110545474617913091643)
  ·
    refine ⟨36402165818211926869637465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24268110545474617913091643 36402165818211926869637465)
    ·
      refine ⟨27301624363658945152228099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36402165818211926869637465 27301624363658945152228099)
      ·
        refine ⟨40952436545488417728342149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27301624363658945152228099 40952436545488417728342149)
        ·
          refine ⟨7678581852279078324064153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40952436545488417728342149 7678581852279078324064153)
          ·
            refine ⟨5758936389209308743048115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7678581852279078324064153 5758936389209308743048115)
            ·
              refine ⟨8638404583813963114572173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5758936389209308743048115 8638404583813963114572173)
              ·
                refine ⟨3239401718930236167964565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8638404583813963114572173 3239401718930236167964565)
                ·
                  refine ⟨151846955574854820373339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3239401718930236167964565 151846955574854820373339)
                  ·
                    rfl

theorem cell22_1330744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_1330744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330744 prefixEnd_1330744 := by exact prefixLift 1330744
  have htrace : WordTrace (prefixWord ++ tailWord_1330744) baseStart_1330744 baseEnd_1330744 := by
    simpa [prefixWord, tailWord_1330744, baseEnd_1330744] using wordTrace_append hprefix tailTrace_1330744
  have hstable : (prefixWord ++ tailWord_1330744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330744).length < 2 ^ (prefixWord ++ tailWord_1330744).sum := by decide
  have hdescent : baseEnd_1330744 < baseStart_1330744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330789 : List Nat := [1, 3, 1, 3, 3, 1, 10]
def baseStart_1330789 : Nat := 118140960795 + 1330789 * 2 ^ 59
def prefixEnd_1330789 : Nat := 4983230072969 + 3 ^ 40 * 1330789 * 2
def baseEnd_1330789 : Nat := 16872454486822197916477

theorem tailTrace_1330789 : CollatzResearch.WordTrace tailWord_1330789 prefixEnd_1330789 16872454486822197916477 := by
  unfold tailWord_1330789
  simp only [CollatzResearch.WordTrace]
  refine ⟨48537862375786208511571421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32358574917190805674380947 48537862375786208511571421)
  ·
    refine ⟨18201698390919828191839283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48537862375786208511571421 18201698390919828191839283)
    ·
      refine ⟨27302547586379742287758925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18201698390919828191839283 27302547586379742287758925)
      ·
        refine ⟨10238455344892403357909597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27302547586379742287758925 10238455344892403357909597)
        ·
          refine ⟨3839420754334651259216099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10238455344892403357909597 3839420754334651259216099)
          ·
            refine ⟨5759131131501976888824149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3839420754334651259216099 5759131131501976888824149)
            ·
              refine ⟨16872454486822197916477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5759131131501976888824149 16872454486822197916477)
              ·
                rfl

theorem cell22_1330789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 10].length) (baseStart_1330789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330789 prefixEnd_1330789 := by exact prefixLift 1330789
  have htrace : WordTrace (prefixWord ++ tailWord_1330789) baseStart_1330789 baseEnd_1330789 := by
    simpa [prefixWord, tailWord_1330789, baseEnd_1330789] using wordTrace_append hprefix tailTrace_1330789
  have hstable : (prefixWord ++ tailWord_1330789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330789).length < 2 ^ (prefixWord ++ tailWord_1330789).sum := by decide
  have hdescent : baseEnd_1330789 < baseStart_1330789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330806 : List Nat := [5, 1, 1, 2, 2, 1, 1, 9]
def baseStart_1330806 : Nat := 118140960795 + 1330806 * 2 ^ 59
def prefixEnd_1330806 : Nat := 4983230072969 + 3 ^ 40 * 1330806 * 2
def baseEnd_1330806 : Nat := 50618010065735218452203

theorem tailTrace_1330806 : CollatzResearch.WordTrace tailWord_1330806 prefixEnd_1330806 50618010065735218452203 := by
  unfold tailWord_1330806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3033655151045288775933767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32358988277816413609960181 3033655151045288775933767)
  ·
    refine ⟨4550482726567933163900651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3033655151045288775933767 4550482726567933163900651)
    ·
      refine ⟨6825724089851899745850977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4550482726567933163900651 6825724089851899745850977)
      ·
        refine ⟨5119293067388924809388233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6825724089851899745850977 5119293067388924809388233)
        ·
          refine ⟨3839469800541693607041175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5119293067388924809388233 3839469800541693607041175)
          ·
            refine ⟨5759204700812540410561763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3839469800541693607041175 5759204700812540410561763)
            ·
              refine ⟨8638807051218810615842645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5759204700812540410561763 8638807051218810615842645)
              ·
                refine ⟨50618010065735218452203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8638807051218810615842645 50618010065735218452203)
                ·
                  rfl

theorem cell22_1330806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_1330806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330806 prefixEnd_1330806 := by exact prefixLift 1330806
  have htrace : WordTrace (prefixWord ++ tailWord_1330806) baseStart_1330806 baseEnd_1330806 := by
    simpa [prefixWord, tailWord_1330806, baseEnd_1330806] using wordTrace_append hprefix tailTrace_1330806
  have hstable : (prefixWord ++ tailWord_1330806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330806).length < 2 ^ (prefixWord ++ tailWord_1330806).sum := by decide
  have hdescent : baseEnd_1330806 < baseStart_1330806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330821 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 5, 3]
def baseStart_1330821 : Nat := 118140960795 + 1330821 * 2 ^ 59
def prefixEnd_1330821 : Nat := 4983230072969 + 3 ^ 40 * 1330821 * 2
def baseEnd_1330821 : Nat := 455567225398161926944781

theorem tailTrace_1330821 : CollatzResearch.WordTrace tailWord_1330821 prefixEnd_1330821 455567225398161926944781 := by
  unfold tailWord_1330821
  simp only [CollatzResearch.WordTrace]
  refine ⟨48539029511670277976736317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32359353007780185317824211 48539029511670277976736317)
  ·
    refine ⟨18202136066876354241276119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48539029511670277976736317 18202136066876354241276119)
    ·
      refine ⟨27303204100314531361914179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18202136066876354241276119 27303204100314531361914179)
      ·
        refine ⟨40954806150471797042871269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27303204100314531361914179 40954806150471797042871269)
        ·
          refine ⟨7679026153213461945538363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40954806150471797042871269 7679026153213461945538363)
          ·
            refine ⟨11518539229820192918307545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7679026153213461945538363 11518539229820192918307545)
            ·
              refine ⟨8638904422365144688730659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11518539229820192918307545 8638904422365144688730659)
              ·
                refine ⟨12958356633547717033095989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8638904422365144688730659 12958356633547717033095989)
                ·
                  refine ⟨1214845934395098471852749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12958356633547717033095989 1214845934395098471852749)
                  ·
                    refine ⟨455567225398161926944781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1214845934395098471852749 455567225398161926944781)
                    ·
                      rfl

theorem cell22_1330821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_1330821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330821 prefixEnd_1330821 := by exact prefixLift 1330821
  have htrace : WordTrace (prefixWord ++ tailWord_1330821) baseStart_1330821 baseEnd_1330821 := by
    simpa [prefixWord, tailWord_1330821, baseEnd_1330821] using wordTrace_append hprefix tailTrace_1330821
  have hstable : (prefixWord ++ tailWord_1330821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330821).length < 2 ^ (prefixWord ++ tailWord_1330821).sum := by decide
  have hdescent : baseEnd_1330821 < baseStart_1330821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330851 : List Nat := [1, 1, 1, 4, 1, 1, 6, 2, 5]
def baseStart_1330851 : Nat := 118140960795 + 1330851 * 2 ^ 59
def prefixEnd_1330851 : Nat := 4983230072969 + 3 ^ 40 * 1330851 * 2
def baseEnd_1330851 : Nat := 151859165003750616231563

theorem tailTrace_1330851 : CollatzResearch.WordTrace tailWord_1330851 prefixEnd_1330851 151859165003750616231563 := by
  unfold tailWord_1330851
  simp only [CollatzResearch.WordTrace]
  refine ⟨48540123701561593100328407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32360082467707728733552271 48540123701561593100328407)
  ·
    refine ⟨72810185552342389650492611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48540123701561593100328407 72810185552342389650492611)
    ·
      refine ⟨109215278328513584475738917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72810185552342389650492611 109215278328513584475738917)
      ·
        refine ⟨20477864686596297089201047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109215278328513584475738917 20477864686596297089201047)
        ·
          refine ⟨30716797029894445633801571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20477864686596297089201047 30716797029894445633801571)
          ·
            refine ⟨46075195544841668450702357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30716797029894445633801571 46075195544841668450702357)
            ·
              refine ⟨2159774791164453208626673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46075195544841668450702357 2159774791164453208626673)
              ·
                refine ⟨1619831093373339906470005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2159774791164453208626673 1619831093373339906470005)
                ·
                  refine ⟨151859165003750616231563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1619831093373339906470005 151859165003750616231563)
                  ·
                    rfl

theorem cell22_1330851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 5].length) (baseStart_1330851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330851 prefixEnd_1330851 := by exact prefixLift 1330851
  have htrace : WordTrace (prefixWord ++ tailWord_1330851) baseStart_1330851 baseEnd_1330851 := by
    simpa [prefixWord, tailWord_1330851, baseEnd_1330851] using wordTrace_append hprefix tailTrace_1330851
  have hstable : (prefixWord ++ tailWord_1330851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330851).length < 2 ^ (prefixWord ++ tailWord_1330851).sum := by decide
  have hdescent : baseEnd_1330851 < baseStart_1330851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330913 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 6]
def baseStart_1330913 : Nat := 118140960795 + 1330913 * 2 ^ 59
def prefixEnd_1330913 : Nat := 4983230072969 + 3 ^ 40 * 1330913 * 2
def baseEnd_1330913 : Nat := 151866239626101451214833

theorem tailTrace_1330913 : CollatzResearch.WordTrace tailWord_1330913 prefixEnd_1330913 151866239626101451214833 := by
  unfold tailWord_1330913
  simp only [CollatzResearch.WordTrace]
  refine ⟨48542385027336977689085393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32361590018224651792723595 48542385027336977689085393)
  ·
    refine ⟨36406788770502733266814045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48542385027336977689085393 36406788770502733266814045)
    ·
      refine ⟨13652545788938524975055267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36406788770502733266814045 13652545788938524975055267)
      ·
        refine ⟨20478818683407787462582901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13652545788938524975055267 20478818683407787462582901)
        ·
          refine ⟨1919889251569480074617147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20478818683407787462582901 1919889251569480074617147)
          ·
            refine ⟨2879833877354220111925721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919889251569480074617147 2879833877354220111925721)
            ·
              refine ⟨2159875408015665083944291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2879833877354220111925721 2159875408015665083944291)
              ·
                refine ⟨3239813112023497625916437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159875408015665083944291 3239813112023497625916437)
                ·
                  refine ⟨151866239626101451214833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3239813112023497625916437 151866239626101451214833)
                  ·
                    rfl

theorem cell22_1330913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 6].length) (baseStart_1330913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330913 prefixEnd_1330913 := by exact prefixLift 1330913
  have htrace : WordTrace (prefixWord ++ tailWord_1330913) baseStart_1330913 baseEnd_1330913 := by
    simpa [prefixWord, tailWord_1330913, baseEnd_1330913] using wordTrace_append hprefix tailTrace_1330913
  have hstable : (prefixWord ++ tailWord_1330913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330913).length < 2 ^ (prefixWord ++ tailWord_1330913).sum := by decide
  have hdescent : baseEnd_1330913 < baseStart_1330913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330926 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1330926 : Nat := 118140960795 + 1330926 * 2 ^ 59
def prefixEnd_1330926 : Nat := 4983230072969 + 3 ^ 40 * 1330926 * 2
def baseEnd_1330926 : Nat := 455603169043976653069459

theorem tailTrace_1330926 : CollatzResearch.WordTrace tailWord_1330926 prefixEnd_1330926 455603169043976653069459 := by
  unfold tailWord_1330926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6067857397036235113663579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32361906117526587272872421 6067857397036235113663579)
  ·
    refine ⟨9101786095554352670495369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6067857397036235113663579 9101786095554352670495369)
    ·
      refine ⟨6826339571665764502871527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9101786095554352670495369 6826339571665764502871527)
      ·
        refine ⟨10239509357498646754307291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6826339571665764502871527 10239509357498646754307291)
        ·
          refine ⟨15359264036247970131460937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10239509357498646754307291 15359264036247970131460937)
          ·
            refine ⟨11519448027185977598595703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15359264036247970131460937 11519448027185977598595703)
            ·
              refine ⟨17279172040778966397893555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11519448027185977598595703 17279172040778966397893555)
              ·
                refine ⟨25918758061168449596840333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17279172040778966397893555 25918758061168449596840333)
                ·
                  refine ⟨9719534272938168598815125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25918758061168449596840333 9719534272938168598815125)
                  ·
                    refine ⟨455603169043976653069459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9719534272938168598815125 455603169043976653069459)
                    ·
                      rfl

theorem cell22_1330926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1330926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330926 prefixEnd_1330926 := by exact prefixLift 1330926
  have htrace : WordTrace (prefixWord ++ tailWord_1330926) baseStart_1330926 baseEnd_1330926 := by
    simpa [prefixWord, tailWord_1330926, baseEnd_1330926] using wordTrace_append hprefix tailTrace_1330926
  have hstable : (prefixWord ++ tailWord_1330926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330926).length < 2 ^ (prefixWord ++ tailWord_1330926).sum := by decide
  have hdescent : baseEnd_1330926 < baseStart_1330926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330932 : List Nat := [2, 6, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1330932 : Nat := 118140960795 + 1330932 * 2 ^ 59
def prefixEnd_1330932 : Nat := 4983230072969 + 3 ^ 40 * 1330932 * 2
def baseEnd_1330932 : Nat := 455605222966594637419441

theorem tailTrace_1330932 : CollatzResearch.WordTrace tailWord_1330932 prefixEnd_1330932 455605222966594637419441 := by
  unfold tailWord_1330932
  simp only [CollatzResearch.WordTrace]
  refine ⟨24271539007134071967013525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32362052009512095956018033 24271539007134071967013525)
  ·
    refine ⟨1137728390959409623453759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24271539007134071967013525 1137728390959409623453759)
    ·
      refine ⟨1706592586439114435180639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137728390959409623453759 1706592586439114435180639)
      ·
        refine ⟨2559888879658671652770959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1706592586439114435180639 2559888879658671652770959)
        ·
          refine ⟨3839833319488007479156439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2559888879658671652770959 3839833319488007479156439)
          ·
            refine ⟨5759749979232011218734659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3839833319488007479156439 5759749979232011218734659)
            ·
              refine ⟨8639624968848016828101989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5759749979232011218734659 8639624968848016828101989)
              ·
                refine ⟨1619929681659003155269123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8639624968848016828101989 1619929681659003155269123)
                ·
                  refine ⟨2429894522488504732903685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619929681659003155269123 2429894522488504732903685)
                  ·
                    refine ⟨455605222966594637419441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2429894522488504732903685 455605222966594637419441)
                    ·
                      rfl

theorem cell22_1330932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1330932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330932 prefixEnd_1330932 := by exact prefixLift 1330932
  have htrace : WordTrace (prefixWord ++ tailWord_1330932) baseStart_1330932 baseEnd_1330932 := by
    simpa [prefixWord, tailWord_1330932, baseEnd_1330932] using wordTrace_append hprefix tailTrace_1330932
  have hstable : (prefixWord ++ tailWord_1330932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330932).length < 2 ^ (prefixWord ++ tailWord_1330932).sum := by decide
  have hdescent : baseEnd_1330932 < baseStart_1330932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330964 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 6]
def baseStart_1330964 : Nat := 118140960795 + 1330964 * 2 ^ 59
def prefixEnd_1330964 : Nat := 4983230072969 + 3 ^ 40 * 1330964 * 2
def baseEnd_1330964 : Nat := 151872059073519073539781

theorem tailTrace_1330964 : CollatzResearch.WordTrace tailWord_1330964 prefixEnd_1330964 151872059073519073539781 := by
  unfold tailWord_1330964
  simp only [CollatzResearch.WordTrace]
  refine ⟨24272122575076106699595973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32362830100101475599461297 24272122575076106699595973)
  ·
    refine ⟨4551022982826770006174245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24272122575076106699595973 4551022982826770006174245)
    ·
      refine ⟨853316809280019376157671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4551022982826770006174245 853316809280019376157671)
      ·
        refine ⟨1279975213920029064236507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853316809280019376157671 1279975213920029064236507)
        ·
          refine ⟨1919962820880043596354761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279975213920029064236507 1919962820880043596354761)
          ·
            refine ⟨1439972115660032697266071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1919962820880043596354761 1439972115660032697266071)
            ·
              refine ⟨2159958173490049045899107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439972115660032697266071 2159958173490049045899107)
              ·
                refine ⟨3239937260235073568848661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159958173490049045899107 3239937260235073568848661)
                ·
                  refine ⟨151872059073519073539781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3239937260235073568848661 151872059073519073539781)
                  ·
                    rfl

theorem cell22_1330964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_1330964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1330964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1330964 prefixEnd_1330964 := by exact prefixLift 1330964
  have htrace : WordTrace (prefixWord ++ tailWord_1330964) baseStart_1330964 baseEnd_1330964 := by
    simpa [prefixWord, tailWord_1330964, baseEnd_1330964] using wordTrace_append hprefix tailTrace_1330964
  have hstable : (prefixWord ++ tailWord_1330964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330964).length < 2 ^ (prefixWord ++ tailWord_1330964).sum := by decide
  have hdescent : baseEnd_1330964 < baseStart_1330964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331020 : List Nat := [2, 2, 1, 3, 4, 1, 2, 2, 5]
def baseStart_1331020 : Nat := 118140960795 + 1331020 * 2 ^ 59
def prefixEnd_1331020 : Nat := 4983230072969 + 3 ^ 40 * 1331020 * 2
def baseEnd_1331020 : Nat := 151878449054997247073057

theorem tailTrace_1331020 : CollatzResearch.WordTrace tailWord_1331020 prefixEnd_1331020 151878449054997247073057 := by
  unfold tailWord_1331020
  simp only [CollatzResearch.WordTrace]
  refine ⟨24273143818974667481615257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32364191758632889975487009 24273143818974667481615257)
  ·
    refine ⟨18204857864231000611211443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24273143818974667481615257 18204857864231000611211443)
    ·
      refine ⟨27307286796346500916817165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18204857864231000611211443 27307286796346500916817165)
      ·
        refine ⟨10240232548629937843806437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27307286796346500916817165 10240232548629937843806437)
        ·
          refine ⟨1920043602868113345713707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10240232548629937843806437 1920043602868113345713707)
          ·
            refine ⟨2880065404302170018570561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920043602868113345713707 2880065404302170018570561)
            ·
              refine ⟨2160049053226627513927921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2880065404302170018570561 2160049053226627513927921)
              ·
                refine ⟨1620036789919970635445941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160049053226627513927921 1620036789919970635445941)
                ·
                  refine ⟨151878449054997247073057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1620036789919970635445941 151878449054997247073057)
                  ·
                    rfl

theorem cell22_1331020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_1331020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331020 prefixEnd_1331020 := by exact prefixLift 1331020
  have htrace : WordTrace (prefixWord ++ tailWord_1331020) baseStart_1331020 baseEnd_1331020 := by
    simpa [prefixWord, tailWord_1331020, baseEnd_1331020] using wordTrace_append hprefix tailTrace_1331020
  have hstable : (prefixWord ++ tailWord_1331020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331020).length < 2 ^ (prefixWord ++ tailWord_1331020).sum := by decide
  have hdescent : baseEnd_1331020 < baseStart_1331020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331048 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 6]
def baseStart_1331048 : Nat := 118140960795 + 1331048 * 2 ^ 59
def prefixEnd_1331048 : Nat := 4983230072969 + 3 ^ 40 * 1331048 * 2
def baseEnd_1331048 : Nat := 151881644045736333839695

theorem tailTrace_1331048 : CollatzResearch.WordTrace tailWord_1331048 prefixEnd_1331048 151881644045736333839695 := by
  unfold tailWord_1331048
  simp only [CollatzResearch.WordTrace]
  refine ⟨24273654440923947872624899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32364872587898597163499865 24273654440923947872624899)
  ·
    refine ⟨36410481661385921808937349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24273654440923947872624899 36410481661385921808937349)
    ·
      refine ⟨6826965311509860339175753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36410481661385921808937349 6826965311509860339175753)
      ·
        refine ⟨5120223983632395254381815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6826965311509860339175753 5120223983632395254381815)
        ·
          refine ⟨7680335975448592881572723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5120223983632395254381815 7680335975448592881572723)
          ·
            refine ⟨11520503963172889322359085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7680335975448592881572723 11520503963172889322359085)
            ·
              refine ⟨4320188986189833495884657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11520503963172889322359085 4320188986189833495884657)
              ·
                refine ⟨3240141739642375121913493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4320188986189833495884657 3240141739642375121913493)
                ·
                  refine ⟨151881644045736333839695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3240141739642375121913493 151881644045736333839695)
                  ·
                    rfl

theorem cell22_1331048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_1331048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331048 prefixEnd_1331048 := by exact prefixLift 1331048
  have htrace : WordTrace (prefixWord ++ tailWord_1331048) baseStart_1331048 baseEnd_1331048 := by
    simpa [prefixWord, tailWord_1331048, baseEnd_1331048] using wordTrace_append hprefix tailTrace_1331048
  have hstable : (prefixWord ++ tailWord_1331048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331048).length < 2 ^ (prefixWord ++ tailWord_1331048).sum := by decide
  have hdescent : baseEnd_1331048 < baseStart_1331048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331065 : List Nat := [1, 2, 1, 3, 2, 2, 4, 3, 4]
def baseStart_1331065 : Nat := 118140960795 + 1331065 * 2 ^ 59
def prefixEnd_1331065 : Nat := 4983230072969 + 3 ^ 40 * 1331065 * 2
def baseEnd_1331065 : Nat := 151883583861542207948011

theorem tailTrace_1331065 : CollatzResearch.WordTrace tailWord_1331065 prefixEnd_1331065 151883583861542207948011 := by
  unfold tailWord_1331065
  simp only [CollatzResearch.WordTrace]
  refine ⟨48547928922786307648618649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32365285948524205099079099 48547928922786307648618649)
  ·
    refine ⟨36410946692089730736463987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48547928922786307648618649 36410946692089730736463987)
    ·
      refine ⟨54616420038134596104695981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36410946692089730736463987 54616420038134596104695981)
      ·
        refine ⟨20481157514300473539260993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54616420038134596104695981 20481157514300473539260993)
        ·
          refine ⟨15360868135725355154445745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20481157514300473539260993 15360868135725355154445745)
          ·
            refine ⟨11520651101794016365834309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15360868135725355154445745 11520651101794016365834309)
            ·
              refine ⟨2160122081586378068593933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11520651101794016365834309 2160122081586378068593933)
              ·
                refine ⟨810045780594891775722725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2160122081586378068593933 810045780594891775722725)
                ·
                  refine ⟨151883583861542207948011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 810045780594891775722725 151883583861542207948011)
                  ·
                    rfl

theorem cell22_1331065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 4].length) (baseStart_1331065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331065 prefixEnd_1331065 := by exact prefixLift 1331065
  have htrace : WordTrace (prefixWord ++ tailWord_1331065) baseStart_1331065 baseEnd_1331065 := by
    simpa [prefixWord, tailWord_1331065, baseEnd_1331065] using wordTrace_append hprefix tailTrace_1331065
  have hstable : (prefixWord ++ tailWord_1331065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331065).length < 2 ^ (prefixWord ++ tailWord_1331065).sum := by decide
  have hdescent : baseEnd_1331065 < baseStart_1331065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331236 : List Nat := [2, 3, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_1331236 : Nat := 118140960795 + 1331236 * 2 ^ 59
def prefixEnd_1331236 : Nat := 4983230072969 + 3 ^ 40 * 1331236 * 2
def baseEnd_1331236 : Nat := 455709288379239177818509

theorem tailTrace_1331236 : CollatzResearch.WordTrace tailWord_1331236 prefixEnd_1331236 455709288379239177818509 := by
  unfold tailWord_1331236
  simp only [CollatzResearch.WordTrace]
  refine ⟨24277082902583401926546781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32369443870111202568729041 24277082902583401926546781)
  ·
    refine ⟨9103906088468775722455043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24277082902583401926546781 9103906088468775722455043)
    ·
      refine ⟨13655859132703163583682565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9103906088468775722455043 13655859132703163583682565)
      ·
        refine ⟨2560473587381843171940481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13655859132703163583682565 2560473587381843171940481)
        ·
          refine ⟨1920355190536382378955361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2560473587381843171940481 1920355190536382378955361)
          ·
            refine ⟨1440266392902286784216521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1920355190536382378955361 1440266392902286784216521)
            ·
              refine ⟨1080199794676715088162391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1440266392902286784216521 1080199794676715088162391)
              ·
                refine ⟨1620299692015072632243587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080199794676715088162391 1620299692015072632243587)
                ·
                  refine ⟨2430449538022608948365381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620299692015072632243587 2430449538022608948365381)
                  ·
                    refine ⟨455709288379239177818509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2430449538022608948365381 455709288379239177818509)
                    ·
                      rfl

theorem cell22_1331236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_1331236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331236 prefixEnd_1331236 := by exact prefixLift 1331236
  have htrace : WordTrace (prefixWord ++ tailWord_1331236) baseStart_1331236 baseEnd_1331236 := by
    simpa [prefixWord, tailWord_1331236, baseEnd_1331236] using wordTrace_append hprefix tailTrace_1331236
  have hstable : (prefixWord ++ tailWord_1331236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331236).length < 2 ^ (prefixWord ++ tailWord_1331236).sum := by decide
  have hdescent : baseEnd_1331236 < baseStart_1331236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331249 : List Nat := [1, 2, 2, 3, 1, 5, 1, 2, 2, 3]
def baseStart_1331249 : Nat := 118140960795 + 1331249 * 2 ^ 59
def prefixEnd_1331249 : Nat := 4983230072969 + 3 ^ 40 * 1331249 * 2
def baseEnd_1331249 : Nat := 455713738544911477243469

theorem tailTrace_1331249 : CollatzResearch.WordTrace tailWord_1331249 prefixEnd_1331249 455713738544911477243469 := by
  unfold tailWord_1331249
  simp only [CollatzResearch.WordTrace]
  refine ⟨48554639954119707073316801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32369759969413138048877867 48554639954119707073316801)
  ·
    refine ⟨36415979965589780304987601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48554639954119707073316801 36415979965589780304987601)
    ·
      refine ⟨27311984974192335228740701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36415979965589780304987601 27311984974192335228740701)
      ·
        refine ⟨10241994365322125710777763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27311984974192335228740701 10241994365322125710777763)
        ·
          refine ⟨15362991547983188566166645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10241994365322125710777763 15362991547983188566166645)
          ·
            refine ⟨1440280457623423928078123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15362991547983188566166645 1440280457623423928078123)
            ·
              refine ⟨2160420686435135892117185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1440280457623423928078123 2160420686435135892117185)
              ·
                refine ⟨1620315514826351919087889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160420686435135892117185 1620315514826351919087889)
                ·
                  refine ⟨1215236636119763939315917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1620315514826351919087889 1215236636119763939315917)
                  ·
                    refine ⟨455713738544911477243469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1215236636119763939315917 455713738544911477243469)
                    ·
                      rfl

theorem cell22_1331249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_1331249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1331249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1331249 prefixEnd_1331249 := by exact prefixLift 1331249
  have htrace : WordTrace (prefixWord ++ tailWord_1331249) baseStart_1331249 baseEnd_1331249 := by
    simpa [prefixWord, tailWord_1331249, baseEnd_1331249] using wordTrace_append hprefix tailTrace_1331249
  have hstable : (prefixWord ++ tailWord_1331249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331249).length < 2 ^ (prefixWord ++ tailWord_1331249).sum := by decide
  have hdescent : baseEnd_1331249 < baseStart_1331249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
