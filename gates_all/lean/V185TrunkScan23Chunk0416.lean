import V185TrunkScan23Chunk0415

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2458680 : List Nat := [2, 1, 2, 1, 5, 3, 2, 1, 1, 3, 2]
def baseStart_2458680 : Nat := 118140960795 + 2458680 * 2 ^ 59
def prefixEnd_2458680 : Nat := 4983230072969 + 3 ^ 40 * 2458680 * 2
def baseEnd_2458680 : Nat := 1262484615596545636892743

theorem tailTrace_2458680 : CollatzResearch.WordTrace tailWord_2458680 prefixEnd_2458680 1262484615596545636892743 := by
  unfold tailWord_2458680
  simp only [CollatzResearch.WordTrace]
  refine ⟨44837713366314871979218747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59783617821753162638958329 44837713366314871979218747)
  ·
    refine ⟨67256570049472307968828121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44837713366314871979218747 67256570049472307968828121)
    ·
      refine ⟨50442427537104230976621091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67256570049472307968828121 50442427537104230976621091)
      ·
        refine ⟨75663641305656346464931637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50442427537104230976621091 75663641305656346464931637)
        ·
          refine ⟨7093466372405282481087341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75663641305656346464931637 7093466372405282481087341)
          ·
            refine ⟨2660049889651980930407753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7093466372405282481087341 2660049889651980930407753)
            ·
              refine ⟨1995037417238985697805815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2660049889651980930407753 1995037417238985697805815)
              ·
                refine ⟨2992556125858478546708723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995037417238985697805815 2992556125858478546708723)
                ·
                  refine ⟨4488834188787717820063085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2992556125858478546708723 4488834188787717820063085)
                  ·
                    refine ⟨1683312820795394182523657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4488834188787717820063085 1683312820795394182523657)
                    ·
                      refine ⟨1262484615596545636892743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1683312820795394182523657 1262484615596545636892743)
                      ·
                        rfl

theorem cell23_2458680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 1, 3, 2].length) (baseStart_2458680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458680 prefixEnd_2458680 := by exact prefixLift 2458680
  have htrace : WordTrace (prefixWord ++ tailWord_2458680) baseStart_2458680 baseEnd_2458680 := by
    simpa [prefixWord, tailWord_2458680, baseEnd_2458680] using wordTrace_append hprefix tailTrace_2458680
  have hstable : (prefixWord ++ tailWord_2458680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458680).length < 2 ^ (prefixWord ++ tailWord_2458680).sum := by decide
  have hdescent : baseEnd_2458680 < baseStart_2458680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458693 : List Nat := [1, 3, 1, 1, 1, 3, 5, 2, 2, 2, 2]
def baseStart_2458693 : Nat := 118140960795 + 2458693 * 2 ^ 59
def prefixEnd_2458693 : Nat := 4983230072969 + 3 ^ 40 * 2458693 * 2
def baseEnd_2458693 : Nat := 1262491290845054086030183

theorem tailTrace_2458693 : CollatzResearch.WordTrace tailWord_2458693 prefixEnd_2458693 1262491290845054086030183 := by
  unfold tailWord_2458693
  simp only [CollatzResearch.WordTrace]
  refine ⟨89675900881582647178660733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59783933921055098119107155 89675900881582647178660733)
  ·
    refine ⟨33628462830593492691997775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89675900881582647178660733 33628462830593492691997775)
    ·
      refine ⟨50442694245890239037996663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33628462830593492691997775 50442694245890239037996663)
      ·
        refine ⟨75664041368835358556994995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50442694245890239037996663 75664041368835358556994995)
        ·
          refine ⟨113496062053253037835492493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75664041368835358556994995 113496062053253037835492493)
          ·
            refine ⟨42561023269969889188309685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113496062053253037835492493 42561023269969889188309685)
            ·
              refine ⟨3990095931559677111404033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42561023269969889188309685 3990095931559677111404033)
              ·
                refine ⟨2992571948669757833553025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3990095931559677111404033 2992571948669757833553025)
                ·
                  refine ⟨2244428961502318375164769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2992571948669757833553025 2244428961502318375164769)
                  ·
                    refine ⟨1683321721126738781373577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2244428961502318375164769 1683321721126738781373577)
                    ·
                      refine ⟨1262491290845054086030183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1683321721126738781373577 1262491290845054086030183)
                      ·
                        rfl

theorem cell23_2458693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 2, 2].length) (baseStart_2458693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458693 prefixEnd_2458693 := by exact prefixLift 2458693
  have htrace : WordTrace (prefixWord ++ tailWord_2458693) baseStart_2458693 baseEnd_2458693 := by
    simpa [prefixWord, tailWord_2458693, baseEnd_2458693] using wordTrace_append hprefix tailTrace_2458693
  have hstable : (prefixWord ++ tailWord_2458693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458693).length < 2 ^ (prefixWord ++ tailWord_2458693).sum := by decide
  have hdescent : baseEnd_2458693 < baseStart_2458693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458709 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_2458709 : Nat := 118140960795 + 2458709 * 2 ^ 59
def prefixEnd_2458709 : Nat := 4983230072969 + 3 ^ 40 * 2458709 * 2
def baseEnd_2458709 : Nat := 1262499506535526023430109

theorem tailTrace_2458709 : CollatzResearch.WordTrace tailWord_2458709 prefixEnd_2458709 1262499506535526023430109 := by
  unfold tailWord_2458709
  simp only [CollatzResearch.WordTrace]
  refine ⟨89676484449524681911243181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59784322966349787940828787 89676484449524681911243181)
  ·
    refine ⟨33628681668571755716716193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89676484449524681911243181 33628681668571755716716193)
    ·
      refine ⟨25221511251428816787537145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33628681668571755716716193 25221511251428816787537145)
      ·
        refine ⟨18916133438571612590652859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25221511251428816787537145 18916133438571612590652859)
        ·
          refine ⟨28374200157857418885979289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18916133438571612590652859 28374200157857418885979289)
          ·
            refine ⟨21280650118393064164484467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28374200157857418885979289 21280650118393064164484467)
            ·
              refine ⟨31920975177589596246726701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21280650118393064164484467 31920975177589596246726701)
              ·
                refine ⟨11970365691596098592522513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31920975177589596246726701 11970365691596098592522513)
                ·
                  refine ⟨8977774268697073944391885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11970365691596098592522513 8977774268697073944391885)
                  ·
                    refine ⟨3366665350761402729146957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8977774268697073944391885 3366665350761402729146957)
                    ·
                      refine ⟨1262499506535526023430109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3366665350761402729146957 1262499506535526023430109)
                      ·
                        rfl

theorem cell23_2458709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_2458709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458709 prefixEnd_2458709 := by exact prefixLift 2458709
  have htrace : WordTrace (prefixWord ++ tailWord_2458709) baseStart_2458709 baseEnd_2458709 := by
    simpa [prefixWord, tailWord_2458709, baseEnd_2458709] using wordTrace_append hprefix tailTrace_2458709
  have hstable : (prefixWord ++ tailWord_2458709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458709).length < 2 ^ (prefixWord ++ tailWord_2458709).sum := by decide
  have hdescent : baseEnd_2458709 < baseStart_2458709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458712 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 3, 7]
def baseStart_2458712 : Nat := 118140960795 + 2458712 * 2 ^ 59
def prefixEnd_2458712 : Nat := 4983230072969 + 3 ^ 40 * 2458712 * 2
def baseEnd_2458712 : Nat := 420833682325829837230865

theorem tailTrace_2458712 : CollatzResearch.WordTrace tailWord_2458712 prefixEnd_2458712 420833682325829837230865 := by
  unfold tailWord_2458712
  simp only [CollatzResearch.WordTrace]
  refine ⟨44838296934256906711801195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59784395912342542282401593 44838296934256906711801195)
  ·
    refine ⟨67257445401385360067701793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44838296934256906711801195 67257445401385360067701793)
    ·
      refine ⟨50443084051039020050776345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67257445401385360067701793 50443084051039020050776345)
      ·
        refine ⟨37832313038279265038082259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50443084051039020050776345 37832313038279265038082259)
        ·
          refine ⟨56748469557418897557123389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37832313038279265038082259 56748469557418897557123389)
          ·
            refine ⟨21280676084032086583921271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56748469557418897557123389 21280676084032086583921271)
            ·
              refine ⟨31921014126048129875881907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21280676084032086583921271 31921014126048129875881907)
              ·
                refine ⟨47881521189072194813822861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31921014126048129875881907 47881521189072194813822861)
                ·
                  refine ⟨17955570445902073055183573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47881521189072194813822861 17955570445902073055183573)
                  ·
                    refine ⟨420833682325829837230865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17955570445902073055183573 420833682325829837230865)
                    ·
                      rfl

theorem cell23_2458712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_2458712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458712 prefixEnd_2458712 := by exact prefixLift 2458712
  have htrace : WordTrace (prefixWord ++ tailWord_2458712) baseStart_2458712 baseEnd_2458712 := by
    simpa [prefixWord, tailWord_2458712, baseEnd_2458712] using wordTrace_append hprefix tailTrace_2458712
  have hstable : (prefixWord ++ tailWord_2458712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458712).length < 2 ^ (prefixWord ++ tailWord_2458712).sum := by decide
  have hdescent : baseEnd_2458712 < baseStart_2458712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458733 : List Nat := [1, 5, 1, 1, 2, 4, 1, 3, 5]
def baseStart_2458733 : Nat := 118140960795 + 2458733 * 2 ^ 59
def prefixEnd_2458733 : Nat := 4983230072969 + 3 ^ 40 * 2458733 * 2
def baseEnd_2458733 : Nat := 140279092230137103281111

theorem tailTrace_2458733 : CollatzResearch.WordTrace tailWord_2458733 prefixEnd_2458733 140279092230137103281111 := by
  unfold tailWord_2458733
  simp only [CollatzResearch.WordTrace]
  refine ⟨89677359801437734010116853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59784906534291822673411235 89677359801437734010116853)
  ·
    refine ⟨8407252481384787563448455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89677359801437734010116853 8407252481384787563448455)
    ·
      refine ⟨12610878722077181345172683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8407252481384787563448455 12610878722077181345172683)
      ·
        refine ⟨18916318083115772017759025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12610878722077181345172683 18916318083115772017759025)
        ·
          refine ⟨14187238562336829013319269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18916318083115772017759025 14187238562336829013319269)
          ·
            refine ⟨2660107230438155439997363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14187238562336829013319269 2660107230438155439997363)
            ·
              refine ⟨3990160845657233159996045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2660107230438155439997363 3990160845657233159996045)
              ·
                refine ⟨1496310317121462434998517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3990160845657233159996045 1496310317121462434998517)
                ·
                  refine ⟨140279092230137103281111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1496310317121462434998517 140279092230137103281111)
                  ·
                    rfl

theorem cell23_2458733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_2458733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458733 prefixEnd_2458733 := by exact prefixLift 2458733
  have htrace : WordTrace (prefixWord ++ tailWord_2458733) baseStart_2458733 baseEnd_2458733 := by
    simpa [prefixWord, tailWord_2458733, baseEnd_2458733] using wordTrace_append hprefix tailTrace_2458733
  have hstable : (prefixWord ++ tailWord_2458733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458733).length < 2 ^ (prefixWord ++ tailWord_2458733).sum := by decide
  have hdescent : baseEnd_2458733 < baseStart_2458733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458783 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2458783 : Nat := 118140960795 + 2458783 * 2 ^ 59
def prefixEnd_2458783 : Nat := 4983230072969 + 3 ^ 40 * 2458783 * 2
def baseEnd_2458783 : Nat := 1262537504103958733904769

theorem tailTrace_2458783 : CollatzResearch.WordTrace tailWord_2458783 prefixEnd_2458783 1262537504103958733904769 := by
  unfold tailWord_2458783
  simp only [CollatzResearch.WordTrace]
  refine ⟨89679183451256592549437003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59786122300837728366291335 89679183451256592549437003)
  ·
    refine ⟨134518775176884888824155505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89679183451256592549437003 134518775176884888824155505)
    ·
      refine ⟨100889081382663666618116629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134518775176884888824155505 100889081382663666618116629)
      ·
        refine ⟨4729175689812359372724217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100889081382663666618116629 4729175689812359372724217)
        ·
          refine ⟨3546881767359269529543163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4729175689812359372724217 3546881767359269529543163)
          ·
            refine ⟨5320322651038904294314745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3546881767359269529543163 5320322651038904294314745)
            ·
              refine ⟨3990241988279178220736059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5320322651038904294314745 3990241988279178220736059)
              ·
                refine ⟨5985362982418767331104089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3990241988279178220736059 5985362982418767331104089)
                ·
                  refine ⟨4489022236814075498328067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5985362982418767331104089 4489022236814075498328067)
                  ·
                    refine ⟨6733533355221113247492101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4489022236814075498328067 6733533355221113247492101)
                    ·
                      refine ⟨1262537504103958733904769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6733533355221113247492101 1262537504103958733904769)
                      ·
                        rfl

theorem cell23_2458783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2458783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458783 prefixEnd_2458783 := by exact prefixLift 2458783
  have htrace : WordTrace (prefixWord ++ tailWord_2458783) baseStart_2458783 baseEnd_2458783 := by
    simpa [prefixWord, tailWord_2458783, baseEnd_2458783] using wordTrace_append hprefix tailTrace_2458783
  have hstable : (prefixWord ++ tailWord_2458783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458783).length < 2 ^ (prefixWord ++ tailWord_2458783).sum := by decide
  have hdescent : baseEnd_2458783 < baseStart_2458783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458853 : List Nat := [1, 3, 1, 4, 3, 1, 1, 3, 1, 5]
def baseStart_2458853 : Nat := 118140960795 + 2458853 * 2 ^ 59
def prefixEnd_2458853 : Nat := 4983230072969 + 3 ^ 40 * 2458853 * 2
def baseEnd_2458853 : Nat := 420857815916591153343149

theorem tailTrace_2458853 : CollatzResearch.WordTrace tailWord_2458853 prefixEnd_2458853 420857815916591153343149 := by
  unfold tailWord_2458853
  simp only [CollatzResearch.WordTrace]
  refine ⟨89681736561002994504485213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59787824374001996336323475 89681736561002994504485213)
  ·
    refine ⟨33630651210376122939181955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89681736561002994504485213 33630651210376122939181955)
    ·
      refine ⟨50445976815564184408772933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33630651210376122939181955 50445976815564184408772933)
      ·
        refine ⟨9458620652918284576644925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50445976815564184408772933 9458620652918284576644925)
        ·
          refine ⟨3546982744844356716241847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9458620652918284576644925 3546982744844356716241847)
          ·
            refine ⟨5320474117266535074362771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3546982744844356716241847 5320474117266535074362771)
            ·
              refine ⟨7980711175899802611544157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5320474117266535074362771 7980711175899802611544157)
              ·
                refine ⟨2992766690962425979329059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7980711175899802611544157 2992766690962425979329059)
                ·
                  refine ⟨4489150036443638968993589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2992766690962425979329059 4489150036443638968993589)
                  ·
                    refine ⟨420857815916591153343149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4489150036443638968993589 420857815916591153343149)
                    ·
                      rfl

theorem cell23_2458853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_2458853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458853 prefixEnd_2458853 := by exact prefixLift 2458853
  have htrace : WordTrace (prefixWord ++ tailWord_2458853) baseStart_2458853 baseEnd_2458853 := by
    simpa [prefixWord, tailWord_2458853, baseEnd_2458853] using wordTrace_append hprefix tailTrace_2458853
  have hstable : (prefixWord ++ tailWord_2458853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458853).length < 2 ^ (prefixWord ++ tailWord_2458853).sum := by decide
  have hdescent : baseEnd_2458853 < baseStart_2458853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458939 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 8, 6]
def baseStart_2458939 : Nat := 118140960795 + 2458939 * 2 ^ 59
def prefixEnd_2458939 : Nat := 4983230072969 + 3 ^ 40 * 2458939 * 2
def baseEnd_2458939 : Nat := 420872535695353374518017

theorem tailTrace_2458939 : CollatzResearch.WordTrace tailWord_2458939 prefixEnd_2458939 420872535695353374518017 := by
  unfold tailWord_2458939
  simp only [CollatzResearch.WordTrace]
  refine ⟨89684873238691431192115871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59789915492460954128077247 89684873238691431192115871)
  ·
    refine ⟨134527309858037146788173807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89684873238691431192115871 134527309858037146788173807)
    ·
      refine ⟨201790964787055720182260711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134527309858037146788173807 201790964787055720182260711)
      ·
        refine ⟨302686447180583580273391067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201790964787055720182260711 302686447180583580273391067)
        ·
          refine ⟨454029670770875370410086601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302686447180583580273391067 454029670770875370410086601)
          ·
            refine ⟨340522253078156527807564951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454029670770875370410086601 340522253078156527807564951)
            ·
              refine ⟨510783379617234791711347427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340522253078156527807564951 510783379617234791711347427)
              ·
                refine ⟨766175069425852187567021141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510783379617234791711347427 766175069425852187567021141)
                ·
                  refine ⟨8978614094834205323051029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 766175069425852187567021141 8978614094834205323051029)
                  ·
                    refine ⟨420872535695353374518017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8978614094834205323051029 420872535695353374518017)
                    ·
                      rfl

theorem cell23_2458939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 6].length) (baseStart_2458939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458939 prefixEnd_2458939 := by exact prefixLift 2458939
  have htrace : WordTrace (prefixWord ++ tailWord_2458939) baseStart_2458939 baseEnd_2458939 := by
    simpa [prefixWord, tailWord_2458939, baseEnd_2458939] using wordTrace_append hprefix tailTrace_2458939
  have hstable : (prefixWord ++ tailWord_2458939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458939).length < 2 ^ (prefixWord ++ tailWord_2458939).sum := by decide
  have hdescent : baseEnd_2458939 < baseStart_2458939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458940 : List Nat := [2, 2, 2, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_2458940 : Nat := 118140960795 + 2458940 * 2 ^ 59
def prefixEnd_2458940 : Nat := 4983230072969 + 3 ^ 40 * 2458940 * 2
def baseEnd_2458940 : Nat := 1262618120566714619641547

theorem tailTrace_2458940 : CollatzResearch.WordTrace tailWord_2458940 prefixEnd_2458940 1262618120566714619641547 := by
  unfold tailWord_2458940
  simp only [CollatzResearch.WordTrace]
  refine ⟨44842454855843904181451137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59789939807791872241934849 44842454855843904181451137)
  ·
    refine ⟨33631841141882928136088353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44842454855843904181451137 33631841141882928136088353)
    ·
      refine ⟨25223880856412196102066265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33631841141882928136088353 25223880856412196102066265)
      ·
        refine ⟨18917910642309147076549699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25223880856412196102066265 18917910642309147076549699)
        ·
          refine ⟨28376865963463720614824549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18917910642309147076549699 28376865963463720614824549)
          ·
            refine ⟨5320662368149447615279603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28376865963463720614824549 5320662368149447615279603)
            ·
              refine ⟨7980993552224171422919405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5320662368149447615279603 7980993552224171422919405)
              ·
                refine ⟨2992872582084064283594777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7980993552224171422919405 2992872582084064283594777)
                ·
                  refine ⟨2244654436563048212696083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2992872582084064283594777 2244654436563048212696083)
                  ·
                    refine ⟨3366981654844572319044125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2244654436563048212696083 3366981654844572319044125)
                    ·
                      refine ⟨1262618120566714619641547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3366981654844572319044125 1262618120566714619641547)
                      ·
                        rfl

theorem cell23_2458940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_2458940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458940 prefixEnd_2458940 := by exact prefixLift 2458940
  have htrace : WordTrace (prefixWord ++ tailWord_2458940) baseStart_2458940 baseEnd_2458940 := by
    simpa [prefixWord, tailWord_2458940, baseEnd_2458940] using wordTrace_append hprefix tailTrace_2458940
  have hstable : (prefixWord ++ tailWord_2458940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458940).length < 2 ^ (prefixWord ++ tailWord_2458940).sum := by decide
  have hdescent : baseEnd_2458940 < baseStart_2458940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458957 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2458957 : Nat := 118140960795 + 2458957 * 2 ^ 59
def prefixEnd_2458957 : Nat := 4983230072969 + 3 ^ 40 * 2458957 * 2
def baseEnd_2458957 : Nat := 1262626849737841053128969

theorem tailTrace_2458957 : CollatzResearch.WordTrace tailWord_2458957 prefixEnd_2458957 1262626849737841053128969 := by
  unfold tailWord_2458957
  simp only [CollatzResearch.WordTrace]
  refine ⟨89685529752626220266271125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59790353168417480177514083 89685529752626220266271125)
  ·
    refine ⟨4204009207154354074981459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89685529752626220266271125 4204009207154354074981459)
    ·
      refine ⟨6306013810731531112472189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4204009207154354074981459 6306013810731531112472189)
      ·
        refine ⟨2364755179024324167177071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6306013810731531112472189 2364755179024324167177071)
        ·
          refine ⟨3547132768536486250765607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2364755179024324167177071 3547132768536486250765607)
          ·
            refine ⟨5320699152804729376148411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547132768536486250765607 5320699152804729376148411)
            ·
              refine ⟨7981048729207094064222617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5320699152804729376148411 7981048729207094064222617)
              ·
                refine ⟨5985786546905320548166963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7981048729207094064222617 5985786546905320548166963)
                ·
                  refine ⟨8978679820357980822250445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5985786546905320548166963 8978679820357980822250445)
                  ·
                    refine ⟨3367004932634242808343917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8978679820357980822250445 3367004932634242808343917)
                    ·
                      refine ⟨1262626849737841053128969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3367004932634242808343917 1262626849737841053128969)
                      ·
                        rfl

theorem cell23_2458957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2458957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458957 prefixEnd_2458957 := by exact prefixLift 2458957
  have htrace : WordTrace (prefixWord ++ tailWord_2458957) baseStart_2458957 baseEnd_2458957 := by
    simpa [prefixWord, tailWord_2458957, baseEnd_2458957] using wordTrace_append hprefix tailTrace_2458957
  have hstable : (prefixWord ++ tailWord_2458957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458957).length < 2 ^ (prefixWord ++ tailWord_2458957).sum := by decide
  have hdescent : baseEnd_2458957 < baseStart_2458957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458959 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 6]
def baseStart_2458959 : Nat := 118140960795 + 2458959 * 2 ^ 59
def prefixEnd_2458959 : Nat := 4983230072969 + 3 ^ 40 * 2458959 * 2
def baseEnd_2458959 : Nat := 1262627876699150045303959

theorem tailTrace_2458959 : CollatzResearch.WordTrace tailWord_2458959 prefixEnd_2458959 1262627876699150045303959 := by
  unfold tailWord_2458959
  simp only [CollatzResearch.WordTrace]
  refine ⟨89685602698618974607843931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59790401799079316405229287 89685602698618974607843931)
  ·
    refine ⟨134528404047928461911765897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89685602698618974607843931 134528404047928461911765897)
    ·
      refine ⟨100896303035946346433824423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134528404047928461911765897 100896303035946346433824423)
      ·
        refine ⟨151344454553919519650736635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100896303035946346433824423 151344454553919519650736635)
        ·
          refine ⟨227016681830879279476104953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151344454553919519650736635 227016681830879279476104953)
          ·
            refine ⟨170262511373159459607078715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227016681830879279476104953 170262511373159459607078715)
            ·
              refine ⟨255393767059739189410618073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170262511373159459607078715 255393767059739189410618073)
              ·
                refine ⟨191545325294804392057963555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255393767059739189410618073 191545325294804392057963555)
                ·
                  refine ⟨287317987942206588086945333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191545325294804392057963555 287317987942206588086945333)
                  ·
                    refine ⟨26936061369581867633151125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 287317987942206588086945333 26936061369581867633151125)
                    ·
                      refine ⟨1262627876699150045303959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26936061369581867633151125 1262627876699150045303959)
                      ·
                        rfl

theorem cell23_2458959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_2458959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458959 prefixEnd_2458959 := by exact prefixLift 2458959
  have htrace : WordTrace (prefixWord ++ tailWord_2458959) baseStart_2458959 baseEnd_2458959 := by
    simpa [prefixWord, tailWord_2458959, baseEnd_2458959] using wordTrace_append hprefix tailTrace_2458959
  have hstable : (prefixWord ++ tailWord_2458959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458959).length < 2 ^ (prefixWord ++ tailWord_2458959).sum := by decide
  have hdescent : baseEnd_2458959 < baseStart_2458959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458963 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 1, 4, 2]
def baseStart_2458963 : Nat := 118140960795 + 2458963 * 2 ^ 59
def prefixEnd_2458963 : Nat := 4983230072969 + 3 ^ 40 * 2458963 * 2
def baseEnd_2458963 : Nat := 1262629930621768029653941

theorem tailTrace_2458963 : CollatzResearch.WordTrace tailWord_2458963 prefixEnd_2458963 1262629930621768029653941 := by
  unfold tailWord_2458963
  simp only [CollatzResearch.WordTrace]
  refine ⟨89685748590604483290989543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59790499060402988860659695 89685748590604483290989543)
  ·
    refine ⟨134528622885906724936484315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89685748590604483290989543 134528622885906724936484315)
    ·
      refine ⟨201792934328860087404726473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134528622885906724936484315 201792934328860087404726473)
      ·
        refine ⟨151344700746645065553544855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201792934328860087404726473 151344700746645065553544855)
        ·
          refine ⟨227017051119967598330317283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151344700746645065553544855 227017051119967598330317283)
          ·
            refine ⟨340525576679951397495475925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227017051119967598330317283 340525576679951397495475925)
            ·
              refine ⟨7981068203436360878800217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 340525576679951397495475925 7981068203436360878800217)
              ·
                refine ⟨5985801152577270659100163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7981068203436360878800217 5985801152577270659100163)
                ·
                  refine ⟨8978701728865905988650245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5985801152577270659100163 8978701728865905988650245)
                  ·
                    refine ⟨1683506574162357372871921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8978701728865905988650245 1683506574162357372871921)
                    ·
                      refine ⟨1262629930621768029653941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1683506574162357372871921 1262629930621768029653941)
                      ·
                        rfl

theorem cell23_2458963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 4, 2].length) (baseStart_2458963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458963 prefixEnd_2458963 := by exact prefixLift 2458963
  have htrace : WordTrace (prefixWord ++ tailWord_2458963) baseStart_2458963 baseEnd_2458963 := by
    simpa [prefixWord, tailWord_2458963, baseEnd_2458963] using wordTrace_append hprefix tailTrace_2458963
  have hstable : (prefixWord ++ tailWord_2458963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458963).length < 2 ^ (prefixWord ++ tailWord_2458963).sum := by decide
  have hdescent : baseEnd_2458963 < baseStart_2458963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458967 : List Nat := [1, 1, 3, 2, 3, 3, 3, 1, 1, 3, 2]
def baseStart_2458967 : Nat := 118140960795 + 2458967 * 2 ^ 59
def prefixEnd_2458967 : Nat := 4983230072969 + 3 ^ 40 * 2458967 * 2
def baseEnd_2458967 : Nat := 1262631984544386014003923

theorem tailTrace_2458967 : CollatzResearch.WordTrace tailWord_2458967 prefixEnd_2458967 1262631984544386014003923 := by
  unfold tailWord_2458967
  simp only [CollatzResearch.WordTrace]
  refine ⟨89685894482589991974135155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59790596321726661316090103 89685894482589991974135155)
  ·
    refine ⟨134528841723884987961202733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89685894482589991974135155 134528841723884987961202733)
    ·
      refine ⟨50448315646456870485451025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134528841723884987961202733 50448315646456870485451025)
      ·
        refine ⟨37836236734842652864088269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50448315646456870485451025 37836236734842652864088269)
        ·
          refine ⟨14188588775565994824033101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37836236734842652864088269 14188588775565994824033101)
          ·
            refine ⟨5320720790837248059012413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14188588775565994824033101 5320720790837248059012413)
            ·
              refine ⟨1995270296563968022129655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5320720790837248059012413 1995270296563968022129655)
              ·
                refine ⟨2992905444845952033194483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995270296563968022129655 2992905444845952033194483)
                ·
                  refine ⟨4489358167268928049791725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2992905444845952033194483 4489358167268928049791725)
                  ·
                    refine ⟨1683509312725848018671897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4489358167268928049791725 1683509312725848018671897)
                    ·
                      refine ⟨1262631984544386014003923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1683509312725848018671897 1262631984544386014003923)
                      ·
                        rfl

theorem cell23_2458967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_2458967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458967 prefixEnd_2458967 := by exact prefixLift 2458967
  have htrace : WordTrace (prefixWord ++ tailWord_2458967) baseStart_2458967 baseEnd_2458967 := by
    simpa [prefixWord, tailWord_2458967, baseEnd_2458967] using wordTrace_append hprefix tailTrace_2458967
  have hstable : (prefixWord ++ tailWord_2458967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458967).length < 2 ^ (prefixWord ++ tailWord_2458967).sum := by decide
  have hdescent : baseEnd_2458967 < baseStart_2458967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458990 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_2458990 : Nat := 118140960795 + 2458990 * 2 ^ 59
def prefixEnd_2458990 : Nat := 4983230072969 + 3 ^ 40 * 2458990 * 2
def baseEnd_2458990 : Nat := 420881264866479808005439

theorem tailTrace_2458990 : CollatzResearch.WordTrace tailWord_2458990 prefixEnd_2458990 420881264866479808005439 := by
  unfold tailWord_2458990
  simp only [CollatzResearch.WordTrace]
  refine ⟨11210841670188333362777803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59791155574337777934814949 11210841670188333362777803)
  ·
    refine ⟨16816262505282500044166705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11210841670188333362777803 16816262505282500044166705)
    ·
      refine ⟨12612196878961875033125029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16816262505282500044166705 12612196878961875033125029)
      ·
        refine ⟨2364786914805351568710943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12612196878961875033125029 2364786914805351568710943)
        ·
          refine ⟨3547180372208027353066415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2364786914805351568710943 3547180372208027353066415)
          ·
            refine ⟨5320770558312041029599623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547180372208027353066415 5320770558312041029599623)
            ·
              refine ⟨7981155837468061544399435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5320770558312041029599623 7981155837468061544399435)
              ·
                refine ⟨11971733756202092316599153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7981155837468061544399435 11971733756202092316599153)
                ·
                  refine ⟨8978800317151569237449365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11971733756202092316599153 8978800317151569237449365)
                  ·
                    refine ⟨420881264866479808005439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8978800317151569237449365 420881264866479808005439)
                    ·
                      rfl

theorem cell23_2458990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_2458990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458990 prefixEnd_2458990 := by exact prefixLift 2458990
  have htrace : WordTrace (prefixWord ++ tailWord_2458990) baseStart_2458990 baseEnd_2458990 := by
    simpa [prefixWord, tailWord_2458990, baseEnd_2458990] using wordTrace_append hprefix tailTrace_2458990
  have hstable : (prefixWord ++ tailWord_2458990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458990).length < 2 ^ (prefixWord ++ tailWord_2458990).sum := by decide
  have hdescent : baseEnd_2458990 < baseStart_2458990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458997 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_2458997 : Nat := 118140960795 + 2458997 * 2 ^ 59
def prefixEnd_2458997 : Nat := 4983230072969 + 3 ^ 40 * 2458997 * 2
def baseEnd_2458997 : Nat := 1262647388964020896628785

theorem tailTrace_2458997 : CollatzResearch.WordTrace tailWord_2458997 prefixEnd_2458997 1262647388964020896628785 := by
  unfold tailWord_2458997
  simp only [CollatzResearch.WordTrace]
  refine ⟨89686988672481307097727245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59791325781654204731818163 89686988672481307097727245)
  ·
    refine ⟨33632620752180490161647717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89686988672481307097727245 33632620752180490161647717)
    ·
      refine ⟨6306116391033841905308947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33632620752180490161647717 6306116391033841905308947)
      ·
        refine ⟨9459174586550762857963421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6306116391033841905308947 9459174586550762857963421)
        ·
          refine ⟨3547190469956536071736283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9459174586550762857963421 3547190469956536071736283)
          ·
            refine ⟨5320785704934804107604425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547190469956536071736283 5320785704934804107604425)
            ·
              refine ⟨3990589278701103080703319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5320785704934804107604425 3990589278701103080703319)
              ·
                refine ⟨5985883918051654621054979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3990589278701103080703319 5985883918051654621054979)
                ·
                  refine ⟨8978825877077481931582469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5985883918051654621054979 8978825877077481931582469)
                  ·
                    refine ⟨1683529851952027862171713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8978825877077481931582469 1683529851952027862171713)
                    ·
                      refine ⟨1262647388964020896628785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1683529851952027862171713 1262647388964020896628785)
                      ·
                        rfl

theorem cell23_2458997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_2458997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2458997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2458997 prefixEnd_2458997 := by exact prefixLift 2458997
  have htrace : WordTrace (prefixWord ++ tailWord_2458997) baseStart_2458997 baseEnd_2458997 := by
    simpa [prefixWord, tailWord_2458997, baseEnd_2458997] using wordTrace_append hprefix tailTrace_2458997
  have hstable : (prefixWord ++ tailWord_2458997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458997).length < 2 ^ (prefixWord ++ tailWord_2458997).sum := by decide
  have hdescent : baseEnd_2458997 < baseStart_2458997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459063 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 3, 4]
def baseStart_2459063 : Nat := 118140960795 + 2459063 * 2 ^ 59
def prefixEnd_2459063 : Nat := 4983230072969 + 3 ^ 40 * 2459063 * 2
def baseEnd_2459063 : Nat := 420893759562405879467827

theorem tailTrace_2459063 : CollatzResearch.WordTrace tailWord_2459063 prefixEnd_2459063 420893759562405879467827 := by
  unfold tailWord_2459063
  simp only [CollatzResearch.WordTrace]
  refine ⟨89689395890242200369629843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59792930593494800246419895 89689395890242200369629843)
  ·
    refine ⟨134534093835363300554444765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89689395890242200369629843 134534093835363300554444765)
    ·
      refine ⟨50450285188261237707916787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134534093835363300554444765 50450285188261237707916787)
      ·
        refine ⟨75675427782391856561875181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50450285188261237707916787 75675427782391856561875181)
        ·
          refine ⟨28378285418396946210703193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75675427782391856561875181 28378285418396946210703193)
          ·
            refine ⟨21283714063797709658027395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28378285418396946210703193 21283714063797709658027395)
            ·
              refine ⟨31925571095696564487041093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21283714063797709658027395 31925571095696564487041093)
              ·
                refine ⟨5986044580443105841320205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31925571095696564487041093 5986044580443105841320205)
                ·
                  refine ⟨2244766717666164690495077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5986044580443105841320205 2244766717666164690495077)
                  ·
                    refine ⟨420893759562405879467827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2244766717666164690495077 420893759562405879467827)
                    ·
                      rfl

theorem cell23_2459063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_2459063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459063 prefixEnd_2459063 := by exact prefixLift 2459063
  have htrace : WordTrace (prefixWord ++ tailWord_2459063) baseStart_2459063 baseEnd_2459063 := by
    simpa [prefixWord, tailWord_2459063, baseEnd_2459063] using wordTrace_append hprefix tailTrace_2459063
  have hstable : (prefixWord ++ tailWord_2459063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459063).length < 2 ^ (prefixWord ++ tailWord_2459063).sum := by decide
  have hdescent : baseEnd_2459063 < baseStart_2459063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459093 : List Nat := [1, 3, 2, 3, 1, 1, 2, 4, 6]
def baseStart_2459093 : Nat := 118140960795 + 2459093 * 2 ^ 59
def prefixEnd_2459093 : Nat := 4983230072969 + 3 ^ 40 * 2459093 * 2
def baseEnd_2459093 : Nat := 140299631456316946780927

theorem tailTrace_2459093 : CollatzResearch.WordTrace tailWord_2459093 prefixEnd_2459093 140299631456316946780927 := by
  unfold tailWord_2459093
  simp only [CollatzResearch.WordTrace]
  refine ⟨89690490080133515493221933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59793660053422343662147955 89690490080133515493221933)
  ·
    refine ⟨33633933780050068309958225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89690490080133515493221933 33633933780050068309958225)
    ·
      refine ⟨25225450335037551232468669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33633933780050068309958225 25225450335037551232468669)
      ·
        refine ⟨9459543875639081712175751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25225450335037551232468669 9459543875639081712175751)
        ·
          refine ⟨14189315813458622568263627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9459543875639081712175751 14189315813458622568263627)
          ·
            refine ⟨21283973720187933852395441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14189315813458622568263627 21283973720187933852395441)
            ·
              refine ⟨15962980290140950389296581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21283973720187933852395441 15962980290140950389296581)
              ·
                refine ⟨2993058804401428197993109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15962980290140950389296581 2993058804401428197993109)
                ·
                  refine ⟨140299631456316946780927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2993058804401428197993109 140299631456316946780927)
                  ·
                    rfl

theorem cell23_2459093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_2459093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459093 prefixEnd_2459093 := by exact prefixLift 2459093
  have htrace : WordTrace (prefixWord ++ tailWord_2459093) baseStart_2459093 baseEnd_2459093 := by
    simpa [prefixWord, tailWord_2459093, baseEnd_2459093] using wordTrace_append hprefix tailTrace_2459093
  have hstable : (prefixWord ++ tailWord_2459093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459093).length < 2 ^ (prefixWord ++ tailWord_2459093).sum := by decide
  have hdescent : baseEnd_2459093 < baseStart_2459093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459096 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2459096 : Nat := 118140960795 + 2459096 * 2 ^ 59
def prefixEnd_2459096 : Nat := 4983230072969 + 3 ^ 40 * 2459096 * 2
def baseEnd_2459096 : Nat := 1262698223548816009290829

theorem tailTrace_2459096 : CollatzResearch.WordTrace tailWord_2459096 prefixEnd_2459096 1262698223548816009290829 := by
  unfold tailWord_2459096
  simp only [CollatzResearch.WordTrace]
  refine ⟨44845299749561323502790571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59793732999415098003720761 44845299749561323502790571)
  ·
    refine ⟨67267949624341985254185857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44845299749561323502790571 67267949624341985254185857)
    ·
      refine ⟨50450962218256488940639393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67267949624341985254185857 50450962218256488940639393)
      ·
        refine ⟨37838221663692366705479545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50450962218256488940639393 37838221663692366705479545)
        ·
          refine ⟨28378666247769275029109659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37838221663692366705479545 28378666247769275029109659)
          ·
            refine ⟨42567999371653912543664489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28378666247769275029109659 42567999371653912543664489)
            ·
              refine ⟨31925999528740434407748367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42567999371653912543664489 31925999528740434407748367)
              ·
                refine ⟨47888999293110651611622551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31925999528740434407748367 47888999293110651611622551)
                ·
                  refine ⟨71833498939665977417433827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47888999293110651611622551 71833498939665977417433827)
                  ·
                    refine ⟨107750248409498966126150741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71833498939665977417433827 107750248409498966126150741)
                    ·
                      refine ⟨1262698223548816009290829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 107750248409498966126150741 1262698223548816009290829)
                      ·
                        rfl

theorem cell23_2459096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2459096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459096 prefixEnd_2459096 := by exact prefixLift 2459096
  have htrace : WordTrace (prefixWord ++ tailWord_2459096) baseStart_2459096 baseEnd_2459096 := by
    simpa [prefixWord, tailWord_2459096, baseEnd_2459096] using wordTrace_append hprefix tailTrace_2459096
  have hstable : (prefixWord ++ tailWord_2459096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459096).length < 2 ^ (prefixWord ++ tailWord_2459096).sum := by decide
  have hdescent : baseEnd_2459096 < baseStart_2459096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459116 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_2459116 : Nat := 118140960795 + 2459116 * 2 ^ 59
def prefixEnd_2459116 : Nat := 4983230072969 + 3 ^ 40 * 2459116 * 2
def baseEnd_2459116 : Nat := 1262708493161905931040737

theorem tailTrace_2459116 : CollatzResearch.WordTrace tailWord_2459116 prefixEnd_2459116 1262708493161905931040737 := by
  unfold tailWord_2459116
  simp only [CollatzResearch.WordTrace]
  refine ⟨44845664479525095210654601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59794219306033460280872801 44845664479525095210654601)
  ·
    refine ⟨33634248359643821407990951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44845664479525095210654601 33634248359643821407990951)
    ·
      refine ⟨50451372539465732111986427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33634248359643821407990951 50451372539465732111986427)
      ·
        refine ⟨75677058809198598167979641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50451372539465732111986427 75677058809198598167979641)
        ·
          refine ⟨56757794106898948625984731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75677058809198598167979641 56757794106898948625984731)
          ·
            refine ⟨85136691160348422938977097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56757794106898948625984731 85136691160348422938977097)
            ·
              refine ⟨63852518370261317204232823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85136691160348422938977097 63852518370261317204232823)
              ·
                refine ⟨95778777555391975806349235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63852518370261317204232823 95778777555391975806349235)
                ·
                  refine ⟨143668166333087963709523853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95778777555391975806349235 143668166333087963709523853)
                  ·
                    refine ⟨53875562374907986391071445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143668166333087963709523853 53875562374907986391071445)
                    ·
                      refine ⟨1262708493161905931040737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53875562374907986391071445 1262708493161905931040737)
                      ·
                        rfl

theorem cell23_2459116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_2459116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459116 prefixEnd_2459116 := by exact prefixLift 2459116
  have htrace : WordTrace (prefixWord ++ tailWord_2459116) baseStart_2459116 baseEnd_2459116 := by
    simpa [prefixWord, tailWord_2459116, baseEnd_2459116] using wordTrace_append hprefix tailTrace_2459116
  have hstable : (prefixWord ++ tailWord_2459116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459116).length < 2 ^ (prefixWord ++ tailWord_2459116).sum := by decide
  have hdescent : baseEnd_2459116 < baseStart_2459116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459123 : List Nat := [1, 1, 1, 2, 2, 2, 2, 6, 1, 5]
def baseStart_2459123 : Nat := 118140960795 + 2459123 * 2 ^ 59
def prefixEnd_2459123 : Nat := 4983230072969 + 3 ^ 40 * 2459123 * 2
def baseEnd_2459123 : Nat := 420904029175495801217735

theorem tailTrace_2459123 : CollatzResearch.WordTrace tailWord_2459123 prefixEnd_2459123 420904029175495801217735 := by
  unfold tailWord_2459123
  simp only [CollatzResearch.WordTrace]
  refine ⟨89691584270024830616814023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59794389513349887077876015 89691584270024830616814023)
  ·
    refine ⟨134537376405037245925221035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89691584270024830616814023 134537376405037245925221035)
    ·
      refine ⟨201806064607555868887831553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134537376405037245925221035 201806064607555868887831553)
      ·
        refine ⟨151354548455666901665873665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201806064607555868887831553 151354548455666901665873665)
        ·
          refine ⟨113515911341750176249405249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151354548455666901665873665 113515911341750176249405249)
          ·
            refine ⟨85136933506312632187053937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113515911341750176249405249 85136933506312632187053937)
            ·
              refine ⟨63852700129734474140290453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85136933506312632187053937 63852700129734474140290453)
              ·
                refine ⟨2993095318581303475326115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63852700129734474140290453 2993095318581303475326115)
                ·
                  refine ⟨4489642977871955212989173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993095318581303475326115 4489642977871955212989173)
                  ·
                    refine ⟨420904029175495801217735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4489642977871955212989173 420904029175495801217735)
                    ·
                      rfl

theorem cell23_2459123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 5].length) (baseStart_2459123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459123 prefixEnd_2459123 := by exact prefixLift 2459123
  have htrace : WordTrace (prefixWord ++ tailWord_2459123) baseStart_2459123 baseEnd_2459123 := by
    simpa [prefixWord, tailWord_2459123, baseEnd_2459123] using wordTrace_append hprefix tailTrace_2459123
  have hstable : (prefixWord ++ tailWord_2459123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459123).length < 2 ^ (prefixWord ++ tailWord_2459123).sum := by decide
  have hdescent : baseEnd_2459123 < baseStart_2459123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459240 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2459240 : Nat := 118140960795 + 2459240 * 2 ^ 59
def prefixEnd_2459240 : Nat := 4983230072969 + 3 ^ 40 * 2459240 * 2
def baseEnd_2459240 : Nat := 1262772164763063445890167

theorem tailTrace_2459240 : CollatzResearch.WordTrace tailWord_2459240 prefixEnd_2459240 1262772164763063445890167 := by
  unfold tailWord_2459240
  simp only [CollatzResearch.WordTrace]
  refine ⟨44847925805300479799411587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59797234407067306399215449 44847925805300479799411587)
  ·
    refine ⟨67271888707950719699117381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44847925805300479799411587 67271888707950719699117381)
    ·
      refine ⟨12613479132740759943584509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67271888707950719699117381 12613479132740759943584509)
      ·
        refine ⟨4730054674777784978844191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12613479132740759943584509 4730054674777784978844191)
        ·
          refine ⟨7095082012166677468266287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4730054674777784978844191 7095082012166677468266287)
          ·
            refine ⟨10642623018250016202399431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7095082012166677468266287 10642623018250016202399431)
            ·
              refine ⟨15963934527375024303599147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10642623018250016202399431 15963934527375024303599147)
              ·
                refine ⟨23945901791062536455398721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15963934527375024303599147 23945901791062536455398721)
                ·
                  refine ⟨17959426343296902341549041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23945901791062536455398721 17959426343296902341549041)
                  ·
                    refine ⟨13469569757472676756161781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17959426343296902341549041 13469569757472676756161781)
                    ·
                      refine ⟨1262772164763063445890167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13469569757472676756161781 1262772164763063445890167)
                      ·
                        rfl

theorem cell23_2459240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2459240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459240 prefixEnd_2459240 := by exact prefixLift 2459240
  have htrace : WordTrace (prefixWord ++ tailWord_2459240) baseStart_2459240 baseEnd_2459240 := by
    simpa [prefixWord, tailWord_2459240, baseEnd_2459240] using wordTrace_append hprefix tailTrace_2459240
  have hstable : (prefixWord ++ tailWord_2459240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459240).length < 2 ^ (prefixWord ++ tailWord_2459240).sum := by decide
  have hdescent : baseEnd_2459240 < baseStart_2459240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459245 : List Nat := [1, 5, 1, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_2459245 : Nat := 118140960795 + 2459245 * 2 ^ 59
def prefixEnd_2459245 : Nat := 4983230072969 + 3 ^ 40 * 2459245 * 2
def baseEnd_2459245 : Nat := 1262774732166335926327645

theorem tailTrace_2459245 : CollatzResearch.WordTrace tailWord_2459245 prefixEnd_2459245 1262774732166335926327645 := by
  unfold tailWord_2459245
  simp only [CollatzResearch.WordTrace]
  refine ⟨89696033975582845452755189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59797355983721896968503459 89696033975582845452755189)
  ·
    refine ⟨8409003185210891761195799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89696033975582845452755189 8409003185210891761195799)
    ·
      refine ⟨12613504777816337641793699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8409003185210891761195799 12613504777816337641793699)
      ·
        refine ⟨18920257166724506462690549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12613504777816337641793699 18920257166724506462690549)
        ·
          refine ⟨1773774109380422480877239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18920257166724506462690549 1773774109380422480877239)
          ·
            refine ⟨2660661164070633721315859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1773774109380422480877239 2660661164070633721315859)
            ·
              refine ⟨3990991746105950581973789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2660661164070633721315859 3990991746105950581973789)
              ·
                refine ⟨1496621904789731468240171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3990991746105950581973789 1496621904789731468240171)
                ·
                  refine ⟨2244932857184597202360257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1496621904789731468240171 2244932857184597202360257)
                  ·
                    refine ⟨1683699642888447901770193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2244932857184597202360257 1683699642888447901770193)
                    ·
                      refine ⟨1262774732166335926327645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1683699642888447901770193 1262774732166335926327645)
                      ·
                        rfl

theorem cell23_2459245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_2459245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459245 prefixEnd_2459245 := by exact prefixLift 2459245
  have htrace : WordTrace (prefixWord ++ tailWord_2459245) baseStart_2459245 baseEnd_2459245 := by
    simpa [prefixWord, tailWord_2459245, baseEnd_2459245] using wordTrace_append hprefix tailTrace_2459245
  have hstable : (prefixWord ++ tailWord_2459245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459245).length < 2 ^ (prefixWord ++ tailWord_2459245).sum := by decide
  have hdescent : baseEnd_2459245 < baseStart_2459245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459318 : List Nat := [5, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_2459318 : Nat := 118140960795 + 2459318 * 2 ^ 59
def prefixEnd_2459318 : Nat := 4983230072969 + 3 ^ 40 * 2459318 * 2
def baseEnd_2459318 : Nat := 1262812216254114140714809

theorem tailTrace_2459318 : CollatzResearch.WordTrace tailWord_2459318 prefixEnd_2459318 1262812216254114140714809 := by
  unfold tailWord_2459318
  simp only [CollatzResearch.WordTrace]
  refine ⟨5606168531519898682510163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59799131002878919280108405 5606168531519898682510163)
  ·
    refine ⟨8409252797279848023765245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5606168531519898682510163 8409252797279848023765245)
    ·
      refine ⟨3153469798979943008911967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8409252797279848023765245 3153469798979943008911967)
      ·
        refine ⟨4730204698469914513367951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3153469798979943008911967 4730204698469914513367951)
        ·
          refine ⟨7095307047704871770051927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4730204698469914513367951 7095307047704871770051927)
          ·
            refine ⟨10642960571557307655077891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7095307047704871770051927 10642960571557307655077891)
            ·
              refine ⟨15964440857335961482616837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10642960571557307655077891 15964440857335961482616837)
              ·
                refine ⟨2993332660750492777990657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15964440857335961482616837 2993332660750492777990657)
                ·
                  refine ⟨2244999495562869583492993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2993332660750492777990657 2244999495562869583492993)
                  ·
                    refine ⟨1683749621672152187619745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2244999495562869583492993 1683749621672152187619745)
                    ·
                      refine ⟨1262812216254114140714809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1683749621672152187619745 1262812216254114140714809)
                      ·
                        rfl

theorem cell23_2459318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_2459318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459318 prefixEnd_2459318 := by exact prefixLift 2459318
  have htrace : WordTrace (prefixWord ++ tailWord_2459318) baseStart_2459318 baseEnd_2459318 := by
    simpa [prefixWord, tailWord_2459318, baseEnd_2459318] using wordTrace_append hprefix tailTrace_2459318
  have hstable : (prefixWord ++ tailWord_2459318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459318).length < 2 ^ (prefixWord ++ tailWord_2459318).sum := by decide
  have hdescent : baseEnd_2459318 < baseStart_2459318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459324 : List Nat := [2, 2, 2, 3, 1, 2, 4, 2, 5]
def baseStart_2459324 : Nat := 118140960795 + 2459324 * 2 ^ 59
def prefixEnd_2459324 : Nat := 4983230072969 + 3 ^ 40 * 2459324 * 2
def baseEnd_2459324 : Nat := 140312810793115679693309

theorem tailTrace_2459324 : CollatzResearch.WordTrace tailWord_2459324 prefixEnd_2459324 140312810793115679693309 := by
  unfold tailWord_2459324
  simp only [CollatzResearch.WordTrace]
  refine ⟨44849457671148320972440513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59799276894864427963254017 44849457671148320972440513)
  ·
    refine ⟨33637093253361240729330385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44849457671148320972440513 33637093253361240729330385)
    ·
      refine ⟨25227819940020930546997789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33637093253361240729330385 25227819940020930546997789)
      ·
        refine ⟨9460432477507848955124171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25227819940020930546997789 9460432477507848955124171)
        ·
          refine ⟨14190648716261773432686257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9460432477507848955124171 14190648716261773432686257)
          ·
            refine ⟨10642986537196330074514693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14190648716261773432686257 10642986537196330074514693)
            ·
              refine ⟨1995559975724311888971505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10642986537196330074514693 1995559975724311888971505)
              ·
                refine ⟨1496669981793233916728629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1995559975724311888971505 1496669981793233916728629)
                ·
                  refine ⟨140312810793115679693309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1496669981793233916728629 140312810793115679693309)
                  ·
                    rfl

theorem cell23_2459324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 5].length) (baseStart_2459324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459324 prefixEnd_2459324 := by exact prefixLift 2459324
  have htrace : WordTrace (prefixWord ++ tailWord_2459324) baseStart_2459324 baseEnd_2459324 := by
    simpa [prefixWord, tailWord_2459324, baseEnd_2459324] using wordTrace_append hprefix tailTrace_2459324
  have hstable : (prefixWord ++ tailWord_2459324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459324).length < 2 ^ (prefixWord ++ tailWord_2459324).sum := by decide
  have hdescent : baseEnd_2459324 < baseStart_2459324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459370 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2459370 : Nat := 118140960795 + 2459370 * 2 ^ 59
def prefixEnd_2459370 : Nat := 4983230072969 + 3 ^ 40 * 2459370 * 2
def baseEnd_2459370 : Nat := 1262838917248147937264569

theorem tailTrace_2459370 : CollatzResearch.WordTrace tailWord_2459370 prefixEnd_2459370 1262838917248147937264569 := by
  unfold tailWord_2459370
  simp only [CollatzResearch.WordTrace]
  refine ⟨22425148275032497950263891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59800395400086661200703709 22425148275032497950263891)
  ·
    refine ⟨33637722412548746925395837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22425148275032497950263891 33637722412548746925395837)
    ·
      refine ⟨12614145904705780097023439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33637722412548746925395837 12614145904705780097023439)
      ·
        refine ⟨18921218857058670145535159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12614145904705780097023439 18921218857058670145535159)
        ·
          refine ⟨28381828285588005218302739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18921218857058670145535159 28381828285588005218302739)
          ·
            refine ⟨42572742428382007827454109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28381828285588005218302739 42572742428382007827454109)
            ·
              refine ⟨15964778410643252935295291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42572742428382007827454109 15964778410643252935295291)
              ·
                refine ⟨23947167615964879402942937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15964778410643252935295291 23947167615964879402942937)
                ·
                  refine ⟨17960375711973659552207203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23947167615964879402942937 17960375711973659552207203)
                  ·
                    refine ⟨26940563567960489328310805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17960375711973659552207203 26940563567960489328310805)
                    ·
                      refine ⟨1262838917248147937264569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26940563567960489328310805 1262838917248147937264569)
                      ·
                        rfl

theorem cell23_2459370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2459370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459370 prefixEnd_2459370 := by exact prefixLift 2459370
  have htrace : WordTrace (prefixWord ++ tailWord_2459370) baseStart_2459370 baseEnd_2459370 := by
    simpa [prefixWord, tailWord_2459370, baseEnd_2459370] using wordTrace_append hprefix tailTrace_2459370
  have hstable : (prefixWord ++ tailWord_2459370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459370).length < 2 ^ (prefixWord ++ tailWord_2459370).sum := by decide
  have hdescent : baseEnd_2459370 < baseStart_2459370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459400 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_2459400 : Nat := 118140960795 + 2459400 * 2 ^ 59
def prefixEnd_2459400 : Nat := 4983230072969 + 3 ^ 40 * 2459400 * 2
def baseEnd_2459400 : Nat := 1262854321667782819889431

theorem tailTrace_2459400 : CollatzResearch.WordTrace tailWord_2459400 prefixEnd_2459400 1262854321667782819889431 := by
  unfold tailWord_2459400
  simp only [CollatzResearch.WordTrace]
  refine ⟨44850843645010653462323827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59801124860014204616431769 44850843645010653462323827)
  ·
    refine ⟨67276265467515980193485741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44850843645010653462323827 67276265467515980193485741)
    ·
      refine ⟨25228599550318492572557153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67276265467515980193485741 25228599550318492572557153)
      ·
        refine ⟨18921449662738869429417865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25228599550318492572557153 18921449662738869429417865)
        ·
          refine ⟨14191087247054152072063399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18921449662738869429417865 14191087247054152072063399)
          ·
            refine ⟨21286630870581228108095099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14191087247054152072063399 21286630870581228108095099)
            ·
              refine ⟨31929946305871842162142649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21286630870581228108095099 31929946305871842162142649)
              ·
                refine ⟨23947459729403881621606987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31929946305871842162142649 23947459729403881621606987)
                ·
                  refine ⟨35921189594105822432410481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23947459729403881621606987 35921189594105822432410481)
                  ·
                    refine ⟨26940892195579366824307861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35921189594105822432410481 26940892195579366824307861)
                    ·
                      refine ⟨1262854321667782819889431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26940892195579366824307861 1262854321667782819889431)
                      ·
                        rfl

theorem cell23_2459400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_2459400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459400 prefixEnd_2459400 := by exact prefixLift 2459400
  have htrace : WordTrace (prefixWord ++ tailWord_2459400) baseStart_2459400 baseEnd_2459400 := by
    simpa [prefixWord, tailWord_2459400, baseEnd_2459400] using wordTrace_append hprefix tailTrace_2459400
  have hstable : (prefixWord ++ tailWord_2459400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459400).length < 2 ^ (prefixWord ++ tailWord_2459400).sum := by decide
  have hdescent : baseEnd_2459400 < baseStart_2459400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459407 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 5, 1, 3]
def baseStart_2459407 : Nat := 118140960795 + 2459407 * 2 ^ 59
def prefixEnd_2459407 : Nat := 4983230072969 + 3 ^ 40 * 2459407 * 2
def baseEnd_2459407 : Nat := 1262857916032364292501899

theorem tailTrace_2459407 : CollatzResearch.WordTrace tailWord_2459407 prefixEnd_2459407 1262857916032364292501899 := by
  unfold tailWord_2459407
  simp only [CollatzResearch.WordTrace]
  refine ⟨89701942600995947120152475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59801295067330631413434983 89701942600995947120152475)
  ·
    refine ⟨134552913901493920680228713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89701942600995947120152475 134552913901493920680228713)
    ·
      refine ⟨100914685426120440510171535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134552913901493920680228713 100914685426120440510171535)
      ·
        refine ⟨151372028139180660765257303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100914685426120440510171535 151372028139180660765257303)
        ·
          refine ⟨227058042208770991147885955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151372028139180660765257303 227058042208770991147885955)
          ·
            refine ⟨340587063313156486721828933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227058042208770991147885955 340587063313156486721828933)
            ·
              refine ⟨63860074371216841260342925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 340587063313156486721828933 63860074371216841260342925)
              ·
                refine ⟨23947527889206315472628597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63860074371216841260342925 23947527889206315472628597)
                ·
                  refine ⟨2245080739613092075558931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23947527889206315472628597 2245080739613092075558931)
                  ·
                    refine ⟨3367621109419638113338397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2245080739613092075558931 3367621109419638113338397)
                    ·
                      refine ⟨1262857916032364292501899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3367621109419638113338397 1262857916032364292501899)
                      ·
                        rfl

theorem cell23_2459407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 1, 3].length) (baseStart_2459407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459407 prefixEnd_2459407 := by exact prefixLift 2459407
  have htrace : WordTrace (prefixWord ++ tailWord_2459407) baseStart_2459407 baseEnd_2459407 := by
    simpa [prefixWord, tailWord_2459407, baseEnd_2459407] using wordTrace_append hprefix tailTrace_2459407
  have hstable : (prefixWord ++ tailWord_2459407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459407).length < 2 ^ (prefixWord ++ tailWord_2459407).sum := by decide
  have hdescent : baseEnd_2459407 < baseStart_2459407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459427 : List Nat := [1, 1, 1, 4, 2, 1, 4, 3, 1, 5]
def baseStart_2459427 : Nat := 118140960795 + 2459427 * 2 ^ 59
def prefixEnd_2459427 : Nat := 4983230072969 + 3 ^ 40 * 2459427 * 2
def baseEnd_2459427 : Nat := 420956061881818071417269

theorem tailTrace_2459427 : CollatzResearch.WordTrace tailWord_2459427 prefixEnd_2459427 420956061881818071417269 := by
  unfold tailWord_2459427
  simp only [CollatzResearch.WordTrace]
  refine ⟨89702672060923490535880535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59801781373948993690587023 89702672060923490535880535)
  ·
    refine ⟨134554008091385235803820803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89702672060923490535880535 134554008091385235803820803)
    ·
      refine ⟨201831012137077853705731205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134554008091385235803820803 201831012137077853705731205)
      ·
        refine ⟨37843314775702097569824601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201831012137077853705731205 37843314775702097569824601)
        ·
          refine ⟨28382486081776573177368451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37843314775702097569824601 28382486081776573177368451)
          ·
            refine ⟨42573729122664859766052677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28382486081776573177368451 42573729122664859766052677)
            ·
              refine ⟨7982574210499661206134877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42573729122664859766052677 7982574210499661206134877)
              ·
                refine ⟨2993465328937372952300579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7982574210499661206134877 2993465328937372952300579)
                ·
                  refine ⟨4490197993406059428450869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993465328937372952300579 4490197993406059428450869)
                  ·
                    refine ⟨420956061881818071417269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4490197993406059428450869 420956061881818071417269)
                    ·
                      rfl

theorem cell23_2459427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 5].length) (baseStart_2459427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459427 prefixEnd_2459427 := by exact prefixLift 2459427
  have htrace : WordTrace (prefixWord ++ tailWord_2459427) baseStart_2459427 baseEnd_2459427 := by
    simpa [prefixWord, tailWord_2459427, baseEnd_2459427] using wordTrace_append hprefix tailTrace_2459427
  have hstable : (prefixWord ++ tailWord_2459427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459427).length < 2 ^ (prefixWord ++ tailWord_2459427).sum := by decide
  have hdescent : baseEnd_2459427 < baseStart_2459427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459441 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 3, 1, 3]
def baseStart_2459441 : Nat := 118140960795 + 2459441 * 2 ^ 59
def prefixEnd_2459441 : Nat := 4983230072969 + 3 ^ 40 * 2459441 * 2
def baseEnd_2459441 : Nat := 1262875374374617159476743

theorem tailTrace_2459441 : CollatzResearch.WordTrace tailWord_2459441 prefixEnd_2459441 1262875374374617159476743 := by
  unfold tailWord_2459441
  simp only [CollatzResearch.WordTrace]
  refine ⟨89703182682872770926890177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59802121788581847284593451 89703182682872770926890177)
  ·
    refine ⟨67277387012154578195167633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89703182682872770926890177 67277387012154578195167633)
    ·
      refine ⟨50458040259115933646375725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67277387012154578195167633 50458040259115933646375725)
      ·
        refine ⟨18921765097168475117390897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50458040259115933646375725 18921765097168475117390897)
        ·
          refine ⟨14191323822876356338043173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18921765097168475117390897 14191323822876356338043173)
          ·
            refine ⟨2660873216789316813383095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14191323822876356338043173 2660873216789316813383095)
            ·
              refine ⟨3991309825183975220074643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2660873216789316813383095 3991309825183975220074643)
              ·
                refine ⟨5986964737775962830111965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3991309825183975220074643 5986964737775962830111965)
                ·
                  refine ⟨2245111776665986061291987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5986964737775962830111965 2245111776665986061291987)
                  ·
                    refine ⟨3367667664998979091937981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2245111776665986061291987 3367667664998979091937981)
                    ·
                      refine ⟨1262875374374617159476743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3367667664998979091937981 1262875374374617159476743)
                      ·
                        rfl

theorem cell23_2459441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_2459441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459441 prefixEnd_2459441 := by exact prefixLift 2459441
  have htrace : WordTrace (prefixWord ++ tailWord_2459441) baseStart_2459441 baseEnd_2459441 := by
    simpa [prefixWord, tailWord_2459441, baseEnd_2459441] using wordTrace_append hprefix tailTrace_2459441
  have hstable : (prefixWord ++ tailWord_2459441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459441).length < 2 ^ (prefixWord ++ tailWord_2459441).sum := by decide
  have hdescent : baseEnd_2459441 < baseStart_2459441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459447 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 2, 6, 2]
def baseStart_2459447 : Nat := 118140960795 + 2459447 * 2 ^ 59
def prefixEnd_2459447 : Nat := 4983230072969 + 3 ^ 40 * 2459447 * 2
def baseEnd_2459447 : Nat := 1262878455258544136001715

theorem tailTrace_2459447 : CollatzResearch.WordTrace tailWord_2459447 prefixEnd_2459447 1262878455258544136001715 := by
  unfold tailWord_2459447
  simp only [CollatzResearch.WordTrace]
  refine ⟨89703401520851033951608595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59802267680567355967739063 89703401520851033951608595)
  ·
    refine ⟨134555102281276550927412893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89703401520851033951608595 134555102281276550927412893)
    ·
      refine ⟨50458163355478706597779835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134555102281276550927412893 50458163355478706597779835)
      ·
        refine ⟨75687245033218059896669753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50458163355478706597779835 75687245033218059896669753)
        ·
          refine ⟨56765433774913544922502315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75687245033218059896669753 56765433774913544922502315)
          ·
            refine ⟨85148150662370317383753473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56765433774913544922502315 85148150662370317383753473)
            ·
              refine ⟨63861112996777738037815105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85148150662370317383753473 63861112996777738037815105)
              ·
                refine ⟨47895834747583303528361329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63861112996777738037815105 47895834747583303528361329)
                ·
                  refine ⟨35921876060687477646270997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47895834747583303528361329 35921876060687477646270997)
                  ·
                    refine ⟨1683837940344725514668953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35921876060687477646270997 1683837940344725514668953)
                    ·
                      refine ⟨1262878455258544136001715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1683837940344725514668953 1262878455258544136001715)
                      ·
                        rfl

theorem cell23_2459447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 6, 2].length) (baseStart_2459447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459447 prefixEnd_2459447 := by exact prefixLift 2459447
  have htrace : WordTrace (prefixWord ++ tailWord_2459447) baseStart_2459447 baseEnd_2459447 := by
    simpa [prefixWord, tailWord_2459447, baseEnd_2459447] using wordTrace_append hprefix tailTrace_2459447
  have hstable : (prefixWord ++ tailWord_2459447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459447).length < 2 ^ (prefixWord ++ tailWord_2459447).sum := by decide
  have hdescent : baseEnd_2459447 < baseStart_2459447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459464 : List Nat := [2, 1, 3, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_2459464 : Nat := 118140960795 + 2459464 * 2 ^ 59
def prefixEnd_2459464 : Nat := 4983230072969 + 3 ^ 40 * 2459464 * 2
def baseEnd_2459464 : Nat := 1262887184429670569489137

theorem tailTrace_2459464 : CollatzResearch.WordTrace tailWord_2459464 prefixEnd_2459464 1262887184429670569489137 := by
  unfold tailWord_2459464
  simp only [CollatzResearch.WordTrace]
  refine ⟨44852010780894722927488723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59802681041192963903318297 44852010780894722927488723)
  ·
    refine ⟨67278016171342084391233085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44852010780894722927488723 67278016171342084391233085)
    ·
      refine ⟨25229256064253281646712407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67278016171342084391233085 25229256064253281646712407)
      ·
        refine ⟨37843884096379922470068611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25229256064253281646712407 37843884096379922470068611)
        ·
          refine ⟨56765826144569883705102917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37843884096379922470068611 56765826144569883705102917)
          ·
            refine ⟨10643592402106853194706797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56765826144569883705102917 10643592402106853194706797)
            ·
              refine ⟨3991347150790069948015049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10643592402106853194706797 3991347150790069948015049)
              ·
                refine ⟨2993510363092552461011287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3991347150790069948015049 2993510363092552461011287)
                ·
                  refine ⟨4490265544638828691516931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993510363092552461011287 4490265544638828691516931)
                  ·
                    refine ⟨6735398316958243037275397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4490265544638828691516931 6735398316958243037275397)
                    ·
                      refine ⟨1262887184429670569489137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6735398316958243037275397 1262887184429670569489137)
                      ·
                        rfl

theorem cell23_2459464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_2459464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459464 prefixEnd_2459464 := by exact prefixLift 2459464
  have htrace : WordTrace (prefixWord ++ tailWord_2459464) baseStart_2459464 baseEnd_2459464 := by
    simpa [prefixWord, tailWord_2459464, baseEnd_2459464] using wordTrace_append hprefix tailTrace_2459464
  have hstable : (prefixWord ++ tailWord_2459464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459464).length < 2 ^ (prefixWord ++ tailWord_2459464).sum := by decide
  have hdescent : baseEnd_2459464 < baseStart_2459464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459477 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_2459477 : Nat := 118140960795 + 2459477 * 2 ^ 59
def prefixEnd_2459477 : Nat := 4983230072969 + 3 ^ 40 * 2459477 * 2
def baseEnd_2459477 : Nat := 1262893859678179018626577

theorem tailTrace_2459477 : CollatzResearch.WordTrace tailWord_2459477 prefixEnd_2459477 1262893859678179018626577 := by
  unfold tailWord_2459477
  simp only [CollatzResearch.WordTrace]
  refine ⟨89704495710742349075200685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59802997140494899383467123 89704495710742349075200685)
  ·
    refine ⟨33639185891528380903200257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89704495710742349075200685 33639185891528380903200257)
    ·
      refine ⟨25229389418646285677400193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33639185891528380903200257 25229389418646285677400193)
      ·
        refine ⟨18922042063984714258050145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25229389418646285677400193 18922042063984714258050145)
        ·
          refine ⟨14191531547988535693537609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18922042063984714258050145 14191531547988535693537609)
          ·
            refine ⟨10643648660991401770153207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14191531547988535693537609 10643648660991401770153207)
            ·
              refine ⟨15965472991487102655229811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10643648660991401770153207 15965472991487102655229811)
              ·
                refine ⟨23948209487230653982844717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15965472991487102655229811 23948209487230653982844717)
                ·
                  refine ⟨8980578557711495243566769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23948209487230653982844717 8980578557711495243566769)
                  ·
                    refine ⟨6735433918283621432675077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8980578557711495243566769 6735433918283621432675077)
                    ·
                      refine ⟨1262893859678179018626577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6735433918283621432675077 1262893859678179018626577)
                      ·
                        rfl

theorem cell23_2459477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_2459477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459477 prefixEnd_2459477 := by exact prefixLift 2459477
  have htrace : WordTrace (prefixWord ++ tailWord_2459477) baseStart_2459477 baseEnd_2459477 := by
    simpa [prefixWord, tailWord_2459477, baseEnd_2459477] using wordTrace_append hprefix tailTrace_2459477
  have hstable : (prefixWord ++ tailWord_2459477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459477).length < 2 ^ (prefixWord ++ tailWord_2459477).sum := by decide
  have hdescent : baseEnd_2459477 < baseStart_2459477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459491 : List Nat := [1, 1, 1, 5, 4, 1, 2, 2, 2, 4]
def baseStart_2459491 : Nat := 118140960795 + 2459491 * 2 ^ 59
def prefixEnd_2459491 : Nat := 4983230072969 + 3 ^ 40 * 2459491 * 2
def baseEnd_2459491 : Nat := 420967016135780654617171

theorem tailTrace_2459491 : CollatzResearch.WordTrace tailWord_2459491 prefixEnd_2459491 420967016135780654617171 := by
  unfold tailWord_2459491
  simp only [CollatzResearch.WordTrace]
  refine ⟨89705006332691629466210327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59803337555127752977473551 89705006332691629466210327)
  ·
    refine ⟨134557509499037444199315491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89705006332691629466210327 134557509499037444199315491)
    ·
      refine ⟨201836264248556166298973237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134557509499037444199315491 201836264248556166298973237)
      ·
        refine ⟨18922149773302140590528741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 201836264248556166298973237 18922149773302140590528741)
        ·
          refine ⟨3547903082494151360724139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18922149773302140590528741 3547903082494151360724139)
          ·
            refine ⟨5321854623741227041086209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547903082494151360724139 5321854623741227041086209)
            ·
              refine ⟨3991390967805920280814657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5321854623741227041086209 3991390967805920280814657)
              ·
                refine ⟨2993543225854440210610993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3991390967805920280814657 2993543225854440210610993)
                ·
                  refine ⟨2245157419390830157958245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2993543225854440210610993 2245157419390830157958245)
                  ·
                    refine ⟨420967016135780654617171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2245157419390830157958245 420967016135780654617171)
                    ·
                      rfl

theorem cell23_2459491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 4].length) (baseStart_2459491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459491 prefixEnd_2459491 := by exact prefixLift 2459491
  have htrace : WordTrace (prefixWord ++ tailWord_2459491) baseStart_2459491 baseEnd_2459491 := by
    simpa [prefixWord, tailWord_2459491, baseEnd_2459491] using wordTrace_append hprefix tailTrace_2459491
  have hstable : (prefixWord ++ tailWord_2459491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459491).length < 2 ^ (prefixWord ++ tailWord_2459491).sum := by decide
  have hdescent : baseEnd_2459491 < baseStart_2459491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459492 : List Nat := [2, 3, 1, 1, 6, 1, 2, 2, 1, 1, 3]
def baseStart_2459492 : Nat := 118140960795 + 2459492 * 2 ^ 59
def prefixEnd_2459492 : Nat := 4983230072969 + 3 ^ 40 * 2459492 * 2
def baseEnd_2459492 : Nat := 1262901561887996459939009

theorem tailTrace_2459492 : CollatzResearch.WordTrace tailWord_2459492 prefixEnd_2459492 1262901561887996459939009 := by
  unfold tailWord_2459492
  simp only [CollatzResearch.WordTrace]
  refine ⟨44852521402844003318498365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59803361870458671091331153 44852521402844003318498365)
  ·
    refine ⟨16819695526066501244436887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44852521402844003318498365 16819695526066501244436887)
    ·
      refine ⟨25229543289099751866655331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16819695526066501244436887 25229543289099751866655331)
      ·
        refine ⟨37844314933649627799982997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25229543289099751866655331 37844314933649627799982997)
        ·
          refine ⟨1773952262514826303124203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37844314933649627799982997 1773952262514826303124203)
          ·
            refine ⟨2660928393772239454686305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1773952262514826303124203 2660928393772239454686305)
            ·
              refine ⟨1995696295329179591014729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2660928393772239454686305 1995696295329179591014729)
              ·
                refine ⟨1496772221496884693261047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1995696295329179591014729 1496772221496884693261047)
                ·
                  refine ⟨2245158332245327039891571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1496772221496884693261047 2245158332245327039891571)
                  ·
                    refine ⟨3367737498367990559837357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2245158332245327039891571 3367737498367990559837357)
                    ·
                      refine ⟨1262901561887996459939009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3367737498367990559837357 1262901561887996459939009)
                      ·
                        rfl

theorem cell23_2459492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_2459492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459492 prefixEnd_2459492 := by exact prefixLift 2459492
  have htrace : WordTrace (prefixWord ++ tailWord_2459492) baseStart_2459492 baseEnd_2459492 := by
    simpa [prefixWord, tailWord_2459492, baseEnd_2459492] using wordTrace_append hprefix tailTrace_2459492
  have hstable : (prefixWord ++ tailWord_2459492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459492).length < 2 ^ (prefixWord ++ tailWord_2459492).sum := by decide
  have hdescent : baseEnd_2459492 < baseStart_2459492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459521 : List Nat := [1, 2, 4, 4, 1, 1, 3, 7]
def baseStart_2459521 : Nat := 118140960795 + 2459521 * 2 ^ 59
def prefixEnd_2459521 : Nat := 4983230072969 + 3 ^ 40 * 2459521 * 2
def baseEnd_2459521 : Nat := 46774683438036179499125

theorem tailTrace_2459521 : CollatzResearch.WordTrace tailWord_2459521 prefixEnd_2459521 46774683438036179499125 := by
  unfold tailWord_2459521
  simp only [CollatzResearch.WordTrace]
  refine ⟨89706100522582944589802417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59804067015055296393201611 89706100522582944589802417)
  ·
    refine ⟨67279575391937208442351813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89706100522582944589802417 67279575391937208442351813)
    ·
      refine ⟨12614920385988226582940965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67279575391937208442351813 12614920385988226582940965)
      ·
        refine ⟨2365297572372792484301431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12614920385988226582940965 2365297572372792484301431)
        ·
          refine ⟨3547946358559188726452147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365297572372792484301431 3547946358559188726452147)
          ·
            refine ⟨5321919537838783089678221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547946358559188726452147 5321919537838783089678221)
            ·
              refine ⟨1995719826689543658629333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5321919537838783089678221 1995719826689543658629333)
              ·
                refine ⟨46774683438036179499125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1995719826689543658629333 46774683438036179499125)
                ·
                  rfl

theorem cell23_2459521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 7].length) (baseStart_2459521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459521 prefixEnd_2459521 := by exact prefixLift 2459521
  have htrace : WordTrace (prefixWord ++ tailWord_2459521) baseStart_2459521 baseEnd_2459521 := by
    simpa [prefixWord, tailWord_2459521, baseEnd_2459521] using wordTrace_append hprefix tailTrace_2459521
  have hstable : (prefixWord ++ tailWord_2459521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459521).length < 2 ^ (prefixWord ++ tailWord_2459521).sum := by decide
  have hdescent : baseEnd_2459521 < baseStart_2459521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459541 : List Nat := [1, 3, 2, 1, 1, 3, 3, 3, 1, 3, 2]
def baseStart_2459541 : Nat := 118140960795 + 2459541 * 2 ^ 59
def prefixEnd_2459541 : Nat := 4983230072969 + 3 ^ 40 * 2459541 * 2
def baseEnd_2459541 : Nat := 1262926722440066768226283

theorem tailTrace_2459541 : CollatzResearch.WordTrace tailWord_2459541 prefixEnd_2459541 1262926722440066768226283 := by
  unfold tailWord_2459541
  simp only [CollatzResearch.WordTrace]
  refine ⟨89706829982510488005530477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59804553321673658670353651 89706829982510488005530477)
  ·
    refine ⟨33640061243441433002073929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89706829982510488005530477 33640061243441433002073929)
    ·
      refine ⟨25230045932581074751555447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33640061243441433002073929 25230045932581074751555447)
      ·
        refine ⟨37845068898871612127333171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25230045932581074751555447 37845068898871612127333171)
        ·
          refine ⟨56767603348307418190999757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37845068898871612127333171 56767603348307418190999757)
          ·
            refine ⟨21287851255615281821624909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56767603348307418190999757 21287851255615281821624909)
            ·
              refine ⟨7982944220855730683109341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21287851255615281821624909 7982944220855730683109341)
              ·
                refine ⟨2993604082820899006166003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7982944220855730683109341 2993604082820899006166003)
                ·
                  refine ⟨4490406124231348509249005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993604082820899006166003 4490406124231348509249005)
                  ·
                    refine ⟨1683902296586755690968377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4490406124231348509249005 1683902296586755690968377)
                    ·
                      refine ⟨1262926722440066768226283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1683902296586755690968377 1262926722440066768226283)
                      ·
                        rfl

theorem cell23_2459541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_2459541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459541 prefixEnd_2459541 := by exact prefixLift 2459541
  have htrace : WordTrace (prefixWord ++ tailWord_2459541) baseStart_2459541 baseEnd_2459541 := by
    simpa [prefixWord, tailWord_2459541, baseEnd_2459541] using wordTrace_append hprefix tailTrace_2459541
  have hstable : (prefixWord ++ tailWord_2459541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459541).length < 2 ^ (prefixWord ++ tailWord_2459541).sum := by decide
  have hdescent : baseEnd_2459541 < baseStart_2459541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459542 : List Nat := [5, 3, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2459542 : Nat := 118140960795 + 2459542 * 2 ^ 59
def prefixEnd_2459542 : Nat := 4983230072969 + 3 ^ 40 * 2459542 * 2
def baseEnd_2459542 : Nat := 420975745306907088104593

theorem tailTrace_2459542 : CollatzResearch.WordTrace tailWord_2459542 prefixEnd_2459542 420975745306907088104593 := by
  unfold tailWord_2459542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5606679153469179073519805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59804577637004576784211253 5606679153469179073519805)
  ·
    refine ⟨2102504682550942152569927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5606679153469179073519805 2102504682550942152569927)
    ·
      refine ⟨3153757023826413228854891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2102504682550942152569927 3153757023826413228854891)
      ·
        refine ⟨4730635535739619843282337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3153757023826413228854891 4730635535739619843282337)
        ·
          refine ⟨3547976651804714882461753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4730635535739619843282337 3547976651804714882461753)
          ·
            refine ⟨2660982488853536161846315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3547976651804714882461753 2660982488853536161846315)
            ·
              refine ⟨3991473733280304242769473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2660982488853536161846315 3991473733280304242769473)
              ·
                refine ⟨2993605299960228182077105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3991473733280304242769473 2993605299960228182077105)
                ·
                  refine ⟨2245203974970171136557829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2993605299960228182077105 2245203974970171136557829)
                  ·
                    refine ⟨420975745306907088104593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2245203974970171136557829 420975745306907088104593)
                    ·
                      rfl

theorem cell23_2459542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2459542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459542 prefixEnd_2459542 := by exact prefixLift 2459542
  have htrace : WordTrace (prefixWord ++ tailWord_2459542) baseStart_2459542 baseEnd_2459542 := by
    simpa [prefixWord, tailWord_2459542, baseEnd_2459542] using wordTrace_append hprefix tailTrace_2459542
  have hstable : (prefixWord ++ tailWord_2459542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459542).length < 2 ^ (prefixWord ++ tailWord_2459542).sum := by decide
  have hdescent : baseEnd_2459542 < baseStart_2459542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459548 : List Nat := [2, 2, 3, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2459548 : Nat := 118140960795 + 2459548 * 2 ^ 59
def prefixEnd_2459548 : Nat := 4983230072969 + 3 ^ 40 * 2459548 * 2
def baseEnd_2459548 : Nat := 1262930316804648240838751

theorem tailTrace_2459548 : CollatzResearch.WordTrace tailWord_2459548 prefixEnd_2459548 1262930316804648240838751 := by
  unfold tailWord_2459548
  simp only [CollatzResearch.WordTrace]
  refine ⟨44853542646742564100517649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59804723528990085467356865 44853542646742564100517649)
  ·
    refine ⟨33640156985056923075388237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44853542646742564100517649 33640156985056923075388237)
    ·
      refine ⟨12615058869396346153270589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33640156985056923075388237 12615058869396346153270589)
      ·
        refine ⟨4730647076023629807476471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12615058869396346153270589 4730647076023629807476471)
        ·
          refine ⟨7095970614035444711214707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4730647076023629807476471 7095970614035444711214707)
          ·
            refine ⟨10643955921053167066822061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7095970614035444711214707 10643955921053167066822061)
            ·
              refine ⟨3991483470394937650058273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10643955921053167066822061 3991483470394937650058273)
              ·
                refine ⟨2993612602796203237543705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3991483470394937650058273 2993612602796203237543705)
                ·
                  refine ⟨2245209452097152428157779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2993612602796203237543705 2245209452097152428157779)
                  ·
                    refine ⟨3367814178145728642236669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2245209452097152428157779 3367814178145728642236669)
                    ·
                      refine ⟨1262930316804648240838751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3367814178145728642236669 1262930316804648240838751)
                      ·
                        rfl

theorem cell23_2459548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2459548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459548 prefixEnd_2459548 := by exact prefixLift 2459548
  have htrace : WordTrace (prefixWord ++ tailWord_2459548) baseStart_2459548 baseEnd_2459548 := by
    simpa [prefixWord, tailWord_2459548, baseEnd_2459548] using wordTrace_append hprefix tailTrace_2459548
  have hstable : (prefixWord ++ tailWord_2459548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459548).length < 2 ^ (prefixWord ++ tailWord_2459548).sum := by decide
  have hdescent : baseEnd_2459548 < baseStart_2459548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459557 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 1, 6, 3]
def baseStart_2459557 : Nat := 118140960795 + 2459557 * 2 ^ 59
def prefixEnd_2459557 : Nat := 4983230072969 + 3 ^ 40 * 2459557 * 2
def baseEnd_2459557 : Nat := 1262934938130538705626209

theorem tailTrace_2459557 : CollatzResearch.WordTrace tailWord_2459557 prefixEnd_2459557 1262934938130538705626209 := by
  unfold tailWord_2459557
  simp only [CollatzResearch.WordTrace]
  refine ⟨89707413550452522738112925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59804942366968348492075283 89707413550452522738112925)
  ·
    refine ⟨33640280081419696026792347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89707413550452522738112925 33640280081419696026792347)
    ·
      refine ⟨50460420122129544040188521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33640280081419696026792347 50460420122129544040188521)
      ·
        refine ⟨37845315091597158030141391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50460420122129544040188521 37845315091597158030141391)
        ·
          refine ⟨56767972637395737045212087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37845315091597158030141391 56767972637395737045212087)
          ·
            refine ⟨85151958956093605567818131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56767972637395737045212087 85151958956093605567818131)
            ·
              refine ⟨127727938434140408351727197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85151958956093605567818131 127727938434140408351727197)
              ·
                refine ⟨47897976912802653131897699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127727938434140408351727197 47897976912802653131897699)
                ·
                  refine ⟨71846965369203979697846549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47897976912802653131897699 71846965369203979697846549)
                  ·
                    refine ⟨3367826501681436548336557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71846965369203979697846549 3367826501681436548336557)
                    ·
                      refine ⟨1262934938130538705626209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3367826501681436548336557 1262934938130538705626209)
                      ·
                        rfl

theorem cell23_2459557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_2459557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459557 prefixEnd_2459557 := by exact prefixLift 2459557
  have htrace : WordTrace (prefixWord ++ tailWord_2459557) baseStart_2459557 baseEnd_2459557 := by
    simpa [prefixWord, tailWord_2459557, baseEnd_2459557] using wordTrace_append hprefix tailTrace_2459557
  have hstable : (prefixWord ++ tailWord_2459557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459557).length < 2 ^ (prefixWord ++ tailWord_2459557).sum := by decide
  have hdescent : baseEnd_2459557 < baseStart_2459557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459567 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 4]
def baseStart_2459567 : Nat := 118140960795 + 2459567 * 2 ^ 59
def prefixEnd_2459567 : Nat := 4983230072969 + 3 ^ 40 * 2459567 * 2
def baseEnd_2459567 : Nat := 1262940072937083666501163

theorem tailTrace_2459567 : CollatzResearch.WordTrace tailWord_2459567 prefixEnd_2459567 1262940072937083666501163 := by
  unfold tailWord_2459567
  simp only [CollatzResearch.WordTrace]
  refine ⟨89707778280416294445976955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59805185520277529630651303 89707778280416294445976955)
  ·
    refine ⟨134561667420624441668965433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89707778280416294445976955 134561667420624441668965433)
    ·
      refine ⟨100921250565468331251724075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134561667420624441668965433 100921250565468331251724075)
      ·
        refine ⟨151381875848202496877586113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100921250565468331251724075 151381875848202496877586113)
        ·
          refine ⟨113536406886151872658189585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151381875848202496877586113 113536406886151872658189585)
          ·
            refine ⟨85152305164613904493642189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113536406886151872658189585 85152305164613904493642189)
            ·
              refine ⟨31932114436730214185115821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85152305164613904493642189 31932114436730214185115821)
              ·
                refine ⟨11974542913773830319418433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31932114436730214185115821 11974542913773830319418433)
                ·
                  refine ⟨8980907185330372739563825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11974542913773830319418433 8980907185330372739563825)
                  ·
                    refine ⟨6735680388997779554672869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8980907185330372739563825 6735680388997779554672869)
                    ·
                      refine ⟨1262940072937083666501163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6735680388997779554672869 1262940072937083666501163)
                      ·
                        rfl

theorem cell23_2459567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_2459567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459567 prefixEnd_2459567 := by exact prefixLift 2459567
  have htrace : WordTrace (prefixWord ++ tailWord_2459567) baseStart_2459567 baseEnd_2459567 := by
    simpa [prefixWord, tailWord_2459567, baseEnd_2459567] using wordTrace_append hprefix tailTrace_2459567
  have hstable : (prefixWord ++ tailWord_2459567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459567).length < 2 ^ (prefixWord ++ tailWord_2459567).sum := by decide
  have hdescent : baseEnd_2459567 < baseStart_2459567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459577 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 7]
def baseStart_2459577 : Nat := 118140960795 + 2459577 * 2 ^ 59
def prefixEnd_2459577 : Nat := 4983230072969 + 3 ^ 40 * 2459577 * 2
def baseEnd_2459577 : Nat := 140327245304847625264013

theorem tailTrace_2459577 : CollatzResearch.WordTrace tailWord_2459577 prefixEnd_2459577 140327245304847625264013 := by
  unfold tailWord_2459577
  simp only [CollatzResearch.WordTrace]
  refine ⟨89708143010380066153840985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59805428673586710769227323 89708143010380066153840985)
  ·
    refine ⟨67281107257785049615380739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89708143010380066153840985 67281107257785049615380739)
    ·
      refine ⟨100921660886677574423071109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67281107257785049615380739 100921660886677574423071109)
      ·
        refine ⟨18922811416252045204325833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100921660886677574423071109 18922811416252045204325833)
        ·
          refine ⟨14192108562189033903244375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18922811416252045204325833 14192108562189033903244375)
          ·
            refine ⟨21288162843283550854866563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14192108562189033903244375 21288162843283550854866563)
            ·
              refine ⟨31932244264925326282299845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21288162843283550854866563 31932244264925326282299845)
              ·
                refine ⟨5987295799673498677931221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31932244264925326282299845 5987295799673498677931221)
                ·
                  refine ⟨140327245304847625264013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5987295799673498677931221 140327245304847625264013)
                  ·
                    rfl

theorem cell23_2459577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 7].length) (baseStart_2459577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459577 prefixEnd_2459577 := by exact prefixLift 2459577
  have htrace : WordTrace (prefixWord ++ tailWord_2459577) baseStart_2459577 baseEnd_2459577 := by
    simpa [prefixWord, tailWord_2459577, baseEnd_2459577] using wordTrace_append hprefix tailTrace_2459577
  have hstable : (prefixWord ++ tailWord_2459577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459577).length < 2 ^ (prefixWord ++ tailWord_2459577).sum := by decide
  have hdescent : baseEnd_2459577 < baseStart_2459577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459617 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_2459617 : Nat := 118140960795 + 2459617 * 2 ^ 59
def prefixEnd_2459617 : Nat := 4983230072969 + 3 ^ 40 * 2459617 * 2
def baseEnd_2459617 : Nat := 1262965746969808470875933

theorem tailTrace_2459617 : CollatzResearch.WordTrace tailWord_2459617 prefixEnd_2459617 1262965746969808470875933 := by
  unfold tailWord_2459617
  simp only [CollatzResearch.WordTrace]
  refine ⟨89709601930235152985297105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59806401286823435323531403 89709601930235152985297105)
  ·
    refine ⟨67282201447676364738972829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89709601930235152985297105 67282201447676364738972829)
    ·
      refine ⟨25230825542878636777114811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67282201447676364738972829 25230825542878636777114811)
      ·
        refine ⟨37846238314317955165672217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25230825542878636777114811 37846238314317955165672217)
        ·
          refine ⟨28384678735738466374254163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37846238314317955165672217 28384678735738466374254163)
          ·
            refine ⟨42577018103607699561381245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28384678735738466374254163 42577018103607699561381245)
            ·
              refine ⟨15966381788852887335517967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42577018103607699561381245 15966381788852887335517967)
              ·
                refine ⟨23949572683279331003276951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15966381788852887335517967 23949572683279331003276951)
                ·
                  refine ⟨35924359024918996504915427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23949572683279331003276951 35924359024918996504915427)
                  ·
                    refine ⟨53886538537378494757373141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35924359024918996504915427 53886538537378494757373141)
                    ·
                      refine ⟨1262965746969808470875933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53886538537378494757373141 1262965746969808470875933)
                      ·
                        rfl

theorem cell23_2459617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_2459617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459617 prefixEnd_2459617 := by exact prefixLift 2459617
  have htrace : WordTrace (prefixWord ++ tailWord_2459617) baseStart_2459617 baseEnd_2459617 := by
    simpa [prefixWord, tailWord_2459617, baseEnd_2459617] using wordTrace_append hprefix tailTrace_2459617
  have hstable : (prefixWord ++ tailWord_2459617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459617).length < 2 ^ (prefixWord ++ tailWord_2459617).sum := by decide
  have hdescent : baseEnd_2459617 < baseStart_2459617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459627 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 4]
def baseStart_2459627 : Nat := 118140960795 + 2459627 * 2 ^ 59
def prefixEnd_2459627 : Nat := 4983230072969 + 3 ^ 40 * 2459627 * 2
def baseEnd_2459627 : Nat := 1262970881776353431750887

theorem tailTrace_2459627 : CollatzResearch.WordTrace tailWord_2459627 prefixEnd_2459627 1262970881776353431750887 := by
  unfold tailWord_2459627
  simp only [CollatzResearch.WordTrace]
  refine ⟨89709966660198924693161135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59806644440132616462107423 89709966660198924693161135)
  ·
    refine ⟨134564949990298387039741703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89709966660198924693161135 134564949990298387039741703)
    ·
      refine ⟨201847424985447580559612555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134564949990298387039741703 201847424985447580559612555)
      ·
        refine ⟨302771137478171370839418833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201847424985447580559612555 302771137478171370839418833)
        ·
          refine ⟨227078353108628528129564125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302771137478171370839418833 227078353108628528129564125)
          ·
            refine ⟨85154382415735698048586547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227078353108628528129564125 85154382415735698048586547)
            ·
              refine ⟨127731573623603547072879821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85154382415735698048586547 127731573623603547072879821)
              ·
                refine ⟨47899340108851330152329933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127731573623603547072879821 47899340108851330152329933)
                ·
                  refine ⟨17962252540819248807123725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47899340108851330152329933 17962252540819248807123725)
                  ·
                    refine ⟨6735844702807218302671397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17962252540819248807123725 6735844702807218302671397)
                    ·
                      refine ⟨1262970881776353431750887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6735844702807218302671397 1262970881776353431750887)
                      ·
                        rfl

theorem cell23_2459627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 4].length) (baseStart_2459627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459627 prefixEnd_2459627 := by exact prefixLift 2459627
  have htrace : WordTrace (prefixWord ++ tailWord_2459627) baseStart_2459627 baseEnd_2459627 := by
    simpa [prefixWord, tailWord_2459627, baseEnd_2459627] using wordTrace_append hprefix tailTrace_2459627
  have hstable : (prefixWord ++ tailWord_2459627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459627).length < 2 ^ (prefixWord ++ tailWord_2459627).sum := by decide
  have hdescent : baseEnd_2459627 < baseStart_2459627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459667 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 8]
def baseStart_2459667 : Nat := 118140960795 + 2459667 * 2 ^ 59
def prefixEnd_2459667 : Nat := 4983230072969 + 3 ^ 40 * 2459667 * 2
def baseEnd_2459667 : Nat := 140332380111392586138967

theorem tailTrace_2459667 : CollatzResearch.WordTrace tailWord_2459667 prefixEnd_2459667 140332380111392586138967 := by
  unfold tailWord_2459667
  simp only [CollatzResearch.WordTrace]
  refine ⟨89711425580054011524617255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59807617053369341016411503 89711425580054011524617255)
  ·
    refine ⟨134567138370081017286925883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89711425580054011524617255 134567138370081017286925883)
    ·
      refine ⟨201850707555121525930388825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134567138370081017286925883 201850707555121525930388825)
      ·
        refine ⟨151388030666341144447791619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201850707555121525930388825 151388030666341144447791619)
        ·
          refine ⟨227082045999511716671687429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151388030666341144447791619 227082045999511716671687429)
          ·
            refine ⟨42577883624908446875941393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 227082045999511716671687429 42577883624908446875941393)
            ·
              refine ⟨31933412718681335156956045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42577883624908446875941393 31933412718681335156956045)
              ·
                refine ⟨11975029769505500683858517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31933412718681335156956045 11975029769505500683858517)
                ·
                  refine ⟨140332380111392586138967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11975029769505500683858517 140332380111392586138967)
                  ·
                    rfl

theorem cell23_2459667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 8].length) (baseStart_2459667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459667 prefixEnd_2459667 := by exact prefixLift 2459667
  have htrace : WordTrace (prefixWord ++ tailWord_2459667) baseStart_2459667 baseEnd_2459667 := by
    simpa [prefixWord, tailWord_2459667, baseEnd_2459667] using wordTrace_append hprefix tailTrace_2459667
  have hstable : (prefixWord ++ tailWord_2459667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459667).length < 2 ^ (prefixWord ++ tailWord_2459667).sum := by decide
  have hdescent : baseEnd_2459667 < baseStart_2459667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459698 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_2459698 : Nat := 118140960795 + 2459698 * 2 ^ 59
def prefixEnd_2459698 : Nat := 4983230072969 + 3 ^ 40 * 2459698 * 2
def baseEnd_2459698 : Nat := 1263007338902822653963061

theorem tailTrace_2459698 : CollatzResearch.WordTrace tailWord_2459698 prefixEnd_2459698 1263007338902822653963061 := by
  unfold tailWord_2459698
  simp only [CollatzResearch.WordTrace]
  refine ⟨22428139060735425954748937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59808370828627802545997165 22428139060735425954748937)
  ·
    refine ⟨16821104295551569466061703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22428139060735425954748937 16821104295551569466061703)
    ·
      refine ⟨25231656443327354199092555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16821104295551569466061703 25231656443327354199092555)
      ·
        refine ⟨37847484664991031298638833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25231656443327354199092555 37847484664991031298638833)
        ·
          refine ⟨28385613498743273473979125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37847484664991031298638833 28385613498743273473979125)
          ·
            refine ⟨2661151265507181888185543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28385613498743273473979125 2661151265507181888185543)
            ·
              refine ⟨3991726898260772832278315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2661151265507181888185543 3991726898260772832278315)
              ·
                refine ⟨5987590347391159248417473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3991726898260772832278315 5987590347391159248417473)
                ·
                  refine ⟨4490692760543369436313105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5987590347391159248417473 4490692760543369436313105)
                  ·
                    refine ⟨3368019570407527077234829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4490692760543369436313105 3368019570407527077234829)
                    ·
                      refine ⟨1263007338902822653963061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3368019570407527077234829 1263007338902822653963061)
                      ·
                        rfl

theorem cell23_2459698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_2459698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459698 prefixEnd_2459698 := by exact prefixLift 2459698
  have htrace : WordTrace (prefixWord ++ tailWord_2459698) baseStart_2459698 baseEnd_2459698 := by
    simpa [prefixWord, tailWord_2459698, baseEnd_2459698] using wordTrace_append hprefix tailTrace_2459698
  have hstable : (prefixWord ++ tailWord_2459698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459698).length < 2 ^ (prefixWord ++ tailWord_2459698).sum := by decide
  have hdescent : baseEnd_2459698 < baseStart_2459698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459705 : List Nat := [1, 2, 1, 5, 3, 1, 2, 3, 1, 4]
def baseStart_2459705 : Nat := 118140960795 + 2459705 * 2 ^ 59
def prefixEnd_2459705 : Nat := 4983230072969 + 3 ^ 40 * 2459705 * 2
def baseEnd_2459705 : Nat := 421003644422468042191843

theorem tailTrace_2459705 : CollatzResearch.WordTrace tailWord_2459705 prefixEnd_2459705 421003644422468042191843 := by
  unfold tailWord_2459705
  simp only [CollatzResearch.WordTrace]
  refine ⟨89712811553916344014500569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59808541035944229343000379 89712811553916344014500569)
  ·
    refine ⟨67284608665437258010875427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89712811553916344014500569 67284608665437258010875427)
    ·
      refine ⟨100926912998155887016313141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67284608665437258010875427 100926912998155887016313141)
      ·
        refine ⟨9461898093577114407779357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100926912998155887016313141 9461898093577114407779357)
        ·
          refine ⟨3548211785091417902917259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9461898093577114407779357 3548211785091417902917259)
          ·
            refine ⟨5322317677637126854375889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548211785091417902917259 5322317677637126854375889)
            ·
              refine ⟨3991738258227845140781917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5322317677637126854375889 3991738258227845140781917)
              ·
                refine ⟨1496901846835441927793219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3991738258227845140781917 1496901846835441927793219)
                ·
                  refine ⟨2245352770253162891689829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1496901846835441927793219 2245352770253162891689829)
                  ·
                    refine ⟨421003644422468042191843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2245352770253162891689829 421003644422468042191843)
                    ·
                      rfl

theorem cell23_2459705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 1, 4].length) (baseStart_2459705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459705 prefixEnd_2459705 := by exact prefixLift 2459705
  have htrace : WordTrace (prefixWord ++ tailWord_2459705) baseStart_2459705 baseEnd_2459705 := by
    simpa [prefixWord, tailWord_2459705, baseEnd_2459705] using wordTrace_append hprefix tailTrace_2459705
  have hstable : (prefixWord ++ tailWord_2459705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459705).length < 2 ^ (prefixWord ++ tailWord_2459705).sum := by decide
  have hdescent : baseEnd_2459705 < baseStart_2459705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459707 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 7]
def baseStart_2459707 : Nat := 118140960795 + 2459707 * 2 ^ 59
def prefixEnd_2459707 : Nat := 4983230072969 + 3 ^ 40 * 2459707 * 2
def baseEnd_2459707 : Nat := 1263011960228713118750519

theorem tailTrace_2459707 : CollatzResearch.WordTrace tailWord_2459707 prefixEnd_2459707 1263011960228713118750519 := by
  unfold tailWord_2459707
  simp only [CollatzResearch.WordTrace]
  refine ⟨89712884499909098356073375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59808589666606065570715583 89712884499909098356073375)
  ·
    refine ⟨134569326749863647534110063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89712884499909098356073375 134569326749863647534110063)
    ·
      refine ⟨201853990124795471301165095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134569326749863647534110063 201853990124795471301165095)
      ·
        refine ⟨302780985187193206951747643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201853990124795471301165095 302780985187193206951747643)
        ·
          refine ⟨454171477780789810427621465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302780985187193206951747643 454171477780789810427621465)
          ·
            refine ⟨340628608335592357820716099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454171477780789810427621465 340628608335592357820716099)
            ·
              refine ⟨510942912503388536731074149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340628608335592357820716099 510942912503388536731074149)
              ·
                refine ⟨95801796094385350637076403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 510942912503388536731074149 95801796094385350637076403)
                ·
                  refine ⟨143702694141578025955614605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95801796094385350637076403 143702694141578025955614605)
                  ·
                    refine ⟨53888510303091759733355477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143702694141578025955614605 53888510303091759733355477)
                    ·
                      refine ⟨1263011960228713118750519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53888510303091759733355477 1263011960228713118750519)
                      ·
                        rfl

theorem cell23_2459707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_2459707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459707 prefixEnd_2459707 := by exact prefixLift 2459707
  have htrace : WordTrace (prefixWord ++ tailWord_2459707) baseStart_2459707 baseEnd_2459707 := by
    simpa [prefixWord, tailWord_2459707, baseEnd_2459707] using wordTrace_append hprefix tailTrace_2459707
  have hstable : (prefixWord ++ tailWord_2459707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459707).length < 2 ^ (prefixWord ++ tailWord_2459707).sum := by decide
  have hdescent : baseEnd_2459707 < baseStart_2459707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459721 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 4, 3, 2]
def baseStart_2459721 : Nat := 118140960795 + 2459721 * 2 ^ 59
def prefixEnd_2459721 : Nat := 4983230072969 + 3 ^ 40 * 2459721 * 2
def baseEnd_2459721 : Nat := 1263019148957876063975455

theorem tailTrace_2459721 : CollatzResearch.WordTrace tailWord_2459721 prefixEnd_2459721 1263019148957876063975455 := by
  unfold tailWord_2459721
  simp only [CollatzResearch.WordTrace]
  refine ⟨89713395121858378747083017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59808930081238919164722011 89713395121858378747083017)
  ·
    refine ⟨67285046341393784060312263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89713395121858378747083017 67285046341393784060312263)
    ·
      refine ⟨100927569512090676090468395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67285046341393784060312263 100927569512090676090468395)
      ·
        refine ⟨151391354268136014135702593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100927569512090676090468395 151391354268136014135702593)
        ·
          refine ⟨113543515701102010601776945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151391354268136014135702593 113543515701102010601776945)
          ·
            refine ⟨85157636775826507951332709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113543515701102010601776945 85157636775826507951332709)
            ·
              refine ⟨15967056895467470240874883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85157636775826507951332709 15967056895467470240874883)
              ·
                refine ⟨23950585343201205361312325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15967056895467470240874883 23950585343201205361312325)
                ·
                  refine ⟨4490734751850226005246061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23950585343201205361312325 4490734751850226005246061)
                  ·
                    refine ⟨1684025531943834751967273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4490734751850226005246061 1684025531943834751967273)
                    ·
                      refine ⟨1263019148957876063975455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684025531943834751967273 1263019148957876063975455)
                      ·
                        rfl

theorem cell23_2459721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 3, 2].length) (baseStart_2459721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459721 prefixEnd_2459721 := by exact prefixLift 2459721
  have htrace : WordTrace (prefixWord ++ tailWord_2459721) baseStart_2459721 baseEnd_2459721 := by
    simpa [prefixWord, tailWord_2459721, baseEnd_2459721] using wordTrace_append hprefix tailTrace_2459721
  have hstable : (prefixWord ++ tailWord_2459721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459721).length < 2 ^ (prefixWord ++ tailWord_2459721).sum := by decide
  have hdescent : baseEnd_2459721 < baseStart_2459721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459751 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_2459751 : Nat := 118140960795 + 2459751 * 2 ^ 59
def prefixEnd_2459751 : Nat := 4983230072969 + 3 ^ 40 * 2459751 * 2
def baseEnd_2459751 : Nat := 1263034553377510946600317

theorem tailTrace_2459751 : CollatzResearch.WordTrace tailWord_2459751 prefixEnd_2459751 1263034553377510946600317 := by
  unfold tailWord_2459751
  simp only [CollatzResearch.WordTrace]
  refine ⟨89714489311749693870675107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59809659541166462580450071 89714489311749693870675107)
  ·
    refine ⟨134571733967624540806012661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89714489311749693870675107 134571733967624540806012661)
    ·
      refine ⟨12616100059464800700563687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134571733967624540806012661 12616100059464800700563687)
      ·
        refine ⟨18924150089197201050845531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12616100059464800700563687 18924150089197201050845531)
        ·
          refine ⟨28386225133795801576268297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18924150089197201050845531 28386225133795801576268297)
          ·
            refine ⟨21289668850346851182201223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28386225133795801576268297 21289668850346851182201223)
            ·
              refine ⟨31934503275520276773301835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21289668850346851182201223 31934503275520276773301835)
              ·
                refine ⟨47901754913280415159952753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31934503275520276773301835 47901754913280415159952753)
                ·
                  refine ⟨35926316184960311369964565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47901754913280415159952753 35926316184960311369964565)
                  ·
                    refine ⟨1684046071170014595467089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35926316184960311369964565 1684046071170014595467089)
                    ·
                      refine ⟨1263034553377510946600317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684046071170014595467089 1263034553377510946600317)
                      ·
                        rfl

theorem cell23_2459751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_2459751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459751 prefixEnd_2459751 := by exact prefixLift 2459751
  have htrace : WordTrace (prefixWord ++ tailWord_2459751) baseStart_2459751 baseEnd_2459751 := by
    simpa [prefixWord, tailWord_2459751, baseEnd_2459751] using wordTrace_append hprefix tailTrace_2459751
  have hstable : (prefixWord ++ tailWord_2459751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459751).length < 2 ^ (prefixWord ++ tailWord_2459751).sum := by decide
  have hdescent : baseEnd_2459751 < baseStart_2459751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459762 : List Nat := [3, 2, 1, 2, 2, 4, 1, 3, 1, 1, 3]
def baseStart_2459762 : Nat := 118140960795 + 2459762 * 2 ^ 59
def prefixEnd_2459762 : Nat := 4983230072969 + 3 ^ 40 * 2459762 * 2
def baseEnd_2459762 : Nat := 1263040201664710403562767

theorem tailTrace_2459762 : CollatzResearch.WordTrace tailWord_2459762 prefixEnd_2459762 1263040201664710403562767 := by
  unfold tailWord_2459762
  simp only [CollatzResearch.WordTrace]
  refine ⟨22428722628677460687331385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59809927009806561832883693 22428722628677460687331385)
  ·
    refine ⟨16821541971508095515498539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22428722628677460687331385 16821541971508095515498539)
    ·
      refine ⟨25232312957262143273247809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16821541971508095515498539 25232312957262143273247809)
      ·
        refine ⟨18924234717946607454935857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25232312957262143273247809 18924234717946607454935857)
        ·
          refine ⟨14193176038459955591201893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18924234717946607454935857 14193176038459955591201893)
          ·
            refine ⟨2661220507211241673350355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14193176038459955591201893 2661220507211241673350355)
            ·
              refine ⟨3991830760816862510025533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2661220507211241673350355 3991830760816862510025533)
              ·
                refine ⟨1496936535306323441259575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3991830760816862510025533 1496936535306323441259575)
                ·
                  refine ⟨2245404802959485161889363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1496936535306323441259575 2245404802959485161889363)
                  ·
                    refine ⟨3368107204439227742834045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2245404802959485161889363 3368107204439227742834045)
                    ·
                      refine ⟨1263040201664710403562767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3368107204439227742834045 1263040201664710403562767)
                      ·
                        rfl

theorem cell23_2459762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_2459762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459762 prefixEnd_2459762 := by exact prefixLift 2459762
  have htrace : WordTrace (prefixWord ++ tailWord_2459762) baseStart_2459762 baseEnd_2459762 := by
    simpa [prefixWord, tailWord_2459762, baseEnd_2459762] using wordTrace_append hprefix tailTrace_2459762
  have hstable : (prefixWord ++ tailWord_2459762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459762).length < 2 ^ (prefixWord ++ tailWord_2459762).sum := by decide
  have hdescent : baseEnd_2459762 < baseStart_2459762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459802 : List Nat := [3, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4]
def baseStart_2459802 : Nat := 118140960795 + 2459802 * 2 ^ 59
def prefixEnd_2459802 : Nat := 4983230072969 + 3 ^ 40 * 2459802 * 2
def baseEnd_2459802 : Nat := 1263060740890890247062583

theorem tailTrace_2459802 : CollatzResearch.WordTrace tailWord_2459802 prefixEnd_2459802 1263060740890890247062583 := by
  unfold tailWord_2459802
  simp only [CollatzResearch.WordTrace]
  refine ⟨22429087358641232395195415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59810899623043286387187773 22429087358641232395195415)
  ·
    refine ⟨33643631037961848592793123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22429087358641232395195415 33643631037961848592793123)
    ·
      refine ⟨50465446556942772889189685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33643631037961848592793123 50465446556942772889189685)
      ·
        refine ⟨4731135614713384958361533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50465446556942772889189685 4731135614713384958361533)
        ·
          refine ⟨1774175855517519359385575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4731135614713384958361533 1774175855517519359385575)
          ·
            refine ⟨2661263783276279039078363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774175855517519359385575 2661263783276279039078363)
            ·
              refine ⟨3991895674914418558617545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2661263783276279039078363 3991895674914418558617545)
              ·
                refine ⟨2993921756185813918963159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3991895674914418558617545 2993921756185813918963159)
                ·
                  refine ⟨4490882634278720878444739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993921756185813918963159 4490882634278720878444739)
                  ·
                    refine ⟨6736323951418081317667109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4490882634278720878444739 6736323951418081317667109)
                    ·
                      refine ⟨1263060740890890247062583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6736323951418081317667109 1263060740890890247062583)
                      ·
                        rfl

theorem cell23_2459802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_2459802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459802 prefixEnd_2459802 := by exact prefixLift 2459802
  have htrace : WordTrace (prefixWord ++ tailWord_2459802) baseStart_2459802 baseEnd_2459802 := by
    simpa [prefixWord, tailWord_2459802, baseEnd_2459802] using wordTrace_append hprefix tailTrace_2459802
  have hstable : (prefixWord ++ tailWord_2459802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459802).length < 2 ^ (prefixWord ++ tailWord_2459802).sum := by decide
  have hdescent : baseEnd_2459802 < baseStart_2459802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459805 : List Nat := [1, 4, 2, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_2459805 : Nat := 118140960795 + 2459805 * 2 ^ 59
def prefixEnd_2459805 : Nat := 4983230072969 + 3 ^ 40 * 2459805 * 2
def baseEnd_2459805 : Nat := 1263062281332853735325069

theorem tailTrace_2459805 : CollatzResearch.WordTrace tailWord_2459805 prefixEnd_2459805 1263062281332853735325069 := by
  unfold tailWord_2459805
  simp only [CollatzResearch.WordTrace]
  refine ⟨89716458853554061093140869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59810972569036040728760579 89716458853554061093140869)
  ·
    refine ⟨16821836035041386454963913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89716458853554061093140869 16821836035041386454963913)
    ·
      refine ⟨12616377026281039841222935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16821836035041386454963913 12616377026281039841222935)
      ·
        refine ⟨18924565539421559761834403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12616377026281039841222935 18924565539421559761834403)
        ·
          refine ⟨28386848309132339642751605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18924565539421559761834403 28386848309132339642751605)
          ·
            refine ⟨2661267028981156841507963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28386848309132339642751605 2661267028981156841507963)
            ·
              refine ⟨3991900543471735262261945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2661267028981156841507963 3991900543471735262261945)
              ·
                refine ⟨2993925407603801446696459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3991900543471735262261945 2993925407603801446696459)
                ·
                  refine ⟨4490888111405702170044689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993925407603801446696459 4490888111405702170044689)
                  ·
                    refine ⟨3368166083554276627533517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4490888111405702170044689 3368166083554276627533517)
                    ·
                      refine ⟨1263062281332853735325069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3368166083554276627533517 1263062281332853735325069)
                      ·
                        rfl

theorem cell23_2459805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_2459805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459805 prefixEnd_2459805 := by exact prefixLift 2459805
  have htrace : WordTrace (prefixWord ++ tailWord_2459805) baseStart_2459805 baseEnd_2459805 := by
    simpa [prefixWord, tailWord_2459805, baseEnd_2459805] using wordTrace_append hprefix tailTrace_2459805
  have hstable : (prefixWord ++ tailWord_2459805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459805).length < 2 ^ (prefixWord ++ tailWord_2459805).sum := by decide
  have hdescent : baseEnd_2459805 < baseStart_2459805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459822 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2459822 : Nat := 118140960795 + 2459822 * 2 ^ 59
def prefixEnd_2459822 : Nat := 4983230072969 + 3 ^ 40 * 2459822 * 2
def baseEnd_2459822 : Nat := 1263071010503980168812491

theorem tailTrace_2459822 : CollatzResearch.WordTrace tailWord_2459822 prefixEnd_2459822 1263071010503980168812491 := by
  unfold tailWord_2459822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11214634861811559124563715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59811385929661648664339813 11214634861811559124563715)
  ·
    refine ⟨16821952292717338686845573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11214634861811559124563715 16821952292717338686845573)
    ·
      refine ⟨3154116054884501003783545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16821952292717338686845573 3154116054884501003783545)
      ·
        refine ⟨2365587041163375752837659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3154116054884501003783545 2365587041163375752837659)
        ·
          refine ⟨3548380561745063629256489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365587041163375752837659 3548380561745063629256489)
          ·
            refine ⟨2661285421308797721942367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3548380561745063629256489 2661285421308797721942367)
            ·
              refine ⟨3991928131963196582913551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2661285421308797721942367 3991928131963196582913551)
              ·
                refine ⟨5987892197944794874370327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3991928131963196582913551 5987892197944794874370327)
                ·
                  refine ⟨8981838296917192311555491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5987892197944794874370327 8981838296917192311555491)
                  ·
                    refine ⟨13472757445375788467333237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8981838296917192311555491 13472757445375788467333237)
                    ·
                      refine ⟨1263071010503980168812491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13472757445375788467333237 1263071010503980168812491)
                      ·
                        rfl

theorem cell23_2459822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2459822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459822 prefixEnd_2459822 := by exact prefixLift 2459822
  have htrace : WordTrace (prefixWord ++ tailWord_2459822) baseStart_2459822 baseEnd_2459822 := by
    simpa [prefixWord, tailWord_2459822, baseEnd_2459822] using wordTrace_append hprefix tailTrace_2459822
  have hstable : (prefixWord ++ tailWord_2459822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459822).length < 2 ^ (prefixWord ++ tailWord_2459822).sum := by decide
  have hdescent : baseEnd_2459822 < baseStart_2459822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459824 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 4]
def baseStart_2459824 : Nat := 118140960795 + 2459824 * 2 ^ 59
def prefixEnd_2459824 : Nat := 4983230072969 + 3 ^ 40 * 2459824 * 2
def baseEnd_2459824 : Nat := 1263072037465289160987481

theorem tailTrace_2459824 : CollatzResearch.WordTrace tailWord_2459824 prefixEnd_2459824 1263072037465289160987481 := by
  unfold tailWord_2459824
  simp only [CollatzResearch.WordTrace]
  refine ⟨44858575920242613669041263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59811434560323484892055017 44858575920242613669041263)
  ·
    refine ⟨67287863880363920503561895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44858575920242613669041263 67287863880363920503561895)
    ·
      refine ⟨100931795820545880755342843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67287863880363920503561895 100931795820545880755342843)
      ·
        refine ⟨151397693730818821133014265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100931795820545880755342843 151397693730818821133014265)
        ·
          refine ⟨113548270298114115849760699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151397693730818821133014265 113548270298114115849760699)
          ·
            refine ⟨170322405447171173774641049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113548270298114115849760699 170322405447171173774641049)
            ·
              refine ⟨127741804085378380330980787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170322405447171173774641049 127741804085378380330980787)
              ·
                refine ⟨191612706128067570496471181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127741804085378380330980787 191612706128067570496471181)
                ·
                  refine ⟨71854764798025338936176693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191612706128067570496471181 71854764798025338936176693)
                  ·
                    refine ⟨6736384199814875525266565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71854764798025338936176693 6736384199814875525266565)
                    ·
                      refine ⟨1263072037465289160987481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6736384199814875525266565 1263072037465289160987481)
                      ·
                        rfl

theorem cell23_2459824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_2459824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459824 prefixEnd_2459824 := by exact prefixLift 2459824
  have htrace : WordTrace (prefixWord ++ tailWord_2459824) baseStart_2459824 baseEnd_2459824 := by
    simpa [prefixWord, tailWord_2459824, baseEnd_2459824] using wordTrace_append hprefix tailTrace_2459824
  have hstable : (prefixWord ++ tailWord_2459824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459824).length < 2 ^ (prefixWord ++ tailWord_2459824).sum := by decide
  have hdescent : baseEnd_2459824 < baseStart_2459824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459836 : List Nat := [2, 2, 2, 3, 3, 2, 2, 2, 1, 2, 2]
def baseStart_2459836 : Nat := 118140960795 + 2459836 * 2 ^ 59
def prefixEnd_2459836 : Nat := 4983230072969 + 3 ^ 40 * 2459836 * 2
def baseEnd_2459836 : Nat := 1263078199233143114037427

theorem tailTrace_2459836 : CollatzResearch.WordTrace tailWord_2459836 prefixEnd_2459836 1263078199233143114037427 := by
  unfold tailWord_2459836
  simp only [CollatzResearch.WordTrace]
  refine ⟨44858794758220876693759681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59811726344294502258346241 44858794758220876693759681)
  ·
    refine ⟨33644096068665657520319761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44858794758220876693759681 33644096068665657520319761)
    ·
      refine ⟨25233072051499243140239821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33644096068665657520319761 25233072051499243140239821)
      ·
        refine ⟨9462402019312216177589933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25233072051499243140239821 9462402019312216177589933)
        ·
          refine ⟨3548400757242081066596225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9462402019312216177589933 3548400757242081066596225)
          ·
            refine ⟨2661300567931560799947169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3548400757242081066596225 2661300567931560799947169)
            ·
              refine ⟨1995975425948670599960377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661300567931560799947169 1995975425948670599960377)
              ·
                refine ⟨1496981569461502949970283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1995975425948670599960377 1496981569461502949970283)
                ·
                  refine ⟨2245472354192254424955425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1496981569461502949970283 2245472354192254424955425)
                  ·
                    refine ⟨1684104265644190818716569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2245472354192254424955425 1684104265644190818716569)
                    ·
                      refine ⟨1263078199233143114037427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684104265644190818716569 1263078199233143114037427)
                      ·
                        rfl

theorem cell23_2459836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_2459836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459836 prefixEnd_2459836 := by exact prefixLift 2459836
  have htrace : WordTrace (prefixWord ++ tailWord_2459836) baseStart_2459836 baseEnd_2459836 := by
    simpa [prefixWord, tailWord_2459836, baseEnd_2459836] using wordTrace_append hprefix tailTrace_2459836
  have hstable : (prefixWord ++ tailWord_2459836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459836).length < 2 ^ (prefixWord ++ tailWord_2459836).sum := by decide
  have hdescent : baseEnd_2459836 < baseStart_2459836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459862 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_2459862 : Nat := 118140960795 + 2459862 * 2 ^ 59
def prefixEnd_2459862 : Nat := 4983230072969 + 3 ^ 40 * 2459862 * 2
def baseEnd_2459862 : Nat := 1263091549730160012312307

theorem tailTrace_2459862 : CollatzResearch.WordTrace tailWord_2459862 prefixEnd_2459862 1263091549730160012312307 := by
  unfold tailWord_2459862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5607408613396722489247865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59812358542898373218643893 5607408613396722489247865)
  ·
    refine ⟨4205556460047541866935899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5607408613396722489247865 4205556460047541866935899)
    ·
      refine ⟨6308334690071312800403849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4205556460047541866935899 6308334690071312800403849)
      ·
        refine ⟨4731251017553484600302887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6308334690071312800403849 4731251017553484600302887)
        ·
          refine ⟨7096876526330226900454331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4731251017553484600302887 7096876526330226900454331)
          ·
            refine ⟨10645314789495340350681497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7096876526330226900454331 10645314789495340350681497)
            ·
              refine ⟨7983986092121505263011123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10645314789495340350681497 7983986092121505263011123)
              ·
                refine ⟨11975979138182257894516685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7983986092121505263011123 11975979138182257894516685)
                ·
                  refine ⟨4490992176818346710443757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11975979138182257894516685 4490992176818346710443757)
                  ·
                    refine ⟨1684122066306880016416409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4490992176818346710443757 1684122066306880016416409)
                    ·
                      refine ⟨1263091549730160012312307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684122066306880016416409 1263091549730160012312307)
                      ·
                        rfl

theorem cell23_2459862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_2459862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459862 prefixEnd_2459862 := by exact prefixLift 2459862
  have htrace : WordTrace (prefixWord ++ tailWord_2459862) baseStart_2459862 baseEnd_2459862 := by
    simpa [prefixWord, tailWord_2459862, baseEnd_2459862] using wordTrace_append hprefix tailTrace_2459862
  have hstable : (prefixWord ++ tailWord_2459862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459862).length < 2 ^ (prefixWord ++ tailWord_2459862).sum := by decide
  have hdescent : baseEnd_2459862 < baseStart_2459862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459879 : List Nat := [1, 1, 5, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_2459879 : Nat := 118140960795 + 2459879 * 2 ^ 59
def prefixEnd_2459879 : Nat := 4983230072969 + 3 ^ 40 * 2459879 * 2
def baseEnd_2459879 : Nat := 1263100278901286445799729

theorem tailTrace_2459879 : CollatzResearch.WordTrace tailWord_2459879 prefixEnd_2459879 1263100278901286445799729 := by
  unfold tailWord_2459879
  simp only [CollatzResearch.WordTrace]
  refine ⟨89719157855285971731334691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59812771903523981154223127 89719157855285971731334691)
  ·
    refine ⟨134578736782928957597002037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89719157855285971731334691 134578736782928957597002037)
    ·
      refine ⟨12616756573399589774718941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134578736782928957597002037 12616756573399589774718941)
      ·
        refine ⟨4731283715024846165519603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12616756573399589774718941 4731283715024846165519603)
        ·
          refine ⟨7096925572537269248279405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4731283715024846165519603 7096925572537269248279405)
          ·
            refine ⟨2661347089701475968104777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7096925572537269248279405 2661347089701475968104777)
            ·
              refine ⟨1996010317276106976078583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661347089701475968104777 1996010317276106976078583)
              ·
                refine ⟨2994015475914160464117875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1996010317276106976078583 2994015475914160464117875)
                ·
                  refine ⟨4491023213871240696176813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2994015475914160464117875 4491023213871240696176813)
                  ·
                    refine ⟨1684133705201715261066305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4491023213871240696176813 1684133705201715261066305)
                    ·
                      refine ⟨1263100278901286445799729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684133705201715261066305 1263100278901286445799729)
                      ·
                        rfl

theorem cell23_2459879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_2459879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459879 prefixEnd_2459879 := by exact prefixLift 2459879
  have htrace : WordTrace (prefixWord ++ tailWord_2459879) baseStart_2459879 baseEnd_2459879 := by
    simpa [prefixWord, tailWord_2459879, baseEnd_2459879] using wordTrace_append hprefix tailTrace_2459879
  have hstable : (prefixWord ++ tailWord_2459879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459879).length < 2 ^ (prefixWord ++ tailWord_2459879).sum := by decide
  have hdescent : baseEnd_2459879 < baseStart_2459879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459891 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 3]
def baseStart_2459891 : Nat := 118140960795 + 2459891 * 2 ^ 59
def prefixEnd_2459891 : Nat := 4983230072969 + 3 ^ 40 * 2459891 * 2
def baseEnd_2459891 : Nat := 1263106440669140398849673

theorem tailTrace_2459891 : CollatzResearch.WordTrace tailWord_2459891 prefixEnd_2459891 1263106440669140398849673 := by
  unfold tailWord_2459891
  simp only [CollatzResearch.WordTrace]
  refine ⟨89719595531242497780771527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59813063687494998520514351 89719595531242497780771527)
  ·
    refine ⟨134579393296863746671157291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89719595531242497780771527 134579393296863746671157291)
    ·
      refine ⟨201869089945295620006735937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134579393296863746671157291 201869089945295620006735937)
      ·
        refine ⟨151401817458971715005051953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201869089945295620006735937 151401817458971715005051953)
        ·
          refine ⟨113551363094228786253788965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151401817458971715005051953 113551363094228786253788965)
          ·
            refine ⟨21290880580167897422585431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113551363094228786253788965 21290880580167897422585431)
            ·
              refine ⟨31936320870251846133878147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21290880580167897422585431 31936320870251846133878147)
              ·
                refine ⟨47904481305377769200817221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31936320870251846133878147 47904481305377769200817221)
                ·
                  refine ⟨8982090244758331725153229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47904481305377769200817221 8982090244758331725153229)
                  ·
                    refine ⟨3368283841784374396932461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8982090244758331725153229 3368283841784374396932461)
                    ·
                      refine ⟨1263106440669140398849673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3368283841784374396932461 1263106440669140398849673)
                      ·
                        rfl

theorem cell23_2459891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 3].length) (baseStart_2459891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459891 prefixEnd_2459891 := by exact prefixLift 2459891
  have htrace : WordTrace (prefixWord ++ tailWord_2459891) baseStart_2459891 baseEnd_2459891 := by
    simpa [prefixWord, tailWord_2459891, baseEnd_2459891] using wordTrace_append hprefix tailTrace_2459891
  have hstable : (prefixWord ++ tailWord_2459891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459891).length < 2 ^ (prefixWord ++ tailWord_2459891).sum := by decide
  have hdescent : baseEnd_2459891 < baseStart_2459891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459898 : List Nat := [3, 1, 1, 1, 1, 5, 2, 4, 5]
def baseStart_2459898 : Nat := 118140960795 + 2459898 * 2 ^ 59
def prefixEnd_2459898 : Nat := 4983230072969 + 3 ^ 40 * 2459898 * 2
def baseEnd_2459898 : Nat := 140345559448191319051349

theorem tailTrace_2459898 : CollatzResearch.WordTrace tailWord_2459898 prefixEnd_2459898 140345559448191319051349 := by
  unfold tailWord_2459898
  simp only [CollatzResearch.WordTrace]
  refine ⟨22429962710554284494069087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59813233894811425317517565 22429962710554284494069087)
  ·
    refine ⟨33644944065831426741103631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22429962710554284494069087 33644944065831426741103631)
    ·
      refine ⟨50467416098747140111655447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33644944065831426741103631 50467416098747140111655447)
      ·
        refine ⟨75701124148120710167483171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50467416098747140111655447 75701124148120710167483171)
        ·
          refine ⟨113551686222181065251224757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75701124148120710167483171 113551686222181065251224757)
          ·
            refine ⟨10645470583329474867302321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113551686222181065251224757 10645470583329474867302321)
            ·
              refine ⟨7984102937497106150476741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10645470583329474867302321 7984102937497106150476741)
              ·
                refine ⟨1497019300780707403214389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7984102937497106150476741 1497019300780707403214389)
                ·
                  refine ⟨140345559448191319051349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1497019300780707403214389 140345559448191319051349)
                  ·
                    rfl

theorem cell23_2459898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 5].length) (baseStart_2459898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459898 prefixEnd_2459898 := by exact prefixLift 2459898
  have htrace : WordTrace (prefixWord ++ tailWord_2459898) baseStart_2459898 baseEnd_2459898 := by
    simpa [prefixWord, tailWord_2459898, baseEnd_2459898] using wordTrace_append hprefix tailTrace_2459898
  have hstable : (prefixWord ++ tailWord_2459898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459898).length < 2 ^ (prefixWord ++ tailWord_2459898).sum := by decide
  have hdescent : baseEnd_2459898 < baseStart_2459898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459931 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 4]
def baseStart_2459931 : Nat := 118140960795 + 2459931 * 2 ^ 59
def prefixEnd_2459931 : Nat := 4983230072969 + 3 ^ 40 * 2459931 * 2
def baseEnd_2459931 : Nat := 1263126979895320242349489

theorem tailTrace_2459931 : CollatzResearch.WordTrace tailWord_2459931 prefixEnd_2459931 1263126979895320242349489 := by
  unfold tailWord_2459931
  simp only [CollatzResearch.WordTrace]
  refine ⟨89721054451097584612227647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59814036300731723074818431 89721054451097584612227647)
  ·
    refine ⟨134581581676646376918341471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89721054451097584612227647 134581581676646376918341471)
    ·
      refine ⟨201872372514969565377512207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134581581676646376918341471 201872372514969565377512207)
      ·
        refine ⟨302808558772454348066268311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201872372514969565377512207 302808558772454348066268311)
        ·
          refine ⟨454212838158681522099402467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302808558772454348066268311 454212838158681522099402467)
          ·
            refine ⟨681319257238022283149103701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454212838158681522099402467 681319257238022283149103701)
            ·
              refine ⟨7984210045758073630653559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 681319257238022283149103701 7984210045758073630653559)
              ·
                refine ⟨11976315068637110445980339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7984210045758073630653559 11976315068637110445980339)
                ·
                  refine ⟨17964472602955665668970509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11976315068637110445980339 17964472602955665668970509)
                  ·
                    refine ⟨6736677226108374625863941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17964472602955665668970509 6736677226108374625863941)
                    ·
                      refine ⟨1263126979895320242349489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6736677226108374625863941 1263126979895320242349489)
                      ·
                        rfl

theorem cell23_2459931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 4].length) (baseStart_2459931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459931 prefixEnd_2459931 := by exact prefixLift 2459931
  have htrace : WordTrace (prefixWord ++ tailWord_2459931) baseStart_2459931 baseEnd_2459931 := by
    simpa [prefixWord, tailWord_2459931, baseEnd_2459931] using wordTrace_append hprefix tailTrace_2459931
  have hstable : (prefixWord ++ tailWord_2459931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459931).length < 2 ^ (prefixWord ++ tailWord_2459931).sum := by decide
  have hdescent : baseEnd_2459931 < baseStart_2459931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459948 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 4, 4, 2]
def baseStart_2459948 : Nat := 118140960795 + 2459948 * 2 ^ 59
def prefixEnd_2459948 : Nat := 4983230072969 + 3 ^ 40 * 2459948 * 2
def baseEnd_2459948 : Nat := 1263135709066446675836911

theorem tailTrace_2459948 : CollatzResearch.WordTrace tailWord_2459948 prefixEnd_2459948 1263135709066446675836911 := by
  unfold tailWord_2459948
  simp only [CollatzResearch.WordTrace]
  refine ⟨44860837246017998257798249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59814449661357331010397665 44860837246017998257798249)
  ·
    refine ⟨33645627934513498693348687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44860837246017998257798249 33645627934513498693348687)
    ·
      refine ⟨50468441901770248040023031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33645627934513498693348687 50468441901770248040023031)
      ·
        refine ⟨75702662852655372060034547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50468441901770248040023031 75702662852655372060034547)
        ·
          refine ⟨113553994278983058090051821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75702662852655372060034547 113553994278983058090051821)
          ·
            refine ⟨42582747854618646783769433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113553994278983058090051821 42582747854618646783769433)
            ·
              refine ⟨31937060890963985087827075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42582747854618646783769433 31937060890963985087827075)
              ·
                refine ⟨47905591336445977631740613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31937060890963985087827075 47905591336445977631740613)
                ·
                  refine ⟨8982298375583620805951365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47905591336445977631740613 8982298375583620805951365)
                  ·
                    refine ⟨1684180945421928901115881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8982298375583620805951365 1684180945421928901115881)
                    ·
                      refine ⟨1263135709066446675836911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684180945421928901115881 1263135709066446675836911)
                      ·
                        rfl

theorem cell23_2459948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 4, 2].length) (baseStart_2459948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459948 prefixEnd_2459948 := by exact prefixLift 2459948
  have htrace : WordTrace (prefixWord ++ tailWord_2459948) baseStart_2459948 baseEnd_2459948 := by
    simpa [prefixWord, tailWord_2459948, baseEnd_2459948] using wordTrace_append hprefix tailTrace_2459948
  have hstable : (prefixWord ++ tailWord_2459948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459948).length < 2 ^ (prefixWord ++ tailWord_2459948).sum := by decide
  have hdescent : baseEnd_2459948 < baseStart_2459948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459949 : List Nat := [1, 5, 3, 1, 2, 1, 3, 2, 5]
def baseStart_2459949 : Nat := 118140960795 + 2459949 * 2 ^ 59
def prefixEnd_2459949 : Nat := 4983230072969 + 3 ^ 40 * 2459949 * 2
def baseEnd_2459949 : Nat := 140348469171900130213823

theorem tailTrace_2459949 : CollatzResearch.WordTrace tailWord_2459949 prefixEnd_2459949 140348469171900130213823 := by
  unfold tailWord_2459949
  simp only [CollatzResearch.WordTrace]
  refine ⟨89721710965032373686382901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59814473976688249124255267 89721710965032373686382901)
  ·
    refine ⟨8411410402971785033098397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89721710965032373686382901 8411410402971785033098397)
    ·
      refine ⟨3154278901114419387411899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8411410402971785033098397 3154278901114419387411899)
      ·
        refine ⟨4731418351671629081117849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3154278901114419387411899 4731418351671629081117849)
        ·
          refine ⟨3548563763753721810838387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4731418351671629081117849 3548563763753721810838387)
          ·
            refine ⟨5322845645630582716257581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548563763753721810838387 5322845645630582716257581)
            ·
              refine ⟨1996067117111468518596593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5322845645630582716257581 1996067117111468518596593)
              ·
                refine ⟨1497050337833601388947445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1996067117111468518596593 1497050337833601388947445)
                ·
                  refine ⟨140348469171900130213823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1497050337833601388947445 140348469171900130213823)
                  ·
                    rfl

theorem cell23_2459949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_2459949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459949 prefixEnd_2459949 := by exact prefixLift 2459949
  have htrace : WordTrace (prefixWord ++ tailWord_2459949) baseStart_2459949 baseEnd_2459949 := by
    simpa [prefixWord, tailWord_2459949, baseEnd_2459949] using wordTrace_append hprefix tailTrace_2459949
  have hstable : (prefixWord ++ tailWord_2459949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459949).length < 2 ^ (prefixWord ++ tailWord_2459949).sum := by decide
  have hdescent : baseEnd_2459949 < baseStart_2459949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459985 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 2, 2, 3]
def baseStart_2459985 : Nat := 118140960795 + 2459985 * 2 ^ 59
def prefixEnd_2459985 : Nat := 4983230072969 + 3 ^ 40 * 2459985 * 2
def baseEnd_2459985 : Nat := 1263154707850663031074241

theorem tailTrace_2459985 : CollatzResearch.WordTrace tailWord_2459985 prefixEnd_2459985 1263154707850663031074241 := by
  unfold tailWord_2459985
  simp only [CollatzResearch.WordTrace]
  refine ⟨89723023992901951834693409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59815349328601301223128939 89723023992901951834693409)
  ·
    refine ⟨67292267994676463876020057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89723023992901951834693409 67292267994676463876020057)
    ·
      refine ⟨50469200996007347907015043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67292267994676463876020057 50469200996007347907015043)
      ·
        refine ⟨75703801494011021860522565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50469200996007347907015043 75703801494011021860522565)
        ·
          refine ⟨14194462780127066598847981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75703801494011021860522565 14194462780127066598847981)
          ·
            refine ⟨5322923542547649974567993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14194462780127066598847981 5322923542547649974567993)
            ·
              refine ⟨3992192656910737480925995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5322923542547649974567993 3992192656910737480925995)
              ·
                refine ⟨5988288985366106221388993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3992192656910737480925995 5988288985366106221388993)
                ·
                  refine ⟨4491216739024579666041745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5988288985366106221388993 4491216739024579666041745)
                  ·
                    refine ⟨3368412554268434749531309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4491216739024579666041745 3368412554268434749531309)
                    ·
                      refine ⟨1263154707850663031074241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3368412554268434749531309 1263154707850663031074241)
                      ·
                        rfl

theorem cell23_2459985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_2459985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2459985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2459985 prefixEnd_2459985 := by exact prefixLift 2459985
  have htrace : WordTrace (prefixWord ++ tailWord_2459985) baseStart_2459985 baseEnd_2459985 := by
    simpa [prefixWord, tailWord_2459985, baseEnd_2459985] using wordTrace_append hprefix tailTrace_2459985
  have hstable : (prefixWord ++ tailWord_2459985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459985).length < 2 ^ (prefixWord ++ tailWord_2459985).sum := by decide
  have hdescent : baseEnd_2459985 < baseStart_2459985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460018 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_2460018 : Nat := 118140960795 + 2460018 * 2 ^ 59
def prefixEnd_2460018 : Nat := 4983230072969 + 3 ^ 40 * 2460018 * 2
def baseEnd_2460018 : Nat := 421057217570753800653863

theorem tailTrace_2460018 : CollatzResearch.WordTrace tailWord_2460018 prefixEnd_2460018 421057217570753800653863 := by
  unfold tailWord_2460018
  simp only [CollatzResearch.WordTrace]
  refine ⟨22431056900445599617661177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59816151734521598980429805 22431056900445599617661177)
  ·
    refine ⟨16823292675334199713245883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22431056900445599617661177 16823292675334199713245883)
    ·
      refine ⟨25234939013001299569868825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16823292675334199713245883 25234939013001299569868825)
      ·
        refine ⟨18926204259750974677401619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25234939013001299569868825 18926204259750974677401619)
        ·
          refine ⟨28389306389626462016102429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18926204259750974677401619 28389306389626462016102429)
          ·
            refine ⟨10645989896109923256038411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28389306389626462016102429 10645989896109923256038411)
            ·
              refine ⟨15968984844164884884057617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10645989896109923256038411 15968984844164884884057617)
              ·
                refine ⟨11976738633123663663043213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15968984844164884884057617 11976738633123663663043213)
                ·
                  refine ⟨4491276987421373873641205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11976738633123663663043213 4491276987421373873641205)
                  ·
                    refine ⟨421057217570753800653863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4491276987421373873641205 421057217570753800653863)
                    ·
                      rfl

theorem cell23_2460018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_2460018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460018 prefixEnd_2460018 := by exact prefixLift 2460018
  have htrace : WordTrace (prefixWord ++ tailWord_2460018) baseStart_2460018 baseEnd_2460018 := by
    simpa [prefixWord, tailWord_2460018, baseEnd_2460018] using wordTrace_append hprefix tailTrace_2460018
  have hstable : (prefixWord ++ tailWord_2460018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460018).length < 2 ^ (prefixWord ++ tailWord_2460018).sum := by decide
  have hdescent : baseEnd_2460018 < baseStart_2460018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460031 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 5, 6]
def baseStart_2460031 : Nat := 118140960795 + 2460031 * 2 ^ 59
def prefixEnd_2460031 : Nat := 4983230072969 + 3 ^ 40 * 2460031 * 2
def baseEnd_2460031 : Nat := 421059442653589950366343

theorem tailTrace_2460031 : CollatzResearch.WordTrace tailWord_2460031 prefixEnd_2460031 421059442653589950366343 := by
  unfold tailWord_2460031
  simp only [CollatzResearch.WordTrace]
  refine ⟨89724701750735301690867947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59816467833823534460578631 89724701750735301690867947)
  ·
    refine ⟨134587052626102952536301921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89724701750735301690867947 134587052626102952536301921)
    ·
      refine ⟨100940289469577214402226441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134587052626102952536301921 100940289469577214402226441)
      ·
        refine ⟨75705217102182910801669831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100940289469577214402226441 75705217102182910801669831)
        ·
          refine ⟨113557825653274366202504747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75705217102182910801669831 113557825653274366202504747)
          ·
            refine ⟨170336738479911549303757121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113557825653274366202504747 170336738479911549303757121)
            ·
              refine ⟨127752553859933661977817841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170336738479911549303757121 127752553859933661977817841)
              ·
                refine ⟨95814415394950246483363381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127752553859933661977817841 95814415394950246483363381)
                ·
                  refine ⟨8982601443276585607815317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95814415394950246483363381 8982601443276585607815317)
                  ·
                    refine ⟨421059442653589950366343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8982601443276585607815317 421059442653589950366343)
                    ·
                      rfl

theorem cell23_2460031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_2460031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460031 prefixEnd_2460031 := by exact prefixLift 2460031
  have htrace : WordTrace (prefixWord ++ tailWord_2460031) baseStart_2460031 baseEnd_2460031 := by
    simpa [prefixWord, tailWord_2460031, baseEnd_2460031] using wordTrace_append hprefix tailTrace_2460031
  have hstable : (prefixWord ++ tailWord_2460031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460031).length < 2 ^ (prefixWord ++ tailWord_2460031).sum := by decide
  have hdescent : baseEnd_2460031 < baseStart_2460031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460052 : List Nat := [2, 4, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_2460052 : Nat := 118140960795 + 2460052 * 2 ^ 59
def prefixEnd_2460052 : Nat := 4983230072969 + 3 ^ 40 * 2460052 * 2
def baseEnd_2460052 : Nat := 421063037018171422978811

theorem tailTrace_2460052 : CollatzResearch.WordTrace tailWord_2460052 prefixEnd_2460052 421063037018171422978811 := by
  unfold tailWord_2460052
  simp only [CollatzResearch.WordTrace]
  refine ⟨44862733841829611138691205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59816978455772814851588273 44862733841829611138691205)
  ·
    refine ⟨8411762595343052088504601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44862733841829611138691205 8411762595343052088504601)
    ·
      refine ⟨6308821946507289066378451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8411762595343052088504601 6308821946507289066378451)
      ·
        refine ⟨9463232919760933599567677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6308821946507289066378451 9463232919760933599567677)
        ·
          refine ⟨3548712344910350099837879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9463232919760933599567677 3548712344910350099837879)
          ·
            refine ⟨5323068517365525149756819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548712344910350099837879 5323068517365525149756819)
            ·
              refine ⟨7984602776048287724635229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5323068517365525149756819 7984602776048287724635229)
              ·
                refine ⟨2994226041018107896738211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7984602776048287724635229 2994226041018107896738211)
                ·
                  refine ⟨4491339061527161845107317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2994226041018107896738211 4491339061527161845107317)
                  ·
                    refine ⟨421063037018171422978811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4491339061527161845107317 421063037018171422978811)
                    ·
                      rfl

theorem cell23_2460052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_2460052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460052 prefixEnd_2460052 := by exact prefixLift 2460052
  have htrace : WordTrace (prefixWord ++ tailWord_2460052) baseStart_2460052 baseEnd_2460052 := by
    simpa [prefixWord, tailWord_2460052, baseEnd_2460052] using wordTrace_append hprefix tailTrace_2460052
  have hstable : (prefixWord ++ tailWord_2460052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460052).length < 2 ^ (prefixWord ++ tailWord_2460052).sum := by decide
  have hdescent : baseEnd_2460052 < baseStart_2460052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460068 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_2460068 : Nat := 118140960795 + 2460068 * 2 ^ 59
def prefixEnd_2460068 : Nat := 4983230072969 + 3 ^ 40 * 2460068 * 2
def baseEnd_2460068 : Nat := 1263197326744986206336359

theorem tailTrace_2460068 : CollatzResearch.WordTrace tailWord_2460068 prefixEnd_2460068 1263197326744986206336359 := by
  unfold tailWord_2460068
  simp only [CollatzResearch.WordTrace]
  refine ⟨44863025625800628504982429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59817367501067504673309905 44863025625800628504982429)
  ·
    refine ⟨16823634609675235689368411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44863025625800628504982429 16823634609675235689368411)
    ·
      refine ⟨25235451914512853534052617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16823634609675235689368411 25235451914512853534052617)
      ·
        refine ⟨18926588935884640150539463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25235451914512853534052617 18926588935884640150539463)
        ·
          refine ⟨28389883403826960225809195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18926588935884640150539463 28389883403826960225809195)
          ·
            refine ⟨42584825105740440338713793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28389883403826960225809195 42584825105740440338713793)
            ·
              refine ⟨31938618829305330254035345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42584825105740440338713793 31938618829305330254035345)
              ·
                refine ⟨23953964121978997690526509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31938618829305330254035345 23953964121978997690526509)
                ·
                  refine ⟨8982736545742124133947441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23953964121978997690526509 8982736545742124133947441)
                  ·
                    refine ⟨6737052409306593100460581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8982736545742124133947441 6737052409306593100460581)
                    ·
                      refine ⟨1263197326744986206336359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6737052409306593100460581 1263197326744986206336359)
                      ·
                        rfl

theorem cell23_2460068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_2460068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460068 prefixEnd_2460068 := by exact prefixLift 2460068
  have htrace : WordTrace (prefixWord ++ tailWord_2460068) baseStart_2460068 baseEnd_2460068 := by
    simpa [prefixWord, tailWord_2460068, baseEnd_2460068] using wordTrace_append hprefix tailTrace_2460068
  have hstable : (prefixWord ++ tailWord_2460068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460068).length < 2 ^ (prefixWord ++ tailWord_2460068).sum := by decide
  have hdescent : baseEnd_2460068 < baseStart_2460068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460082 : List Nat := [3, 2, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_2460082 : Nat := 118140960795 + 2460082 * 2 ^ 59
def prefixEnd_2460082 : Nat := 4983230072969 + 3 ^ 40 * 2460082 * 2
def baseEnd_2460082 : Nat := 421068171824716383853765

theorem tailTrace_2460082 : CollatzResearch.WordTrace tailWord_2460082 prefixEnd_2460082 421068171824716383853765 := by
  unfold tailWord_2460082
  simp only [CollatzResearch.WordTrace]
  refine ⟨22431640468387634350243625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59817707915700358267316333 22431640468387634350243625)
  ·
    refine ⟨16823730351290725762682719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22431640468387634350243625 16823730351290725762682719)
    ·
      refine ⟨25235595526936088644024079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16823730351290725762682719 25235595526936088644024079)
      ·
        refine ⟨37853393290404132966036119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25235595526936088644024079 37853393290404132966036119)
        ·
          refine ⟨56780089935606199449054179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37853393290404132966036119 56780089935606199449054179)
          ·
            refine ⟨85170134903409299173581269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56780089935606199449054179 85170134903409299173581269)
            ·
              refine ⟨1996175036798655449380811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 85170134903409299173581269 1996175036798655449380811)
              ·
                refine ⟨2994262555197983174071217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1996175036798655449380811 2994262555197983174071217)
                ·
                  refine ⟨2245696916398487380553413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2994262555197983174071217 2245696916398487380553413)
                  ·
                    refine ⟨421068171824716383853765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2245696916398487380553413 421068171824716383853765)
                    ·
                      rfl

theorem cell23_2460082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_2460082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460082 prefixEnd_2460082 := by exact prefixLift 2460082
  have htrace : WordTrace (prefixWord ++ tailWord_2460082) baseStart_2460082 baseEnd_2460082 := by
    simpa [prefixWord, tailWord_2460082, baseEnd_2460082] using wordTrace_append hprefix tailTrace_2460082
  have hstable : (prefixWord ++ tailWord_2460082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460082).length < 2 ^ (prefixWord ++ tailWord_2460082).sum := by decide
  have hdescent : baseEnd_2460082 < baseStart_2460082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460085 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_2460085 : Nat := 118140960795 + 2460085 * 2 ^ 59
def prefixEnd_2460085 : Nat := 4983230072969 + 3 ^ 40 * 2460085 * 2
def baseEnd_2460085 : Nat := 1263206055916112639823781

theorem tailTrace_2460085 : CollatzResearch.WordTrace tailWord_2460085 prefixEnd_2460085 1263206055916112639823781 := by
  unfold tailWord_2460085
  simp only [CollatzResearch.WordTrace]
  refine ⟨89726671292539668913333709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59817780861693112608889139 89726671292539668913333709)
  ·
    refine ⟨33647501734702375842500141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89726671292539668913333709 33647501734702375842500141)
    ·
      refine ⟨12617813150513390940937553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33647501734702375842500141 12617813150513390940937553)
      ·
        refine ⟨9463359862885043205703165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12617813150513390940937553 9463359862885043205703165)
        ·
          refine ⟨3548759948581891202138687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9463359862885043205703165 3548759948581891202138687)
          ·
            refine ⟨5323139922872836803208031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548759948581891202138687 5323139922872836803208031)
            ·
              refine ⟨7984709884309255204812047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5323139922872836803208031 7984709884309255204812047)
              ·
                refine ⟨11977064826463882807218071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7984709884309255204812047 11977064826463882807218071)
                ·
                  refine ⟨17965597239695824210827107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11977064826463882807218071 17965597239695824210827107)
                  ·
                    refine ⟨26948395859543736316240661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17965597239695824210827107 26948395859543736316240661)
                    ·
                      refine ⟨1263206055916112639823781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26948395859543736316240661 1263206055916112639823781)
                      ·
                        rfl

theorem cell23_2460085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_2460085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460085 prefixEnd_2460085 := by exact prefixLift 2460085
  have htrace : WordTrace (prefixWord ++ tailWord_2460085) baseStart_2460085 baseEnd_2460085 := by
    simpa [prefixWord, tailWord_2460085, baseEnd_2460085] using wordTrace_append hprefix tailTrace_2460085
  have hstable : (prefixWord ++ tailWord_2460085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460085).length < 2 ^ (prefixWord ++ tailWord_2460085).sum := by decide
  have hdescent : baseEnd_2460085 < baseStart_2460085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460092 : List Nat := [2, 2, 2, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_2460092 : Nat := 118140960795 + 2460092 * 2 ^ 59
def prefixEnd_2460092 : Nat := 4983230072969 + 3 ^ 40 * 2460092 * 2
def baseEnd_2460092 : Nat := 1263209650280694112436249

theorem tailTrace_2460092 : CollatzResearch.WordTrace tailWord_2460092 prefixEnd_2460092 1263209650280694112436249 := by
  unfold tailWord_2460092
  simp only [CollatzResearch.WordTrace]
  refine ⟨44863463301757154554419265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59817951069009539405892353 44863463301757154554419265)
  ·
    refine ⟨33647597476317865915814449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44863463301757154554419265 33647597476317865915814449)
    ·
      refine ⟨25235698107238399436860837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33647597476317865915814449 25235698107238399436860837)
      ·
        refine ⟨4731693395107199894411407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25235698107238399436860837 4731693395107199894411407)
        ·
          refine ⟨7097540092660799841617111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4731693395107199894411407 7097540092660799841617111)
          ·
            refine ⟨10646310138991199762425667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7097540092660799841617111 10646310138991199762425667)
            ·
              refine ⟨15969465208486799643638501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10646310138991199762425667 15969465208486799643638501)
              ·
                refine ⟨2994274726591274933182219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15969465208486799643638501 2994274726591274933182219)
                ·
                  refine ⟨4491412089886912399773329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2994274726591274933182219 4491412089886912399773329)
                  ·
                    refine ⟨3368559067415184299829997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4491412089886912399773329 3368559067415184299829997)
                    ·
                      refine ⟨1263209650280694112436249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3368559067415184299829997 1263209650280694112436249)
                      ·
                        rfl

theorem cell23_2460092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_2460092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460092 prefixEnd_2460092 := by exact prefixLift 2460092
  have htrace : WordTrace (prefixWord ++ tailWord_2460092) baseStart_2460092 baseEnd_2460092 := by
    simpa [prefixWord, tailWord_2460092, baseEnd_2460092] using wordTrace_append hprefix tailTrace_2460092
  have hstable : (prefixWord ++ tailWord_2460092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460092).length < 2 ^ (prefixWord ++ tailWord_2460092).sum := by decide
  have hdescent : baseEnd_2460092 < baseStart_2460092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460105 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 4, 1, 3]
def baseStart_2460105 : Nat := 118140960795 + 2460105 * 2 ^ 59
def prefixEnd_2460105 : Nat := 4983230072969 + 3 ^ 40 * 2460105 * 2
def baseEnd_2460105 : Nat := 1263216325529202561573689

theorem tailTrace_2460105 : CollatzResearch.WordTrace tailWord_2460105 prefixEnd_2460105 1263216325529202561573689 := by
  unfold tailWord_2460105
  simp only [CollatzResearch.WordTrace]
  refine ⟨89727400752467212329061769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59818267168311474886041179 89727400752467212329061769)
  ·
    refine ⟨67295550564350409246796327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89727400752467212329061769 67295550564350409246796327)
    ·
      refine ⟨100943325846525613870194491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67295550564350409246796327 100943325846525613870194491)
      ·
        refine ⟨151414988769788420805291737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100943325846525613870194491 151414988769788420805291737)
        ·
          refine ⟨113561241577341315603968803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151414988769788420805291737 113561241577341315603968803)
          ·
            refine ⟨170341862366011973405953205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113561241577341315603968803 170341862366011973405953205)
            ·
              refine ⟨15969549596813622506808113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170341862366011973405953205 15969549596813622506808113)
              ·
                refine ⟨11977162197610216880106085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15969549596813622506808113 11977162197610216880106085)
                ·
                  refine ⟨2245717912051915665019891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11977162197610216880106085 2245717912051915665019891)
                  ·
                    refine ⟨3368576868077873497529837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2245717912051915665019891 3368576868077873497529837)
                    ·
                      refine ⟨1263216325529202561573689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3368576868077873497529837 1263216325529202561573689)
                      ·
                        rfl

theorem cell23_2460105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 1, 3].length) (baseStart_2460105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460105 prefixEnd_2460105 := by exact prefixLift 2460105
  have htrace : WordTrace (prefixWord ++ tailWord_2460105) baseStart_2460105 baseEnd_2460105 := by
    simpa [prefixWord, tailWord_2460105, baseEnd_2460105] using wordTrace_append hprefix tailTrace_2460105
  have hstable : (prefixWord ++ tailWord_2460105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460105).length < 2 ^ (prefixWord ++ tailWord_2460105).sum := by decide
  have hdescent : baseEnd_2460105 < baseStart_2460105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460122 : List Nat := [3, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3]
def baseStart_2460122 : Nat := 118140960795 + 2460122 * 2 ^ 59
def prefixEnd_2460122 : Nat := 4983230072969 + 3 ^ 40 * 2460122 * 2
def baseEnd_2460122 : Nat := 1263225054700328995061111

theorem tailTrace_2460122 : CollatzResearch.WordTrace tailWord_2460122 prefixEnd_2460122 1263225054700328995061111 := by
  unfold tailWord_2460122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22432005198351406058107655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59818680528937082821620413 22432005198351406058107655)
  ·
    refine ⟨33648007797527109087161483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22432005198351406058107655 33648007797527109087161483)
    ·
      refine ⟨50472011696290663630742225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33648007797527109087161483 50472011696290663630742225)
      ·
        refine ⟨37854008772217997723056669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50472011696290663630742225 37854008772217997723056669)
        ·
          refine ⟨14195253289581749146146251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37854008772217997723056669 14195253289581749146146251)
          ·
            refine ⟨21292879934372623719219377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14195253289581749146146251 21292879934372623719219377)
            ·
              refine ⟨15969659950779467789414533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21292879934372623719219377 15969659950779467789414533)
              ·
                refine ⟨2994311240771150210515225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15969659950779467789414533 2994311240771150210515225)
                ·
                  refine ⟨2245733430578362657886419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2994311240771150210515225 2245733430578362657886419)
                  ·
                    refine ⟨3368600145867543986829629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2245733430578362657886419 3368600145867543986829629)
                    ·
                      refine ⟨1263225054700328995061111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3368600145867543986829629 1263225054700328995061111)
                      ·
                        rfl

theorem cell23_2460122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_2460122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460122 prefixEnd_2460122 := by exact prefixLift 2460122
  have htrace : WordTrace (prefixWord ++ tailWord_2460122) baseStart_2460122 baseEnd_2460122 := by
    simpa [prefixWord, tailWord_2460122, baseEnd_2460122] using wordTrace_append hprefix tailTrace_2460122
  have hstable : (prefixWord ++ tailWord_2460122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460122).length < 2 ^ (prefixWord ++ tailWord_2460122).sum := by decide
  have hdescent : baseEnd_2460122 < baseStart_2460122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460128 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 4]
def baseStart_2460128 : Nat := 118140960795 + 2460128 * 2 ^ 59
def prefixEnd_2460128 : Nat := 4983230072969 + 3 ^ 40 * 2460128 * 2
def baseEnd_2460128 : Nat := 1263228135584255971586083

theorem tailTrace_2460128 : CollatzResearch.WordTrace tailWord_2460128 prefixEnd_2460128 1263228135584255971586083 := by
  unfold tailWord_2460128
  simp only [CollatzResearch.WordTrace]
  refine ⟨44864119815691943628574519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59818826420922591504766025 44864119815691943628574519)
  ·
    refine ⟨67296179723537915442861779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44864119815691943628574519 67296179723537915442861779)
    ·
      refine ⟨100944269585306873164292669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67296179723537915442861779 100944269585306873164292669)
      ·
        refine ⟨37854101094490077436609751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100944269585306873164292669 37854101094490077436609751)
        ·
          refine ⟨56781151641735116154914627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37854101094490077436609751 56781151641735116154914627)
          ·
            refine ⟨85171727462602674232371941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56781151641735116154914627 85171727462602674232371941)
            ·
              refine ⟨15969698899238001418569739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85171727462602674232371941 15969698899238001418569739)
              ·
                refine ⟨23954548348857002127854609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15969698899238001418569739 23954548348857002127854609)
                ·
                  refine ⟨17965911261642751595890957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23954548348857002127854609 17965911261642751595890957)
                  ·
                    refine ⟨6737216723116031848459109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17965911261642751595890957 6737216723116031848459109)
                    ·
                      refine ⟨1263228135584255971586083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6737216723116031848459109 1263228135584255971586083)
                      ·
                        rfl

theorem cell23_2460128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_2460128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460128 prefixEnd_2460128 := by exact prefixLift 2460128
  have htrace : WordTrace (prefixWord ++ tailWord_2460128) baseStart_2460128 baseEnd_2460128 := by
    simpa [prefixWord, tailWord_2460128, baseEnd_2460128] using wordTrace_append hprefix tailTrace_2460128
  have hstable : (prefixWord ++ tailWord_2460128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460128).length < 2 ^ (prefixWord ++ tailWord_2460128).sum := by decide
  have hdescent : baseEnd_2460128 < baseStart_2460128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460173 : List Nat := [1, 7, 1, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2460173 : Nat := 118140960795 + 2460173 * 2 ^ 59
def prefixEnd_2460173 : Nat := 4983230072969 + 3 ^ 40 * 2460173 * 2
def baseEnd_2460173 : Nat := 1263251242213708295523377

theorem tailTrace_2460173 : CollatzResearch.WordTrace tailWord_2460173 prefixEnd_2460173 1263251242213708295523377 := by
  unfold tailWord_2460173
  simp only [CollatzResearch.WordTrace]
  refine ⟨89729880916220859942537173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59819920610813906628358115 89729880916220859942537173)
  ·
    refine ⟨2103044083973926404903215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 89729880916220859942537173 2103044083973926404903215)
    ·
      refine ⟨3154566125960889607354823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2103044083973926404903215 3154566125960889607354823)
      ·
        refine ⟨4731849188941334411032235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3154566125960889607354823 4731849188941334411032235)
        ·
          refine ⟨7097773783412001616548353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4731849188941334411032235 7097773783412001616548353)
          ·
            refine ⟨5323330337559001212411265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7097773783412001616548353 5323330337559001212411265)
            ·
              refine ⟨3992497753169250909308449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5323330337559001212411265 3992497753169250909308449)
              ·
                refine ⟨2994373314876938181981337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3992497753169250909308449 2994373314876938181981337)
                ·
                  refine ⟨2245779986157703636486003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2994373314876938181981337 2245779986157703636486003)
                  ·
                    refine ⟨3368669979236555454729005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2245779986157703636486003 3368669979236555454729005)
                    ·
                      refine ⟨1263251242213708295523377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3368669979236555454729005 1263251242213708295523377)
                      ·
                        rfl

theorem cell23_2460173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2460173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460173 prefixEnd_2460173 := by exact prefixLift 2460173
  have htrace : WordTrace (prefixWord ++ tailWord_2460173) baseStart_2460173 baseEnd_2460173 := by
    simpa [prefixWord, tailWord_2460173, baseEnd_2460173] using wordTrace_append hprefix tailTrace_2460173
  have hstable : (prefixWord ++ tailWord_2460173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460173).length < 2 ^ (prefixWord ++ tailWord_2460173).sum := by decide
  have hdescent : baseEnd_2460173 < baseStart_2460173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460179 : List Nat := [1, 1, 1, 2, 1, 5, 4, 2, 2, 2, 2]
def baseStart_2460179 : Nat := 118140960795 + 2460179 * 2 ^ 59
def prefixEnd_2460179 : Nat := 4983230072969 + 3 ^ 40 * 2460179 * 2
def baseEnd_2460179 : Nat := 1263254323097635272048349

theorem tailTrace_2460179 : CollatzResearch.WordTrace tailWord_2460179 prefixEnd_2460179 1263254323097635272048349 := by
  unfold tailWord_2460179
  simp only [CollatzResearch.WordTrace]
  refine ⟨89730099754199122967255591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59820066502799415311503727 89730099754199122967255591)
  ·
    refine ⟨134595149631298684450883387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89730099754199122967255591 134595149631298684450883387)
    ·
      refine ⟨201892724446948026676325081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134595149631298684450883387 201892724446948026676325081)
      ·
        refine ⟨151419543335211020007243811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201892724446948026676325081 151419543335211020007243811)
        ·
          refine ⟨227129315002816530010865717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151419543335211020007243811 227129315002816530010865717)
          ·
            refine ⟨21293373281514049688518661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 227129315002816530010865717 21293373281514049688518661)
            ·
              refine ⟨3992507490283884316597249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21293373281514049688518661 3992507490283884316597249)
              ·
                refine ⟨2994380617712913237447937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3992507490283884316597249 2994380617712913237447937)
                ·
                  refine ⟨2245785463284684928085953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2994380617712913237447937 2245785463284684928085953)
                  ·
                    refine ⟨1684339097463513696064465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2245785463284684928085953 1684339097463513696064465)
                    ·
                      refine ⟨1263254323097635272048349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684339097463513696064465 1263254323097635272048349)
                      ·
                        rfl

theorem cell23_2460179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 2, 2].length) (baseStart_2460179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460179 prefixEnd_2460179 := by exact prefixLift 2460179
  have htrace : WordTrace (prefixWord ++ tailWord_2460179) baseStart_2460179 baseEnd_2460179 := by
    simpa [prefixWord, tailWord_2460179, baseEnd_2460179] using wordTrace_append hprefix tailTrace_2460179
  have hstable : (prefixWord ++ tailWord_2460179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460179).length < 2 ^ (prefixWord ++ tailWord_2460179).sum := by decide
  have hdescent : baseEnd_2460179 < baseStart_2460179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460185 : List Nat := [1, 2, 1, 2, 1, 1, 2, 8, 5]
def baseStart_2460185 : Nat := 118140960795 + 2460185 * 2 ^ 59
def prefixEnd_2460185 : Nat := 4983230072969 + 3 ^ 40 * 2460185 * 2
def baseEnd_2460185 : Nat := 140361933775729138730369

theorem tailTrace_2460185 : CollatzResearch.WordTrace tailWord_2460185 prefixEnd_2460185 140361933775729138730369 := by
  unfold tailWord_2460185
  simp only [CollatzResearch.WordTrace]
  refine ⟨89730318592177385991974009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59820212394784923994649339 89730318592177385991974009)
  ·
    refine ⟨67297738944133039493980507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89730318592177385991974009 67297738944133039493980507)
    ·
      refine ⟨100946608416199559240970761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67297738944133039493980507 100946608416199559240970761)
      ·
        refine ⟨75709956312149669430728071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100946608416199559240970761 75709956312149669430728071)
        ·
          refine ⟨113564934468224504146092107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75709956312149669430728071 113564934468224504146092107)
          ·
            refine ⟨170347401702336756219138161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113564934468224504146092107 170347401702336756219138161)
            ·
              refine ⟨127760551276752567164353621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170347401702336756219138161 127760551276752567164353621)
              ·
                refine ⟨1497193960274444146457269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 127760551276752567164353621 1497193960274444146457269)
                ·
                  refine ⟨140361933775729138730369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1497193960274444146457269 140361933775729138730369)
                  ·
                    rfl

theorem cell23_2460185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 5].length) (baseStart_2460185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460185 prefixEnd_2460185 := by exact prefixLift 2460185
  have htrace : WordTrace (prefixWord ++ tailWord_2460185) baseStart_2460185 baseEnd_2460185 := by
    simpa [prefixWord, tailWord_2460185, baseEnd_2460185] using wordTrace_append hprefix tailTrace_2460185
  have hstable : (prefixWord ++ tailWord_2460185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460185).length < 2 ^ (prefixWord ++ tailWord_2460185).sum := by decide
  have hdescent : baseEnd_2460185 < baseStart_2460185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460192 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2460192 : Nat := 118140960795 + 2460192 * 2 ^ 59
def prefixEnd_2460192 : Nat := 4983230072969 + 3 ^ 40 * 2460192 * 2
def baseEnd_2460192 : Nat := 1263260998346143721185789

theorem tailTrace_2460192 : CollatzResearch.WordTrace tailWord_2460192 prefixEnd_2460192 1263260998346143721185789 := by
  unfold tailWord_2460192
  simp only [CollatzResearch.WordTrace]
  refine ⟨44865286951576013093739415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59820382602101350791652553 44865286951576013093739415)
  ·
    refine ⟨67297930427364019640609123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44865286951576013093739415 67297930427364019640609123)
    ·
      refine ⟨100946895641046029460913685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67297930427364019640609123 100946895641046029460913685)
      ·
        refine ⟨4731885733174032630980329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100946895641046029460913685 4731885733174032630980329)
        ·
          refine ⟨3548914299880524473235247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4731885733174032630980329 3548914299880524473235247)
          ·
            refine ⟨5323371449820786709852871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548914299880524473235247 5323371449820786709852871)
            ·
              refine ⟨7985057174731180064779307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5323371449820786709852871 7985057174731180064779307)
              ·
                refine ⟨11977585762096770097168961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7985057174731180064779307 11977585762096770097168961)
                ·
                  refine ⟨8983189321572577572876721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11977585762096770097168961 8983189321572577572876721)
                  ·
                    refine ⟨6737391991179433179657541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8983189321572577572876721 6737391991179433179657541)
                    ·
                      refine ⟨1263260998346143721185789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6737391991179433179657541 1263260998346143721185789)
                      ·
                        rfl

theorem cell23_2460192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2460192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460192 prefixEnd_2460192 := by exact prefixLift 2460192
  have htrace : WordTrace (prefixWord ++ tailWord_2460192) baseStart_2460192 baseEnd_2460192 := by
    simpa [prefixWord, tailWord_2460192, baseEnd_2460192] using wordTrace_append hprefix tailTrace_2460192
  have hstable : (prefixWord ++ tailWord_2460192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460192).length < 2 ^ (prefixWord ++ tailWord_2460192).sum := by decide
  have hdescent : baseEnd_2460192 < baseStart_2460192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460195 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 3]
def baseStart_2460195 : Nat := 118140960795 + 2460195 * 2 ^ 59
def prefixEnd_2460195 : Nat := 4983230072969 + 3 ^ 40 * 2460195 * 2
def baseEnd_2460195 : Nat := 1263262538788107209448275

theorem tailTrace_2460195 : CollatzResearch.WordTrace tailWord_2460195 prefixEnd_2460195 1263262538788107209448275 := by
  unfold tailWord_2460195
  simp only [CollatzResearch.WordTrace]
  refine ⟨89730683322141157699838039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59820455548094105133225359 89730683322141157699838039)
  ·
    refine ⟨134596024983211736549757059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89730683322141157699838039 134596024983211736549757059)
    ·
      refine ⟨201894037474817604824635589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134596024983211736549757059 201894037474817604824635589)
      ·
        refine ⟨37855132026528300904619173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201894037474817604824635589 37855132026528300904619173)
        ·
          refine ⟨7097837254974056419616095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37855132026528300904619173 7097837254974056419616095)
          ·
            refine ⟨10646755882461084629424143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7097837254974056419616095 10646755882461084629424143)
            ·
              refine ⟨15970133823691626944136215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10646755882461084629424143 15970133823691626944136215)
              ·
                refine ⟨23955200735537440416204323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15970133823691626944136215 23955200735537440416204323)
                ·
                  refine ⟨35932801103306160624306485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23955200735537440416204323 35932801103306160624306485)
                  ·
                    refine ⟨3368700103434952558528733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35932801103306160624306485 3368700103434952558528733)
                    ·
                      refine ⟨1263262538788107209448275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3368700103434952558528733 1263262538788107209448275)
                      ·
                        rfl

theorem cell23_2460195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_2460195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460195 prefixEnd_2460195 := by exact prefixLift 2460195
  have htrace : WordTrace (prefixWord ++ tailWord_2460195) baseStart_2460195 baseEnd_2460195 := by
    simpa [prefixWord, tailWord_2460195, baseEnd_2460195] using wordTrace_append hprefix tailTrace_2460195
  have hstable : (prefixWord ++ tailWord_2460195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460195).length < 2 ^ (prefixWord ++ tailWord_2460195).sum := by decide
  have hdescent : baseEnd_2460195 < baseStart_2460195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460196 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 1, 4, 2]
def baseStart_2460196 : Nat := 118140960795 + 2460196 * 2 ^ 59
def prefixEnd_2460196 : Nat := 4983230072969 + 3 ^ 40 * 2460196 * 2
def baseEnd_2460196 : Nat := 1263263052268761705535771

theorem tailTrace_2460196 : CollatzResearch.WordTrace tailWord_2460196 prefixEnd_2460196 1263263052268761705535771 := by
  unfold tailWord_2460196
  simp only [CollatzResearch.WordTrace]
  refine ⟨44865359897568767435312221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59820479863425023247082961 44865359897568767435312221)
  ·
    refine ⟨16824509961588287788242083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44865359897568767435312221 16824509961588287788242083)
    ·
      refine ⟨25236764942382431682363125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16824509961588287788242083 25236764942382431682363125)
      ·
        refine ⟨2365946713348352970221543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25236764942382431682363125 2365946713348352970221543)
        ·
          refine ⟨3548920070022529455332315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365946713348352970221543 3548920070022529455332315)
          ·
            refine ⟨5323380105033794182998473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548920070022529455332315 5323380105033794182998473)
            ·
              refine ⟨3992535078775345637248855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5323380105033794182998473 3992535078775345637248855)
              ·
                refine ⟨5988802618163018455873283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3992535078775345637248855 5988802618163018455873283)
                ·
                  refine ⟨8983203927244527683809925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5988802618163018455873283 8983203927244527683809925)
                  ·
                    refine ⟨1684350736358348940714361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8983203927244527683809925 1684350736358348940714361)
                    ·
                      refine ⟨1263263052268761705535771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684350736358348940714361 1263263052268761705535771)
                      ·
                        rfl

theorem cell23_2460196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_2460196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460196 prefixEnd_2460196 := by exact prefixLift 2460196
  have htrace : WordTrace (prefixWord ++ tailWord_2460196) baseStart_2460196 baseEnd_2460196 := by
    simpa [prefixWord, tailWord_2460196, baseEnd_2460196] using wordTrace_append hprefix tailTrace_2460196
  have hstable : (prefixWord ++ tailWord_2460196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460196).length < 2 ^ (prefixWord ++ tailWord_2460196).sum := by decide
  have hdescent : baseEnd_2460196 < baseStart_2460196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460208 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 7]
def baseStart_2460208 : Nat := 118140960795 + 2460208 * 2 ^ 59
def prefixEnd_2460208 : Nat := 4983230072969 + 3 ^ 40 * 2460208 * 2
def baseEnd_2460208 : Nat := 1263269214036615658585715

theorem tailTrace_2460208 : CollatzResearch.WordTrace tailWord_2460208 prefixEnd_2460208 1263269214036615658585715 := by
  unfold tailWord_2460208
  simp only [CollatzResearch.WordTrace]
  refine ⟨44865578735547030460030639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59820771647396040613374185 44865578735547030460030639)
  ·
    refine ⟨67298368103320545690045959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44865578735547030460030639 67298368103320545690045959)
    ·
      refine ⟨100947552154980818535068939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67298368103320545690045959 100947552154980818535068939)
      ·
        refine ⟨151421328232471227802603409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100947552154980818535068939 151421328232471227802603409)
        ·
          refine ⟨113565996174353420851952557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151421328232471227802603409 113565996174353420851952557)
          ·
            refine ⟨42587248565382532819482209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113565996174353420851952557 42587248565382532819482209)
            ·
              refine ⟨31940436424036899614611657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42587248565382532819482209 31940436424036899614611657)
              ·
                refine ⟨23955327318027674710958743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31940436424036899614611657 23955327318027674710958743)
                ·
                  refine ⟨35932990977041512066438115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23955327318027674710958743 35932990977041512066438115)
                  ·
                    refine ⟨53899486465562268099657173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35932990977041512066438115 53899486465562268099657173)
                    ·
                      refine ⟨1263269214036615658585715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53899486465562268099657173 1263269214036615658585715)
                      ·
                        rfl

theorem cell23_2460208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_2460208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460208 prefixEnd_2460208 := by exact prefixLift 2460208
  have htrace : WordTrace (prefixWord ++ tailWord_2460208) baseStart_2460208 baseEnd_2460208 := by
    simpa [prefixWord, tailWord_2460208, baseEnd_2460208] using wordTrace_append hprefix tailTrace_2460208
  have hstable : (prefixWord ++ tailWord_2460208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460208).length < 2 ^ (prefixWord ++ tailWord_2460208).sum := by decide
  have hdescent : baseEnd_2460208 < baseStart_2460208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460230 : List Nat := [6, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_2460230 : Nat := 118140960795 + 2460230 * 2 ^ 59
def prefixEnd_2460230 : Nat := 4983230072969 + 3 ^ 40 * 2460230 * 2
def baseEnd_2460230 : Nat := 1263280510611014572510615

theorem tailTrace_2460230 : CollatzResearch.WordTrace tailWord_2460230 prefixEnd_2460230 1263280510611014572510615 := by
  unfold tailWord_2460230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2804123746156698708667567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59821306584676239118241429 2804123746156698708667567)
  ·
    refine ⟨4206185619235048063001351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2804123746156698708667567 4206185619235048063001351)
    ·
      refine ⟨6309278428852572094502027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4206185619235048063001351 6309278428852572094502027)
      ·
        refine ⟨9463917643278858141753041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6309278428852572094502027 9463917643278858141753041)
        ·
          refine ⟨7097938232459143606314781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9463917643278858141753041 7097938232459143606314781)
          ·
            refine ⟨2661726837172178852368043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7097938232459143606314781 2661726837172178852368043)
            ·
              refine ⟨3992590255758268278552065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2661726837172178852368043 3992590255758268278552065)
              ·
                refine ⟨2994442691818701208914049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3992590255758268278552065 2994442691818701208914049)
                ·
                  refine ⟨2245832018864025906685537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2994442691818701208914049 2245832018864025906685537)
                  ·
                    refine ⟨1684374014148019430014153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2245832018864025906685537 1684374014148019430014153)
                    ·
                      refine ⟨1263280510611014572510615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684374014148019430014153 1263280510611014572510615)
                      ·
                        rfl

theorem cell23_2460230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_2460230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460230 prefixEnd_2460230 := by exact prefixLift 2460230
  have htrace : WordTrace (prefixWord ++ tailWord_2460230) baseStart_2460230 baseEnd_2460230 := by
    simpa [prefixWord, tailWord_2460230, baseEnd_2460230] using wordTrace_append hprefix tailTrace_2460230
  have hstable : (prefixWord ++ tailWord_2460230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460230).length < 2 ^ (prefixWord ++ tailWord_2460230).sum := by decide
  have hdescent : baseEnd_2460230 < baseStart_2460230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460235 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 4]
def baseStart_2460235 : Nat := 118140960795 + 2460235 * 2 ^ 59
def prefixEnd_2460235 : Nat := 4983230072969 + 3 ^ 40 * 2460235 * 2
def baseEnd_2460235 : Nat := 1263283078014287052948091

theorem tailTrace_2460235 : CollatzResearch.WordTrace tailWord_2460235 prefixEnd_2460235 1263283078014287052948091 := by
  unfold tailWord_2460235
  simp only [CollatzResearch.WordTrace]
  refine ⟨89732142241996244531294159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59821428161330829687529439 89732142241996244531294159)
  ·
    refine ⟨134598213362994366796941239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89732142241996244531294159 134598213362994366796941239)
    ·
      refine ⟨201897320044491550195411859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134598213362994366796941239 201897320044491550195411859)
      ·
        refine ⟨302845980066737325293117789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201897320044491550195411859 302845980066737325293117789)
        ·
          refine ⟨113567242525026496984919171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302845980066737325293117789 113567242525026496984919171)
          ·
            refine ⟨170350863787539745477378757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113567242525026496984919171 170350863787539745477378757)
            ·
              refine ⟨31940786960163702277008517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170350863787539745477378757 31940786960163702277008517)
              ·
                refine ⟨5988897555030694176939097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31940786960163702277008517 5988897555030694176939097)
                ·
                  refine ⟨4491673166273020632704323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5988897555030694176939097 4491673166273020632704323)
                  ·
                    refine ⟨6737509749409530949056485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4491673166273020632704323 6737509749409530949056485)
                    ·
                      refine ⟨1263283078014287052948091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6737509749409530949056485 1263283078014287052948091)
                      ·
                        rfl

theorem cell23_2460235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 4].length) (baseStart_2460235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460235 prefixEnd_2460235 := by exact prefixLift 2460235
  have htrace : WordTrace (prefixWord ++ tailWord_2460235) baseStart_2460235 baseEnd_2460235 := by
    simpa [prefixWord, tailWord_2460235, baseEnd_2460235] using wordTrace_append hprefix tailTrace_2460235
  have hstable : (prefixWord ++ tailWord_2460235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460235).length < 2 ^ (prefixWord ++ tailWord_2460235).sum := by decide
  have hdescent : baseEnd_2460235 < baseStart_2460235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460279 : List Nat := [1, 1, 3, 1, 1, 3, 5, 3, 1, 4]
def baseStart_2460279 : Nat := 118140960795 + 2460279 * 2 ^ 59
def prefixEnd_2460279 : Nat := 4983230072969 + 3 ^ 40 * 2460279 * 2
def baseEnd_2460279 : Nat := 421101890387694960265963

theorem tailTrace_2460279 : CollatzResearch.WordTrace tailWord_2460279 prefixEnd_2460279 421101890387694960265963 := by
  unfold tailWord_2460279
  simp only [CollatzResearch.WordTrace]
  refine ⟨89733747053836840045895891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59822498035891226697263927 89733747053836840045895891)
  ·
    refine ⟨134600620580755260068843837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89733747053836840045895891 134600620580755260068843837)
    ·
      refine ⟨50475232717783222525816439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134600620580755260068843837 50475232717783222525816439)
      ·
        refine ⟨75712849076674833788724659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50475232717783222525816439 75712849076674833788724659)
        ·
          refine ⟨113569273615012250683086989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75712849076674833788724659 113569273615012250683086989)
          ·
            refine ⟨42588477605629594006157621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113569273615012250683086989 42588477605629594006157621)
            ·
              refine ⟨3992669775527774438077277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42588477605629594006157621 3992669775527774438077277)
              ·
                refine ⟨1497251165822915414278979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3992669775527774438077277 1497251165822915414278979)
                ·
                  refine ⟨2245876748734373121418469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497251165822915414278979 2245876748734373121418469)
                  ·
                    refine ⟨421101890387694960265963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2245876748734373121418469 421101890387694960265963)
                    ·
                      rfl

theorem cell23_2460279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_2460279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460279 prefixEnd_2460279 := by exact prefixLift 2460279
  have htrace : WordTrace (prefixWord ++ tailWord_2460279) baseStart_2460279 baseEnd_2460279 := by
    simpa [prefixWord, tailWord_2460279, baseEnd_2460279] using wordTrace_append hprefix tailTrace_2460279
  have hstable : (prefixWord ++ tailWord_2460279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460279).length < 2 ^ (prefixWord ++ tailWord_2460279).sum := by decide
  have hdescent : baseEnd_2460279 < baseStart_2460279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460335 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 3, 6]
def baseStart_2460335 : Nat := 118140960795 + 2460335 * 2 ^ 59
def prefixEnd_2460335 : Nat := 4983230072969 + 3 ^ 40 * 2460335 * 2
def baseEnd_2460335 : Nat := 421111475359912220565877

theorem tailTrace_2460335 : CollatzResearch.WordTrace tailWord_2460335 prefixEnd_2460335 421111475359912220565877 := by
  unfold tailWord_2460335
  simp only [CollatzResearch.WordTrace]
  refine ⟨89735789541633961609934459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59823859694422641073289639 89735789541633961609934459)
  ·
    refine ⟨134603684312450942414901689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89735789541633961609934459 134603684312450942414901689)
    ·
      refine ⟨100952763234338206811176267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134603684312450942414901689 100952763234338206811176267)
      ·
        refine ⟨151429144851507310216764401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100952763234338206811176267 151429144851507310216764401)
        ·
          refine ⟨113571858638630482662573301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151429144851507310216764401 113571858638630482662573301)
          ·
            refine ⟨10647361747371607749616247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113571858638630482662573301 10647361747371607749616247)
            ·
              refine ⟨15971042621057411624424371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10647361747371607749616247 15971042621057411624424371)
              ·
                refine ⟨23956563931586117436636557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15971042621057411624424371 23956563931586117436636557)
                ·
                  refine ⟨8983711474344794038738709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23956563931586117436636557 8983711474344794038738709)
                  ·
                    refine ⟨421111475359912220565877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8983711474344794038738709 421111475359912220565877)
                    ·
                      rfl

theorem cell23_2460335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_2460335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460335 prefixEnd_2460335 := by exact prefixLift 2460335
  have htrace : WordTrace (prefixWord ++ tailWord_2460335) baseStart_2460335 baseEnd_2460335 := by
    simpa [prefixWord, tailWord_2460335, baseEnd_2460335] using wordTrace_append hprefix tailTrace_2460335
  have hstable : (prefixWord ++ tailWord_2460335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460335).length < 2 ^ (prefixWord ++ tailWord_2460335).sum := by decide
  have hdescent : baseEnd_2460335 < baseStart_2460335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460339 : List Nat := [1, 1, 1, 2, 3, 5, 3, 1, 1, 5]
def baseStart_2460339 : Nat := 118140960795 + 2460339 * 2 ^ 59
def prefixEnd_2460339 : Nat := 4983230072969 + 3 ^ 40 * 2460339 * 2
def baseEnd_2460339 : Nat := 421112160000784882015871

theorem tailTrace_2460339 : CollatzResearch.WordTrace tailWord_2460339 prefixEnd_2460339 421112160000784882015871 := by
  unfold tailWord_2460339
  simp only [CollatzResearch.WordTrace]
  refine ⟨89735935433619470293080071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59823956955746313528720047 89735935433619470293080071)
  ·
    refine ⟨134603903150429205439620107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89735935433619470293080071 134603903150429205439620107)
    ·
      refine ⟨201905854725643808159430161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134603903150429205439620107 201905854725643808159430161)
      ·
        refine ⟨151429391044232856119572621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201905854725643808159430161 151429391044232856119572621)
        ·
          refine ⟨56786021641587321044839733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151429391044232856119572621 56786021641587321044839733)
          ·
            refine ⟨5323689528898811347953725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56786021641587321044839733 5323689528898811347953725)
            ·
              refine ⟨1996383573337054255482647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5323689528898811347953725 1996383573337054255482647)
              ·
                refine ⟨2994575360005581383223971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1996383573337054255482647 2994575360005581383223971)
                ·
                  refine ⟨4491863040008372074835957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2994575360005581383223971 4491863040008372074835957)
                  ·
                    refine ⟨421112160000784882015871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4491863040008372074835957 421112160000784882015871)
                    ·
                      rfl

theorem cell23_2460339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 1, 5].length) (baseStart_2460339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460339 prefixEnd_2460339 := by exact prefixLift 2460339
  have htrace : WordTrace (prefixWord ++ tailWord_2460339) baseStart_2460339 baseEnd_2460339 := by
    simpa [prefixWord, tailWord_2460339, baseEnd_2460339] using wordTrace_append hprefix tailTrace_2460339
  have hstable : (prefixWord ++ tailWord_2460339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460339).length < 2 ^ (prefixWord ++ tailWord_2460339).sum := by decide
  have hdescent : baseEnd_2460339 < baseStart_2460339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460376 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 3, 2, 2]
def baseStart_2460376 : Nat := 118140960795 + 2460376 * 2 ^ 59
def prefixEnd_2460376 : Nat := 4983230072969 + 3 ^ 40 * 2460376 * 2
def baseEnd_2460376 : Nat := 1263355478786571001284943

theorem tailTrace_2460376 : CollatzResearch.WordTrace tailWord_2460376 prefixEnd_2460376 1263355478786571001284943 := by
  unfold tailWord_2460376
  simp only [CollatzResearch.WordTrace]
  refine ⟨44868642467242712806088491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59824856622990283741451321 44868642467242712806088491)
  ·
    refine ⟨67302963700864069209132737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44868642467242712806088491 67302963700864069209132737)
    ·
      refine ⟨50477222775648051906849553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67302963700864069209132737 50477222775648051906849553)
      ·
        refine ⟨37857917081736038930137165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50477222775648051906849553 37857917081736038930137165)
        ·
          refine ⟨14196718905651014598801437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37857917081736038930137165 14196718905651014598801437)
          ·
            refine ⟨5323769589619130474550539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14196718905651014598801437 5323769589619130474550539)
            ·
              refine ⟨7985654384428695711825809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5323769589619130474550539 7985654384428695711825809)
              ·
                refine ⟨5989240788321521783869357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7985654384428695711825809 5989240788321521783869357)
                ·
                  refine ⟨2245965295620570668951009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5989240788321521783869357 2245965295620570668951009)
                  ·
                    refine ⟨1684473971715428001713257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2245965295620570668951009 1684473971715428001713257)
                    ·
                      refine ⟨1263355478786571001284943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684473971715428001713257 1263355478786571001284943)
                      ·
                        rfl

theorem cell23_2460376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_2460376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460376 prefixEnd_2460376 := by exact prefixLift 2460376
  have htrace : WordTrace (prefixWord ++ tailWord_2460376) baseStart_2460376 baseEnd_2460376 := by
    simpa [prefixWord, tailWord_2460376, baseEnd_2460376] using wordTrace_append hprefix tailTrace_2460376
  have hstable : (prefixWord ++ tailWord_2460376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460376).length < 2 ^ (prefixWord ++ tailWord_2460376).sum := by decide
  have hdescent : baseEnd_2460376 < baseStart_2460376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460449 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 3, 4, 2]
def baseStart_2460449 : Nat := 118140960795 + 2460449 * 2 ^ 59
def prefixEnd_2460449 : Nat := 4983230072969 + 3 ^ 40 * 2460449 * 2
def baseEnd_2460449 : Nat := 1263392962874349215672107

theorem tailTrace_2460449 : CollatzResearch.WordTrace tailWord_2460449 prefixEnd_2460449 1263392962874349215672107 := by
  unfold tailWord_2460449
  simp only [CollatzResearch.WordTrace]
  refine ⟨89739947463220959079584401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59826631642147306053056267 89739947463220959079584401)
  ·
    refine ⟨67304960597415719309688301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89739947463220959079584401 67304960597415719309688301)
    ·
      refine ⟨25239360224030894741133113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67304960597415719309688301 25239360224030894741133113)
      ·
        refine ⟨18929520168023171055849835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25239360224030894741133113 18929520168023171055849835)
        ·
          refine ⟨28394280252034756583774753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18929520168023171055849835 28394280252034756583774753)
          ·
            refine ⟨21295710189026067437831065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28394280252034756583774753 21295710189026067437831065)
            ·
              refine ⟨15971782641769550578373299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21295710189026067437831065 15971782641769550578373299)
              ·
                refine ⟨23957673962654325867559949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15971782641769550578373299 23957673962654325867559949)
                ·
                  refine ⟨8984127735995372200334981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23957673962654325867559949 8984127735995372200334981)
                  ·
                    refine ⟨1684523950499132287562809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8984127735995372200334981 1684523950499132287562809)
                    ·
                      refine ⟨1263392962874349215672107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684523950499132287562809 1263392962874349215672107)
                      ·
                        rfl

theorem cell23_2460449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_2460449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460449 prefixEnd_2460449 := by exact prefixLift 2460449
  have htrace : WordTrace (prefixWord ++ tailWord_2460449) baseStart_2460449 baseEnd_2460449 := by
    simpa [prefixWord, tailWord_2460449, baseEnd_2460449] using wordTrace_append hprefix tailTrace_2460449
  have hstable : (prefixWord ++ tailWord_2460449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460449).length < 2 ^ (prefixWord ++ tailWord_2460449).sum := by decide
  have hdescent : baseEnd_2460449 < baseStart_2460449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460466 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2]
def baseStart_2460466 : Nat := 118140960795 + 2460466 * 2 ^ 59
def prefixEnd_2460466 : Nat := 4983230072969 + 3 ^ 40 * 2460466 * 2
def baseEnd_2460466 : Nat := 1263401692045475649159529

theorem tailTrace_2460466 : CollatzResearch.WordTrace tailWord_2460466 prefixEnd_2460466 1263401692045475649159529 := by
  unfold tailWord_2460466
  simp only [CollatzResearch.WordTrace]
  refine ⟨22435141876039842745738313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59827045002772913988635501 22435141876039842745738313)
  ·
    refine ⟨16826356407029882059303735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22435141876039842745738313 16826356407029882059303735)
    ·
      refine ⟨25239534610544823088955603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16826356407029882059303735 25239534610544823088955603)
      ·
        refine ⟨37859301915817234633433405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25239534610544823088955603 37859301915817234633433405)
        ·
          refine ⟨14197238218431462987537527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37859301915817234633433405 14197238218431462987537527)
          ·
            refine ⟨21295857327647194481306291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14197238218431462987537527 21295857327647194481306291)
            ·
              refine ⟨31943785991470791721959437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21295857327647194481306291 31943785991470791721959437)
              ·
                refine ⟨11978919746801546895734789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31943785991470791721959437 11978919746801546895734789)
                ·
                  refine ⟨2246047452525290042950273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11978919746801546895734789 2246047452525290042950273)
                  ·
                    refine ⟨1684535589393967532212705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2246047452525290042950273 1684535589393967532212705)
                    ·
                      refine ⟨1263401692045475649159529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684535589393967532212705 1263401692045475649159529)
                      ·
                        rfl

theorem cell23_2460466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_2460466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460466 prefixEnd_2460466 := by exact prefixLift 2460466
  have htrace : WordTrace (prefixWord ++ tailWord_2460466) baseStart_2460466 baseEnd_2460466 := by
    simpa [prefixWord, tailWord_2460466, baseEnd_2460466] using wordTrace_append hprefix tailTrace_2460466
  have hstable : (prefixWord ++ tailWord_2460466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460466).length < 2 ^ (prefixWord ++ tailWord_2460466).sum := by decide
  have hdescent : baseEnd_2460466 < baseStart_2460466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460477 : List Nat := [1, 4, 1, 4, 3, 1, 2, 1, 2, 1, 3]
def baseStart_2460477 : Nat := 118140960795 + 2460477 * 2 ^ 59
def prefixEnd_2460477 : Nat := 4983230072969 + 3 ^ 40 * 2460477 * 2
def baseEnd_2460477 : Nat := 1263407340332675106121979

theorem tailTrace_2460477 : CollatzResearch.WordTrace tailWord_2460477 prefixEnd_2460477 1263407340332675106121979 := by
  unfold tailWord_2460477
  simp only [CollatzResearch.WordTrace]
  refine ⟨89740968707119519861603685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59827312471413013241069123 89740968707119519861603685)
  ·
    refine ⟨16826431632584909974050691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89740968707119519861603685 16826431632584909974050691)
    ·
      refine ⟨25239647448877364961076037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16826431632584909974050691 25239647448877364961076037)
      ·
        refine ⟨4732433896664505930201757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25239647448877364961076037 4732433896664505930201757)
        ·
          refine ⟨1774662711249189723825659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4732433896664505930201757 1774662711249189723825659)
          ·
            refine ⟨2661994066873784585738489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774662711249189723825659 2661994066873784585738489)
            ·
              refine ⟨1996495550155338439303867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661994066873784585738489 1996495550155338439303867)
              ·
                refine ⟨2994743325233007658955801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1996495550155338439303867 2994743325233007658955801)
                ·
                  refine ⟨2246057493924755744216851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2994743325233007658955801 2246057493924755744216851)
                  ·
                    refine ⟨3369086240887133616325277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2246057493924755744216851 3369086240887133616325277)
                    ·
                      refine ⟨1263407340332675106121979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3369086240887133616325277 1263407340332675106121979)
                      ·
                        rfl

theorem cell23_2460477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_2460477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460477 prefixEnd_2460477 := by exact prefixLift 2460477
  have htrace : WordTrace (prefixWord ++ tailWord_2460477) baseStart_2460477 baseEnd_2460477 := by
    simpa [prefixWord, tailWord_2460477, baseEnd_2460477] using wordTrace_append hprefix tailTrace_2460477
  have hstable : (prefixWord ++ tailWord_2460477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460477).length < 2 ^ (prefixWord ++ tailWord_2460477).sum := by decide
  have hdescent : baseEnd_2460477 < baseStart_2460477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460512 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 5]
def baseStart_2460512 : Nat := 118140960795 + 2460512 * 2 ^ 59
def prefixEnd_2460512 : Nat := 4983230072969 + 3 ^ 40 * 2460512 * 2
def baseEnd_2460512 : Nat := 1263425312155582469184317

theorem tailTrace_2460512 : CollatzResearch.WordTrace tailWord_2460512 prefixEnd_2460512 1263425312155582469184317 := by
  unfold tailWord_2460512
  simp only [CollatzResearch.WordTrace]
  refine ⟨44871122630996360419563895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59828163507995147226085193 44871122630996360419563895)
  ·
    refine ⟨67306683946494540629345843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44871122630996360419563895 67306683946494540629345843)
    ·
      refine ⟨100960025919741810944018765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67306683946494540629345843 100960025919741810944018765)
      ·
        refine ⟨37860009719903179104007037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100960025919741810944018765 37860009719903179104007037)
        ·
          refine ⟨14197503644963692164002639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37860009719903179104007037 14197503644963692164002639)
          ·
            refine ⟨21296255467445538246003959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14197503644963692164002639 21296255467445538246003959)
            ·
              refine ⟨31944383201168307369005939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21296255467445538246003959 31944383201168307369005939)
              ·
                refine ⟨47916574801752461053508909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31944383201168307369005939 47916574801752461053508909)
                ·
                  refine ⟨17968715550657172895065841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47916574801752461053508909 17968715550657172895065841)
                  ·
                    refine ⟨13476536662992879671299381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17968715550657172895065841 13476536662992879671299381)
                    ·
                      refine ⟨1263425312155582469184317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13476536662992879671299381 1263425312155582469184317)
                      ·
                        rfl

theorem cell23_2460512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_2460512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460512 prefixEnd_2460512 := by exact prefixLift 2460512
  have htrace : WordTrace (prefixWord ++ tailWord_2460512) baseStart_2460512 baseEnd_2460512 := by
    simpa [prefixWord, tailWord_2460512, baseEnd_2460512] using wordTrace_append hprefix tailTrace_2460512
  have hstable : (prefixWord ++ tailWord_2460512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460512).length < 2 ^ (prefixWord ++ tailWord_2460512).sum := by decide
  have hdescent : baseEnd_2460512 < baseStart_2460512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460519 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 2, 5]
def baseStart_2460519 : Nat := 118140960795 + 2460519 * 2 ^ 59
def prefixEnd_2460519 : Nat := 4983230072969 + 3 ^ 40 * 2460519 * 2
def baseEnd_2460519 : Nat := 421142968840054647265595

theorem tailTrace_2460519 : CollatzResearch.WordTrace tailWord_2460519 prefixEnd_2460519 421142968840054647265595 := by
  unfold tailWord_2460519
  simp only [CollatzResearch.WordTrace]
  refine ⟨89742500572967361034632611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59828333715311574023088407 89742500572967361034632611)
  ·
    refine ⟨134613750859451041551948917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89742500572967361034632611 134613750859451041551948917)
    ·
      refine ⟨12620039143073535145495211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134613750859451041551948917 12620039143073535145495211)
      ·
        refine ⟨18930058714610302718242817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12620039143073535145495211 18930058714610302718242817)
        ·
          refine ⟨14197544035957727038682113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18930058714610302718242817 14197544035957727038682113)
          ·
            refine ⟨10648158026968295279011585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14197544035957727038682113 10648158026968295279011585)
            ·
              refine ⟨7986118520226221459258689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10648158026968295279011585 7986118520226221459258689)
              ·
                refine ⟨5989588890169666094444017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7986118520226221459258689 5989588890169666094444017)
                ·
                  refine ⟨4492191667627249570833013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5989588890169666094444017 4492191667627249570833013)
                  ·
                    refine ⟨421142968840054647265595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4492191667627249570833013 421142968840054647265595)
                    ·
                      rfl

theorem cell23_2460519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_2460519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460519 prefixEnd_2460519 := by exact prefixLift 2460519
  have htrace : WordTrace (prefixWord ++ tailWord_2460519) baseStart_2460519 baseEnd_2460519 := by
    simpa [prefixWord, tailWord_2460519, baseEnd_2460519] using wordTrace_append hprefix tailTrace_2460519
  have hstable : (prefixWord ++ tailWord_2460519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460519).length < 2 ^ (prefixWord ++ tailWord_2460519).sum := by decide
  have hdescent : baseEnd_2460519 < baseStart_2460519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460539 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 1, 6, 2]
def baseStart_2460539 : Nat := 118140960795 + 2460539 * 2 ^ 59
def prefixEnd_2460539 : Nat := 4983230072969 + 3 ^ 40 * 2460539 * 2
def baseEnd_2460539 : Nat := 1263439176133253863546693

theorem tailTrace_2460539 : CollatzResearch.WordTrace tailWord_2460539 prefixEnd_2460539 1263439176133253863546693 := by
  unfold tailWord_2460539
  simp only [CollatzResearch.WordTrace]
  refine ⟨89743230032894904450360671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59828820021929936300240447 89743230032894904450360671)
  ·
    refine ⟨134614845049342356675541007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89743230032894904450360671 134614845049342356675541007)
    ·
      refine ⟨201922267574013535013311511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134614845049342356675541007 201922267574013535013311511)
      ·
        refine ⟨302883401361020302519967267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201922267574013535013311511 302883401361020302519967267)
        ·
          refine ⟨454325102041530453779950901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302883401361020302519967267 454325102041530453779950901)
          ·
            refine ⟨42592978316393480041870397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 454325102041530453779950901 42592978316393480041870397)
            ·
              refine ⟨15972366868647555015701399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42592978316393480041870397 15972366868647555015701399)
              ·
                refine ⟨23958550302971332523552099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15972366868647555015701399 23958550302971332523552099)
                ·
                  refine ⟨35937825454456998785328149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23958550302971332523552099 35937825454456998785328149)
                  ·
                    refine ⟨1684585568177671818062257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35937825454456998785328149 1684585568177671818062257)
                    ·
                      refine ⟨1263439176133253863546693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684585568177671818062257 1263439176133253863546693)
                      ·
                        rfl

theorem cell23_2460539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 6, 2].length) (baseStart_2460539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460539 prefixEnd_2460539 := by exact prefixLift 2460539
  have htrace : WordTrace (prefixWord ++ tailWord_2460539) baseStart_2460539 baseEnd_2460539 := by
    simpa [prefixWord, tailWord_2460539, baseEnd_2460539] using wordTrace_append hprefix tailTrace_2460539
  have hstable : (prefixWord ++ tailWord_2460539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460539).length < 2 ^ (prefixWord ++ tailWord_2460539).sum := by decide
  have hdescent : baseEnd_2460539 < baseStart_2460539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460549 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 5, 4]
def baseStart_2460549 : Nat := 118140960795 + 2460549 * 2 ^ 59
def prefixEnd_2460549 : Nat := 4983230072969 + 3 ^ 40 * 2460549 * 2
def baseEnd_2460549 : Nat := 421148103646599608140549

theorem tailTrace_2460549 : CollatzResearch.WordTrace tailWord_2460549 prefixEnd_2460549 421148103646599608140549 := by
  unfold tailWord_2460549
  simp only [CollatzResearch.WordTrace]
  refine ⟨89743594762858676158224701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59829063175239117438816467 89743594762858676158224701)
  ·
    refine ⟨33653848036072003559334263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89743594762858676158224701 33653848036072003559334263)
    ·
      refine ⟨50480772054108005339001395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33653848036072003559334263 50480772054108005339001395)
      ·
        refine ⟨75721158081162008008502093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50480772054108005339001395 75721158081162008008502093)
        ·
          refine ⟨28395434280435753003188285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75721158081162008008502093 28395434280435753003188285)
          ·
            refine ⟨10648287855163407376195607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28395434280435753003188285 10648287855163407376195607)
            ·
              refine ⟨15972431782745111064293411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10648287855163407376195607 15972431782745111064293411)
              ·
                refine ⟨23958647674117666596440117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15972431782745111064293411 23958647674117666596440117)
                ·
                  refine ⟨2246123219448531243416261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23958647674117666596440117 2246123219448531243416261)
                  ·
                    refine ⟨421148103646599608140549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2246123219448531243416261 421148103646599608140549)
                    ·
                      rfl

theorem cell23_2460549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_2460549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460549 prefixEnd_2460549 := by exact prefixLift 2460549
  have htrace : WordTrace (prefixWord ++ tailWord_2460549) baseStart_2460549 baseEnd_2460549 := by
    simpa [prefixWord, tailWord_2460549, baseEnd_2460549] using wordTrace_append hprefix tailTrace_2460549
  have hstable : (prefixWord ++ tailWord_2460549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460549).length < 2 ^ (prefixWord ++ tailWord_2460549).sum := by decide
  have hdescent : baseEnd_2460549 < baseStart_2460549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460579 : List Nat := [1, 1, 1, 4, 1, 2, 5, 2, 6]
def baseStart_2460579 : Nat := 118140960795 + 2460579 * 2 ^ 59
def prefixEnd_2460579 : Nat := 4983230072969 + 3 ^ 40 * 2460579 * 2
def baseEnd_2460579 : Nat := 140384412817714856338501

theorem tailTrace_2460579 : CollatzResearch.WordTrace tailWord_2460579 prefixEnd_2460579 140384412817714856338501 := by
  unfold tailWord_2460579
  simp only [CollatzResearch.WordTrace]
  refine ⟨89744688952749991281816791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59829792635166660854544527 89744688952749991281816791)
  ·
    refine ⟨134617033429124986922725187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89744688952749991281816791 134617033429124986922725187)
    ·
      refine ⟨201925550143687480384087781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134617033429124986922725187 201925550143687480384087781)
      ·
        refine ⟨37861040651941402572016459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201925550143687480384087781 37861040651941402572016459)
        ·
          refine ⟨56791560977912103858024689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37861040651941402572016459 56791560977912103858024689)
          ·
            refine ⟨42593670733434077893518517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56791560977912103858024689 42593670733434077893518517)
            ·
              refine ⟨3993156631259444802517361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42593670733434077893518517 3993156631259444802517361)
              ·
                refine ⟨2994867473444583601888021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3993156631259444802517361 2994867473444583601888021)
                ·
                  refine ⟨140384412817714856338501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2994867473444583601888021 140384412817714856338501)
                  ·
                    rfl

theorem cell23_2460579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 6].length) (baseStart_2460579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460579 prefixEnd_2460579 := by exact prefixLift 2460579
  have htrace : WordTrace (prefixWord ++ tailWord_2460579) baseStart_2460579 baseEnd_2460579 := by
    simpa [prefixWord, tailWord_2460579, baseEnd_2460579] using wordTrace_append hprefix tailTrace_2460579
  have hstable : (prefixWord ++ tailWord_2460579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460579).length < 2 ^ (prefixWord ++ tailWord_2460579).sum := by decide
  have hdescent : baseEnd_2460579 < baseStart_2460579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460583 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 3, 4]
def baseStart_2460583 : Nat := 118140960795 + 2460583 * 2 ^ 59
def prefixEnd_2460583 : Nat := 4983230072969 + 3 ^ 40 * 2460583 * 2
def baseEnd_2460583 : Nat := 421153923094017230465497

theorem tailTrace_2460583 : CollatzResearch.WordTrace tailWord_2460583 prefixEnd_2460583 421153923094017230465497 := by
  unfold tailWord_2460583
  simp only [CollatzResearch.WordTrace]
  refine ⟨89744834844735499964962403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59829889896490333309974935 89744834844735499964962403)
  ·
    refine ⟨134617252267103249947443605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89744834844735499964962403 134617252267103249947443605)
    ·
      refine ⟨6310183700020464841286419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 134617252267103249947443605 6310183700020464841286419)
      ·
        refine ⟨9465275550030697261929629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6310183700020464841286419 9465275550030697261929629)
        ·
          refine ⟨3549478331261511473223611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9465275550030697261929629 3549478331261511473223611)
          ·
            refine ⟨5324217496892267209835417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3549478331261511473223611 5324217496892267209835417)
            ·
              refine ⟨3993163122669200407376563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5324217496892267209835417 3993163122669200407376563)
              ·
                refine ⟨5989744684003800611064845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3993163122669200407376563 5989744684003800611064845)
                ·
                  refine ⟨2246154256501425229149317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5989744684003800611064845 2246154256501425229149317)
                  ·
                    refine ⟨421153923094017230465497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2246154256501425229149317 421153923094017230465497)
                    ·
                      rfl

theorem cell23_2460583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_2460583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460583 prefixEnd_2460583 := by exact prefixLift 2460583
  have htrace : WordTrace (prefixWord ++ tailWord_2460583) baseStart_2460583 baseEnd_2460583 := by
    simpa [prefixWord, tailWord_2460583, baseEnd_2460583] using wordTrace_append hprefix tailTrace_2460583
  have hstable : (prefixWord ++ tailWord_2460583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460583).length < 2 ^ (prefixWord ++ tailWord_2460583).sum := by decide
  have hdescent : baseEnd_2460583 < baseStart_2460583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460633 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 2, 3, 2]
def baseStart_2460633 : Nat := 118140960795 + 2460633 * 2 ^ 59
def prefixEnd_2460633 : Nat := 4983230072969 + 3 ^ 40 * 2460633 * 2
def baseEnd_2460633 : Nat := 1263487443314776495771261

theorem tailTrace_2460633 : CollatzResearch.WordTrace tailWord_2460633 prefixEnd_2460633 1263487443314776495771261 := by
  unfold tailWord_2460633
  simp only [CollatzResearch.WordTrace]
  refine ⟨89746658494554358504282553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59831105663036239002855035 89746658494554358504282553)
  ·
    refine ⟨67309993870915768878211915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89746658494554358504282553 67309993870915768878211915)
    ·
      refine ⟨100964990806373653317317873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67309993870915768878211915 100964990806373653317317873)
      ·
        refine ⟨75723743104780239987988405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100964990806373653317317873 75723743104780239987988405)
        ·
          refine ⟨7099100916073147498873913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75723743104780239987988405 7099100916073147498873913)
          ·
            refine ⟨5324325687054860624155435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7099100916073147498873913 5324325687054860624155435)
            ·
              refine ⟨7986488530582290936233153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5324325687054860624155435 7986488530582290936233153)
              ·
                refine ⟨5989866397936718202174865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7986488530582290936233153 5989866397936718202174865)
                ·
                  refine ⟨4492399798452538651631149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5989866397936718202174865 4492399798452538651631149)
                  ·
                    refine ⟨1684649924419701994361681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4492399798452538651631149 1684649924419701994361681)
                    ·
                      refine ⟨1263487443314776495771261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684649924419701994361681 1263487443314776495771261)
                      ·
                        rfl

theorem cell23_2460633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 3, 2].length) (baseStart_2460633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460633 prefixEnd_2460633 := by exact prefixLift 2460633
  have htrace : WordTrace (prefixWord ++ tailWord_2460633) baseStart_2460633 baseEnd_2460633 := by
    simpa [prefixWord, tailWord_2460633, baseEnd_2460633] using wordTrace_append hprefix tailTrace_2460633
  have hstable : (prefixWord ++ tailWord_2460633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460633).length < 2 ^ (prefixWord ++ tailWord_2460633).sum := by decide
  have hdescent : baseEnd_2460633 < baseStart_2460633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460697 : List Nat := [1, 2, 1, 2, 1, 1, 8, 2, 1, 2, 2]
def baseStart_2460697 : Nat := 118140960795 + 2460697 * 2 ^ 59
def prefixEnd_2460697 : Nat := 4983230072969 + 3 ^ 40 * 2460697 * 2
def baseEnd_2460697 : Nat := 1263520306076664245370967

theorem tailTrace_2460697 : CollatzResearch.WordTrace tailWord_2460697 prefixEnd_2460697 1263520306076664245370967 := by
  unfold tailWord_2460697
  simp only [CollatzResearch.WordTrace]
  refine ⟨89748992766322497434612345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59832661844214998289741563 89748992766322497434612345)
  ·
    refine ⟨67311744574741873075959259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89748992766322497434612345 67311744574741873075959259)
    ·
      refine ⟨100967616862112809613938889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67311744574741873075959259 100967616862112809613938889)
      ·
        refine ⟨75725712646584607210454167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100967616862112809613938889 75725712646584607210454167)
        ·
          refine ⟨113588568969876910815681251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75725712646584607210454167 113588568969876910815681251)
          ·
            refine ⟨170382853454815366223521877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113588568969876910815681251 170382853454815366223521877)
            ·
              refine ⟨1996674063923617572931897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 170382853454815366223521877 1996674063923617572931897)
              ·
                refine ⟨1497505547942713179698923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1996674063923617572931897 1497505547942713179698923)
                ·
                  refine ⟨2246258321914069769548385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497505547942713179698923 2246258321914069769548385)
                  ·
                    refine ⟨1684693741435552327161289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2246258321914069769548385 1684693741435552327161289)
                    ·
                      refine ⟨1263520306076664245370967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684693741435552327161289 1263520306076664245370967)
                      ·
                        rfl

theorem cell23_2460697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 1, 2, 2].length) (baseStart_2460697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460697 prefixEnd_2460697 := by exact prefixLift 2460697
  have htrace : WordTrace (prefixWord ++ tailWord_2460697) baseStart_2460697 baseEnd_2460697 := by
    simpa [prefixWord, tailWord_2460697, baseEnd_2460697] using wordTrace_append hprefix tailTrace_2460697
  have hstable : (prefixWord ++ tailWord_2460697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460697).length < 2 ^ (prefixWord ++ tailWord_2460697).sum := by decide
  have hdescent : baseEnd_2460697 < baseStart_2460697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460723 : List Nat := [1, 1, 1, 2, 4, 1, 1, 6, 1, 3, 2]
def baseStart_2460723 : Nat := 118140960795 + 2460723 * 2 ^ 59
def prefixEnd_2460723 : Nat := 4983230072969 + 3 ^ 40 * 2460723 * 2
def baseEnd_2460723 : Nat := 1263533656573681143645847

theorem tailTrace_2460723 : CollatzResearch.WordTrace tailWord_2460723 prefixEnd_2460723 1263533656573681143645847 := by
  unfold tailWord_2460723
  simp only [CollatzResearch.WordTrace]
  refine ⟨89749941064228303875058823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59833294042818869250039215 89749941064228303875058823)
  ·
    refine ⟨134624911596342455812588235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89749941064228303875058823 134624911596342455812588235)
    ·
      refine ⟨201937367394513683718882353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134624911596342455812588235 201937367394513683718882353)
      ·
        refine ⟨151453025545885262789161765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201937367394513683718882353 151453025545885262789161765)
        ·
          refine ⟨28397442289853486772967831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151453025545885262789161765 28397442289853486772967831)
          ·
            refine ⟨42596163434780230159451747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28397442289853486772967831 42596163434780230159451747)
            ·
              refine ⟨63894245152170345239177621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42596163434780230159451747 63894245152170345239177621)
              ·
                refine ⟨2995042741507984933086451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63894245152170345239177621 2995042741507984933086451)
                ·
                  refine ⟨4492564112261977399629677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2995042741507984933086451 4492564112261977399629677)
                  ·
                    refine ⟨1684711542098241524861129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4492564112261977399629677 1684711542098241524861129)
                    ·
                      refine ⟨1263533656573681143645847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684711542098241524861129 1263533656573681143645847)
                      ·
                        rfl

theorem cell23_2460723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 3, 2].length) (baseStart_2460723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460723 prefixEnd_2460723 := by exact prefixLift 2460723
  have htrace : WordTrace (prefixWord ++ tailWord_2460723) baseStart_2460723 baseEnd_2460723 := by
    simpa [prefixWord, tailWord_2460723, baseEnd_2460723] using wordTrace_append hprefix tailTrace_2460723
  have hstable : (prefixWord ++ tailWord_2460723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460723).length < 2 ^ (prefixWord ++ tailWord_2460723).sum := by decide
  have hdescent : baseEnd_2460723 < baseStart_2460723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460739 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 5]
def baseStart_2460739 : Nat := 118140960795 + 2460739 * 2 ^ 59
def prefixEnd_2460739 : Nat := 4983230072969 + 3 ^ 40 * 2460739 * 2
def baseEnd_2460739 : Nat := 1263541872264153081045773

theorem tailTrace_2460739 : CollatzResearch.WordTrace tailWord_2460739 prefixEnd_2460739 1263541872264153081045773 := by
  unfold tailWord_2460739
  simp only [CollatzResearch.WordTrace]
  refine ⟨89750524632170338607641271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59833683088113559071760847 89750524632170338607641271)
  ·
    refine ⟨134625786948255507911461907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89750524632170338607641271 134625786948255507911461907)
    ·
      refine ⟨201938680422383261867192861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134625786948255507911461907 201938680422383261867192861)
      ·
        refine ⟨75727005158393723200197323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201938680422383261867192861 75727005158393723200197323)
        ·
          refine ⟨113590507737590584800295985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75727005158393723200197323 113590507737590584800295985)
          ·
            refine ⟨85192880803192938600221989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113590507737590584800295985 85192880803192938600221989)
            ·
              refine ⟨15973665150598675987541623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85192880803192938600221989 15973665150598675987541623)
              ·
                refine ⟨23960497725898013981312435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15973665150598675987541623 23960497725898013981312435)
                ·
                  refine ⟨35940746588847020971968653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23960497725898013981312435 35940746588847020971968653)
                  ·
                    refine ⟨13477779970817632864488245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35940746588847020971968653 13477779970817632864488245)
                    ·
                      refine ⟨1263541872264153081045773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13477779970817632864488245 1263541872264153081045773)
                      ·
                        rfl

theorem cell23_2460739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_2460739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460739 prefixEnd_2460739 := by exact prefixLift 2460739
  have htrace : WordTrace (prefixWord ++ tailWord_2460739) baseStart_2460739 baseEnd_2460739 := by
    simpa [prefixWord, tailWord_2460739, baseEnd_2460739] using wordTrace_append hprefix tailTrace_2460739
  have hstable : (prefixWord ++ tailWord_2460739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460739).length < 2 ^ (prefixWord ++ tailWord_2460739).sum := by decide
  have hdescent : baseEnd_2460739 < baseStart_2460739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460756 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_2460756 : Nat := 118140960795 + 2460756 * 2 ^ 59
def prefixEnd_2460756 : Nat := 4983230072969 + 3 ^ 40 * 2460756 * 2
def baseEnd_2460756 : Nat := 1263550601435279514533195

theorem tailTrace_2460756 : CollatzResearch.WordTrace tailWord_2460756 prefixEnd_2460756 1263550601435279514533195 := by
  unfold tailWord_2460756
  simp only [CollatzResearch.WordTrace]
  refine ⟨44875572336554375255505061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59834096448739167007340081 44875572336554375255505061)
  ·
    refine ⟨8414169813103945360407199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44875572336554375255505061 8414169813103945360407199)
    ·
      refine ⟨12621254719655918040610799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8414169813103945360407199 12621254719655918040610799)
      ·
        refine ⟨18931882079483877060916199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12621254719655918040610799 18931882079483877060916199)
        ·
          refine ⟨28397823119225815591374299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18931882079483877060916199 28397823119225815591374299)
          ·
            refine ⟨42596734678838723387061449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28397823119225815591374299 42596734678838723387061449)
            ·
              refine ⟨31947551009129042540296087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42596734678838723387061449 31947551009129042540296087)
              ·
                refine ⟨47921326513693563810444131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31947551009129042540296087 47921326513693563810444131)
                ·
                  refine ⟨71881989770540345715666197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47921326513693563810444131 71881989770540345715666197)
                  ·
                    refine ⟨3369468270494078705421853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71881989770540345715666197 3369468270494078705421853)
                    ·
                      refine ⟨1263550601435279514533195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3369468270494078705421853 1263550601435279514533195)
                      ·
                        rfl

theorem cell23_2460756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_2460756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460756 prefixEnd_2460756 := by exact prefixLift 2460756
  have htrace : WordTrace (prefixWord ++ tailWord_2460756) baseStart_2460756 baseEnd_2460756 := by
    simpa [prefixWord, tailWord_2460756, baseEnd_2460756] using wordTrace_append hprefix tailTrace_2460756
  have hstable : (prefixWord ++ tailWord_2460756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460756).length < 2 ^ (prefixWord ++ tailWord_2460756).sum := by decide
  have hdescent : baseEnd_2460756 < baseStart_2460756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460799 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 7]
def baseStart_2460799 : Nat := 118140960795 + 2460799 * 2 ^ 59
def prefixEnd_2460799 : Nat := 4983230072969 + 3 ^ 40 * 2460799 * 2
def baseEnd_2460799 : Nat := 1263572681103422846295497

theorem tailTrace_2460799 : CollatzResearch.WordTrace tailWord_2460799 prefixEnd_2460799 1263572681103422846295497 := by
  unfold tailWord_2460799
  simp only [CollatzResearch.WordTrace]
  refine ⟨89752713011952968854825451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59835142007968645903216967 89752713011952968854825451)
  ·
    refine ⟨134629069517929453282238177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89752713011952968854825451 134629069517929453282238177)
    ·
      refine ⟨100971802138447089961678633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134629069517929453282238177 100971802138447089961678633)
      ·
        refine ⟨75728851603835317471258975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100971802138447089961678633 75728851603835317471258975)
        ·
          refine ⟨113593277405752976206888463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75728851603835317471258975 113593277405752976206888463)
          ·
            refine ⟨170389916108629464310332695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113593277405752976206888463 170389916108629464310332695)
            ·
              refine ⟨255584874162944196465499043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170389916108629464310332695 255584874162944196465499043)
              ·
                refine ⟨383377311244416294698248565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255584874162944196465499043 383377311244416294698248565)
                ·
                  refine ⟨35941622929164027627960803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 383377311244416294698248565 35941622929164027627960803)
                  ·
                    refine ⟨53912434393746041441941205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35941622929164027627960803 53912434393746041441941205)
                    ·
                      refine ⟨1263572681103422846295497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53912434393746041441941205 1263572681103422846295497)
                      ·
                        rfl

theorem cell23_2460799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_2460799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460799 prefixEnd_2460799 := by exact prefixLift 2460799
  have htrace : WordTrace (prefixWord ++ tailWord_2460799) baseStart_2460799 baseEnd_2460799 := by
    simpa [prefixWord, tailWord_2460799, baseEnd_2460799] using wordTrace_append hprefix tailTrace_2460799
  have hstable : (prefixWord ++ tailWord_2460799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460799).length < 2 ^ (prefixWord ++ tailWord_2460799).sum := by decide
  have hdescent : baseEnd_2460799 < baseStart_2460799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460810 : List Nat := [3, 1, 2, 3, 1, 1, 5, 2, 5]
def baseStart_2460810 : Nat := 118140960795 + 2460810 * 2 ^ 59
def prefixEnd_2460810 : Nat := 4983230072969 + 3 ^ 40 * 2460810 * 2
def baseEnd_2460810 : Nat := 140397592154513589250883

theorem tailTrace_2460810 : CollatzResearch.WordTrace tailWord_2460810 prefixEnd_2460810 140397592154513589250883 := by
  unfold tailWord_2460810
  simp only [CollatzResearch.WordTrace]
  refine ⟨22438278553728279433368971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59835409476608745155650589 22438278553728279433368971)
  ·
    refine ⟨33657417830592419150053457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22438278553728279433368971 33657417830592419150053457)
    ·
      refine ⟨25243063372944314362540093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33657417830592419150053457 25243063372944314362540093)
      ·
        refine ⟨9466148764854117885952535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25243063372944314362540093 9466148764854117885952535)
        ·
          refine ⟨14199223147281176828928803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9466148764854117885952535 14199223147281176828928803)
          ·
            refine ⟨21298834720921765243393205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14199223147281176828928803 21298834720921765243393205)
            ·
              refine ⟨1996765755086415491568113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21298834720921765243393205 1996765755086415491568113)
              ·
                refine ⟨1497574316314811618676085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1996765755086415491568113 1497574316314811618676085)
                ·
                  refine ⟨140397592154513589250883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1497574316314811618676085 140397592154513589250883)
                  ·
                    rfl

theorem cell23_2460810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 5].length) (baseStart_2460810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460810 prefixEnd_2460810 := by exact prefixLift 2460810
  have htrace : WordTrace (prefixWord ++ tailWord_2460810) baseStart_2460810 baseEnd_2460810 := by
    simpa [prefixWord, tailWord_2460810, baseEnd_2460810] using wordTrace_append hprefix tailTrace_2460810
  have hstable : (prefixWord ++ tailWord_2460810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460810).length < 2 ^ (prefixWord ++ tailWord_2460810).sum := by decide
  have hdescent : baseEnd_2460810 < baseStart_2460810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460863 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 3]
def baseStart_2460863 : Nat := 118140960795 + 2460863 * 2 ^ 59
def prefixEnd_2460863 : Nat := 4983230072969 + 3 ^ 40 * 2460863 * 2
def baseEnd_2460863 : Nat := 1263605543865310595895203

theorem tailTrace_2460863 : CollatzResearch.WordTrace tailWord_2460863 prefixEnd_2460863 1263605543865310595895203 := by
  unfold tailWord_2460863
  simp only [CollatzResearch.WordTrace]
  refine ⟨89755047283721107785155243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59836698189147405190103495 89755047283721107785155243)
  ·
    refine ⟨134632570925581661677732865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89755047283721107785155243 134632570925581661677732865)
    ·
      refine ⟨100974428194186246258299649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134632570925581661677732865 100974428194186246258299649)
      ·
        refine ⟨75730821145639684693724737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100974428194186246258299649 75730821145639684693724737)
        ·
          refine ⟨56798115859229763520293553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75730821145639684693724737 56798115859229763520293553)
          ·
            refine ⟨42598586894422322640220165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56798115859229763520293553 42598586894422322640220165)
            ·
              refine ⟨7987235042704185495041281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42598586894422322640220165 7987235042704185495041281)
              ·
                refine ⟨5990426282028139121280961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7987235042704185495041281 5990426282028139121280961)
                ·
                  refine ⟨4492819711521104340960721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5990426282028139121280961 4492819711521104340960721)
                  ·
                    refine ⟨3369614783640828255720541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4492819711521104340960721 3369614783640828255720541)
                    ·
                      refine ⟨1263605543865310595895203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3369614783640828255720541 1263605543865310595895203)
                      ·
                        rfl

theorem cell23_2460863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_2460863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460863 prefixEnd_2460863 := by exact prefixLift 2460863
  have htrace : WordTrace (prefixWord ++ tailWord_2460863) baseStart_2460863 baseEnd_2460863 := by
    simpa [prefixWord, tailWord_2460863, baseEnd_2460863] using wordTrace_append hprefix tailTrace_2460863
  have hstable : (prefixWord ++ tailWord_2460863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460863).length < 2 ^ (prefixWord ++ tailWord_2460863).sum := by decide
  have hdescent : baseEnd_2460863 < baseStart_2460863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460927 : List Nat := [1, 1, 2, 2, 1, 5, 2, 4, 1, 1, 3]
def baseStart_2460927 : Nat := 118140960795 + 2460927 * 2 ^ 59
def prefixEnd_2460927 : Nat := 4983230072969 + 3 ^ 40 * 2460927 * 2
def baseEnd_2460927 : Nat := 1263638406627198345494909

theorem tailTrace_2460927 : CollatzResearch.WordTrace tailWord_2460927 prefixEnd_2460927 1263638406627198345494909 := by
  unfold tailWord_2460927
  simp only [CollatzResearch.WordTrace]
  refine ⟨89757381555489246715485035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59838254370326164476990023 89757381555489246715485035)
  ·
    refine ⟨134636072333233870073227553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89757381555489246715485035 134636072333233870073227553)
    ·
      refine ⟨100977054249925402554920665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134636072333233870073227553 100977054249925402554920665)
      ·
        refine ⟨75732790687444051916190499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100977054249925402554920665 75732790687444051916190499)
        ·
          refine ⟨113599186031166077874285749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75732790687444051916190499 113599186031166077874285749)
          ·
            refine ⟨10649923690421819800714289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113599186031166077874285749 10649923690421819800714289)
            ·
              refine ⟨7987442767816364850535717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10649923690421819800714289 7987442767816364850535717)
              ·
                refine ⟨1497645518965568409475447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7987442767816364850535717 1497645518965568409475447)
                ·
                  refine ⟨2246468278448352614213171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497645518965568409475447 2246468278448352614213171)
                  ·
                    refine ⟨3369702417672528921319757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2246468278448352614213171 3369702417672528921319757)
                    ·
                      refine ⟨1263638406627198345494909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3369702417672528921319757 1263638406627198345494909)
                      ·
                        rfl

theorem cell23_2460927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 1, 1, 3].length) (baseStart_2460927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460927 prefixEnd_2460927 := by exact prefixLift 2460927
  have htrace : WordTrace (prefixWord ++ tailWord_2460927) baseStart_2460927 baseEnd_2460927 := by
    simpa [prefixWord, tailWord_2460927, baseEnd_2460927] using wordTrace_append hprefix tailTrace_2460927
  have hstable : (prefixWord ++ tailWord_2460927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460927).length < 2 ^ (prefixWord ++ tailWord_2460927).sum := by decide
  have hdescent : baseEnd_2460927 < baseStart_2460927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460970 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2460970 : Nat := 118140960795 + 2460970 * 2 ^ 59
def prefixEnd_2460970 : Nat := 4983230072969 + 3 ^ 40 * 2460970 * 2
def baseEnd_2460970 : Nat := 1263660486295341677257211

theorem tailTrace_2460970 : CollatzResearch.WordTrace tailWord_2460970 prefixEnd_2460970 1263660486295341677257211 := by
  unfold tailWord_2460970
  simp only [CollatzResearch.WordTrace]
  refine ⟨22439737473583366264825091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59839299929555643372866909 22439737473583366264825091)
  ·
    refine ⟨33659606210375049397237637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22439737473583366264825091 33659606210375049397237637)
    ·
      refine ⟨6311176164445321761982057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33659606210375049397237637 6311176164445321761982057)
      ·
        refine ⟨4733382123333991321486543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6311176164445321761982057 4733382123333991321486543)
        ·
          refine ⟨7100073185000986982229815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4733382123333991321486543 7100073185000986982229815)
          ·
            refine ⟨10650109777501480473344723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7100073185000986982229815 10650109777501480473344723)
            ·
              refine ⟨15975164666252220710017085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10650109777501480473344723 15975164666252220710017085)
              ·
                refine ⟨5990686749844582766256407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15975164666252220710017085 5990686749844582766256407)
                ·
                  refine ⟨8986030124766874149384611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5990686749844582766256407 8986030124766874149384611)
                  ·
                    refine ⟨13479045187150311224076917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8986030124766874149384611 13479045187150311224076917)
                    ·
                      refine ⟨1263660486295341677257211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13479045187150311224076917 1263660486295341677257211)
                      ·
                        rfl

theorem cell23_2460970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2460970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460970 prefixEnd_2460970 := by exact prefixLift 2460970
  have htrace : WordTrace (prefixWord ++ tailWord_2460970) baseStart_2460970 baseEnd_2460970 := by
    simpa [prefixWord, tailWord_2460970, baseEnd_2460970] using wordTrace_append hprefix tailTrace_2460970
  have hstable : (prefixWord ++ tailWord_2460970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460970).length < 2 ^ (prefixWord ++ tailWord_2460970).sum := by decide
  have hdescent : baseEnd_2460970 < baseStart_2460970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460998 : List Nat := [6, 1, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_2460998 : Nat := 118140960795 + 2460998 * 2 ^ 59
def prefixEnd_2460998 : Nat := 4983230072969 + 3 ^ 40 * 2460998 * 2
def baseEnd_2460998 : Nat := 421224954584555855902361

theorem tailTrace_2460998 : CollatzResearch.WordTrace tailWord_2460998 prefixEnd_2460998 421224954584555855902361 := by
  unfold tailWord_2460998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2804999098069750807541239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59839980758821350560879765 2804999098069750807541239)
  ·
    refine ⟨4207498647104626211311859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2804999098069750807541239 4207498647104626211311859)
    ·
      refine ⟨6311247970656939316967789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4207498647104626211311859 6311247970656939316967789)
      ·
        refine ⟨2366717988996352243862921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6311247970656939316967789 2366717988996352243862921)
        ·
          refine ⟨1775038491747264182897191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2366717988996352243862921 1775038491747264182897191)
          ·
            refine ⟨2662557737620896274345787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775038491747264182897191 2662557737620896274345787)
            ·
              refine ⟨3993836606431344411518681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2662557737620896274345787 3993836606431344411518681)
              ·
                refine ⟨2995377454823508308639011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3993836606431344411518681 2995377454823508308639011)
                ·
                  refine ⟨4493066182235262462958517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2995377454823508308639011 4493066182235262462958517)
                  ·
                    refine ⟨421224954584555855902361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4493066182235262462958517 421224954584555855902361)
                    ·
                      rfl

theorem cell23_2460998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_2460998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2460998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2460998 prefixEnd_2460998 := by exact prefixLift 2460998
  have htrace : WordTrace (prefixWord ++ tailWord_2460998) baseStart_2460998 baseEnd_2460998 := by
    simpa [prefixWord, tailWord_2460998, baseEnd_2460998] using wordTrace_append hprefix tailTrace_2460998
  have hstable : (prefixWord ++ tailWord_2460998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460998).length < 2 ^ (prefixWord ++ tailWord_2460998).sum := by decide
  have hdescent : baseEnd_2460998 < baseStart_2460998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461021 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2461021 : Nat := 118140960795 + 2461021 * 2 ^ 59
def prefixEnd_2461021 : Nat := 4983230072969 + 3 ^ 40 * 2461021 * 2
def baseEnd_2461021 : Nat := 1263686673808720977719477

theorem tailTrace_2461021 : CollatzResearch.WordTrace tailWord_2461021 prefixEnd_2461021 1263686673808720977719477 := by
  unfold tailWord_2461021
  simp only [CollatzResearch.WordTrace]
  refine ⟨89760810017148700769406917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59840540011432467179604611 89760810017148700769406917)
  ·
    refine ⟨16830151878215381394263797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89760810017148700769406917 16830151878215381394263797)
    ·
      refine ⟨1577826738582692005712231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16830151878215381394263797 1577826738582692005712231)
      ·
        refine ⟨2366740107874038008568347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577826738582692005712231 2366740107874038008568347)
        ·
          refine ⟨3550110161811057012852521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2366740107874038008568347 3550110161811057012852521)
          ·
            refine ⟨2662582621358292759639391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3550110161811057012852521 2662582621358292759639391)
            ·
              refine ⟨3993873932037439139459087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2662582621358292759639391 3993873932037439139459087)
              ·
                refine ⟨5990810898056158709188631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3993873932037439139459087 5990810898056158709188631)
                ·
                  refine ⟨8986216347084238063782947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5990810898056158709188631 8986216347084238063782947)
                  ·
                    refine ⟨13479324520626357095674421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8986216347084238063782947 13479324520626357095674421)
                    ·
                      refine ⟨1263686673808720977719477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13479324520626357095674421 1263686673808720977719477)
                      ·
                        rfl

theorem cell23_2461021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2461021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461021 prefixEnd_2461021 := by exact prefixLift 2461021
  have htrace : WordTrace (prefixWord ++ tailWord_2461021) baseStart_2461021 baseEnd_2461021 := by
    simpa [prefixWord, tailWord_2461021, baseEnd_2461021] using wordTrace_append hprefix tailTrace_2461021
  have hstable : (prefixWord ++ tailWord_2461021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461021).length < 2 ^ (prefixWord ++ tailWord_2461021).sum := by decide
  have hdescent : baseEnd_2461021 < baseStart_2461021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461040 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 3, 4, 2]
def baseStart_2461040 : Nat := 118140960795 + 2461040 * 2 ^ 59
def prefixEnd_2461040 : Nat := 4983230072969 + 3 ^ 40 * 2461040 * 2
def baseEnd_2461040 : Nat := 1263696429941156403381889

theorem tailTrace_2461040 : CollatzResearch.WordTrace tailWord_2461040 prefixEnd_2461040 1263696429941156403381889 := by
  unfold tailWord_2461040
  simp only [CollatzResearch.WordTrace]
  refine ⟨44880751502039933507174287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59841002002719911342899049 44880751502039933507174287)
  ·
    refine ⟨67321127253059900260761431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44880751502039933507174287 67321127253059900260761431)
    ·
      refine ⟨100981690879589850391142147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67321127253059900260761431 100981690879589850391142147)
      ·
        refine ⟨151472536319384775586713221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100981690879589850391142147 151472536319384775586713221)
        ·
          refine ⟨28401100559884645422508729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151472536319384775586713221 28401100559884645422508729)
          ·
            refine ⟨21300825419913484066881547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28401100559884645422508729 21300825419913484066881547)
            ·
              refine ⟨31951238129870226100322321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21300825419913484066881547 31951238129870226100322321)
              ·
                refine ⟨23963428597402669575241741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31951238129870226100322321 23963428597402669575241741)
                ·
                  refine ⟨8986285724026001090715653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23963428597402669575241741 8986285724026001090715653)
                  ·
                    refine ⟨1684928573254875204509185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8986285724026001090715653 1684928573254875204509185)
                    ·
                      refine ⟨1263696429941156403381889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684928573254875204509185 1263696429941156403381889)
                      ·
                        rfl

theorem cell23_2461040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 4, 2].length) (baseStart_2461040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461040 prefixEnd_2461040 := by exact prefixLift 2461040
  have htrace : WordTrace (prefixWord ++ tailWord_2461040) baseStart_2461040 baseEnd_2461040 := by
    simpa [prefixWord, tailWord_2461040, baseEnd_2461040] using wordTrace_append hprefix tailTrace_2461040
  have hstable : (prefixWord ++ tailWord_2461040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461040).length < 2 ^ (prefixWord ++ tailWord_2461040).sum := by decide
  have hdescent : baseEnd_2461040 < baseStart_2461040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461063 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 9]
def baseStart_2461063 : Nat := 118140960795 + 2461063 * 2 ^ 59
def prefixEnd_2461063 : Nat := 4983230072969 + 3 ^ 40 * 2461063 * 2
def baseEnd_2461063 : Nat := 140412026666245534821587

theorem tailTrace_2461063 : CollatzResearch.WordTrace tailWord_2461063 prefixEnd_2461063 140412026666245534821587 := by
  unfold tailWord_2461063
  simp only [CollatzResearch.WordTrace]
  refine ⟨89762341882996541942435843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59841561255331027961623895 89762341882996541942435843)
  ·
    refine ⟨134643512824494812913653765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89762341882996541942435843 134643512824494812913653765)
    ·
      refine ⟨25245658654592777421310081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134643512824494812913653765 25245658654592777421310081)
      ·
        refine ⟨18934243990944583065982561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25245658654592777421310081 18934243990944583065982561)
        ·
          refine ⟨14200682993208437299486921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18934243990944583065982561 14200682993208437299486921)
          ·
            refine ⟨10650512244906327974615191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14200682993208437299486921 10650512244906327974615191)
            ·
              refine ⟨15975768367359491961922787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10650512244906327974615191 15975768367359491961922787)
              ·
                refine ⟨23963652551039237942884181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15975768367359491961922787 23963652551039237942884181)
                ·
                  refine ⟨140412026666245534821587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23963652551039237942884181 140412026666245534821587)
                  ·
                    rfl

theorem cell23_2461063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 9].length) (baseStart_2461063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461063 prefixEnd_2461063 := by exact prefixLift 2461063
  have htrace : WordTrace (prefixWord ++ tailWord_2461063) baseStart_2461063 baseEnd_2461063 := by
    simpa [prefixWord, tailWord_2461063, baseEnd_2461063] using wordTrace_append hprefix tailTrace_2461063
  have hstable : (prefixWord ++ tailWord_2461063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461063).length < 2 ^ (prefixWord ++ tailWord_2461063).sum := by decide
  have hdescent : baseEnd_2461063 < baseStart_2461063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461100 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 1, 7, 2]
def baseStart_2461100 : Nat := 118140960795 + 2461100 * 2 ^ 59
def prefixEnd_2461100 : Nat := 4983230072969 + 3 ^ 40 * 2461100 * 2
def baseEnd_2461100 : Nat := 1263727238780426168631613

theorem tailTrace_2461100 : CollatzResearch.WordTrace tailWord_2461100 prefixEnd_2461100 1263727238780426168631613 := by
  unfold tailWord_2461100
  simp only [CollatzResearch.WordTrace]
  refine ⟨44881845691931248630766377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59842460922574998174355169 44881845691931248630766377)
  ·
    refine ⟨33661384268948436473074783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44881845691931248630766377 33661384268948436473074783)
    ·
      refine ⟨50492076403422654709612175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33661384268948436473074783 50492076403422654709612175)
      ·
        refine ⟨75738114605133982064418263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50492076403422654709612175 75738114605133982064418263)
        ·
          refine ⟨113607171907700973096627395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75738114605133982064418263 113607171907700973096627395)
          ·
            refine ⟨170410757861551459644941093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113607171907700973096627395 170410757861551459644941093)
            ·
              refine ⟨31952017099040898683426455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170410757861551459644941093 31952017099040898683426455)
              ·
                refine ⟨47928025648561348025139683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31952017099040898683426455 47928025648561348025139683)
                ·
                  refine ⟨71892038472842022037709525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47928025648561348025139683 71892038472842022037709525)
                  ·
                    refine ⟨1684969651707234891508817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 71892038472842022037709525 1684969651707234891508817)
                    ·
                      refine ⟨1263727238780426168631613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1684969651707234891508817 1263727238780426168631613)
                      ·
                        rfl

theorem cell23_2461100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 7, 2].length) (baseStart_2461100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461100 prefixEnd_2461100 := by exact prefixLift 2461100
  have htrace : WordTrace (prefixWord ++ tailWord_2461100) baseStart_2461100 baseEnd_2461100 := by
    simpa [prefixWord, tailWord_2461100, baseEnd_2461100] using wordTrace_append hprefix tailTrace_2461100
  have hstable : (prefixWord ++ tailWord_2461100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461100).length < 2 ^ (prefixWord ++ tailWord_2461100).sum := by decide
  have hdescent : baseEnd_2461100 < baseStart_2461100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461103 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 5]
def baseStart_2461103 : Nat := 118140960795 + 2461103 * 2 ^ 59
def prefixEnd_2461103 : Nat := 4983230072969 + 3 ^ 40 * 2461103 * 2
def baseEnd_2461103 : Nat := 1263728779222389656894099

theorem tailTrace_2461103 : CollatzResearch.WordTrace tailWord_2461103 prefixEnd_2461103 1263728779222389656894099 := by
  unfold tailWord_2461103
  simp only [CollatzResearch.WordTrace]
  refine ⟨89763800802851628773891963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59842533868567752515927975 89763800802851628773891963)
  ·
    refine ⟨134645701204277443160837945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89763800802851628773891963 134645701204277443160837945)
    ·
      refine ⟨100984275903208082370628459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134645701204277443160837945 100984275903208082370628459)
      ·
        refine ⟨151476413854812123555942689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100984275903208082370628459 151476413854812123555942689)
        ·
          refine ⟨113607310391109092666957017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151476413854812123555942689 113607310391109092666957017)
          ·
            refine ⟨85205482793331819500217763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113607310391109092666957017 85205482793331819500217763)
            ·
              refine ⟨127808224189997729250326645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85205482793331819500217763 127808224189997729250326645)
              ·
                refine ⟨11982021017812287117218123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127808224189997729250326645 11982021017812287117218123)
                ·
                  refine ⟨17973031526718430675827185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11982021017812287117218123 17973031526718430675827185)
                  ·
                    refine ⟨13479773645038823006870389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17973031526718430675827185 13479773645038823006870389)
                    ·
                      refine ⟨1263728779222389656894099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13479773645038823006870389 1263728779222389656894099)
                      ·
                        rfl

theorem cell23_2461103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_2461103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461103 prefixEnd_2461103 := by exact prefixLift 2461103
  have htrace : WordTrace (prefixWord ++ tailWord_2461103) baseStart_2461103 baseEnd_2461103 := by
    simpa [prefixWord, tailWord_2461103, baseEnd_2461103] using wordTrace_append hprefix tailTrace_2461103
  have hstable : (prefixWord ++ tailWord_2461103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461103).length < 2 ^ (prefixWord ++ tailWord_2461103).sum := by decide
  have hdescent : baseEnd_2461103 < baseStart_2461103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461130 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_2461130 : Nat := 118140960795 + 2461130 * 2 ^ 59
def prefixEnd_2461130 : Nat := 4983230072969 + 3 ^ 40 * 2461130 * 2
def baseEnd_2461130 : Nat := 1263742643200061051256475

theorem tailTrace_2461130 : CollatzResearch.WordTrace tailWord_2461130 prefixEnd_2461130 1263742643200061051256475 := by
  unfold tailWord_2461130
  simp only [CollatzResearch.WordTrace]
  refine ⟨22441196393438453096281211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59843190382502541590083229 22441196393438453096281211)
  ·
    refine ⟨33661794590157679644421817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22441196393438453096281211 33661794590157679644421817)
    ·
      refine ⟨25246345942618259733316363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33661794590157679644421817 25246345942618259733316363)
      ·
        refine ⟨37869518913927389599974545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25246345942618259733316363 37869518913927389599974545)
        ·
          refine ⟨28402139185445542199980909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37869518913927389599974545 28402139185445542199980909)
          ·
            refine ⟨10650802194542078324992841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28402139185445542199980909 10650802194542078324992841)
            ·
              refine ⟨7988101645906558743744631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10650802194542078324992841 7988101645906558743744631)
              ·
                refine ⟨11982152468859838115616947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7988101645906558743744631 11982152468859838115616947)
                ·
                  refine ⟨17973228703289757173425421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11982152468859838115616947 17973228703289757173425421)
                  ·
                    refine ⟨6739960763733658940034533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17973228703289757173425421 6739960763733658940034533)
                    ·
                      refine ⟨1263742643200061051256475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6739960763733658940034533 1263742643200061051256475)
                      ·
                        rfl

theorem cell23_2461130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_2461130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461130 prefixEnd_2461130 := by exact prefixLift 2461130
  have htrace : WordTrace (prefixWord ++ tailWord_2461130) baseStart_2461130 baseEnd_2461130 := by
    simpa [prefixWord, tailWord_2461130, baseEnd_2461130] using wordTrace_append hprefix tailTrace_2461130
  have hstable : (prefixWord ++ tailWord_2461130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461130).length < 2 ^ (prefixWord ++ tailWord_2461130).sum := by decide
  have hdescent : baseEnd_2461130 < baseStart_2461130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461143 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_2461143 : Nat := 118140960795 + 2461143 * 2 ^ 59
def prefixEnd_2461143 : Nat := 4983230072969 + 3 ^ 40 * 2461143 * 2
def baseEnd_2461143 : Nat := 1263749318448569500393915

theorem tailTrace_2461143 : CollatzResearch.WordTrace tailWord_2461143 prefixEnd_2461143 1263749318448569500393915 := by
  unfold tailWord_2461143
  simp only [CollatzResearch.WordTrace]
  refine ⟨89765259722706715605348083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59843506481804477070232055 89765259722706715605348083)
  ·
    refine ⟨134647889584060073408022125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89765259722706715605348083 134647889584060073408022125)
    ·
      refine ⟨50492958594022527528008297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134647889584060073408022125 50492958594022527528008297)
      ·
        refine ⟨37869718945516895646006223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50492958594022527528008297 37869718945516895646006223)
        ·
          refine ⟨56804578418275343469009335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37869718945516895646006223 56804578418275343469009335)
          ·
            refine ⟨85206867627413015203514003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56804578418275343469009335 85206867627413015203514003)
            ·
              refine ⟨127810301441119522805271005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85206867627413015203514003 127810301441119522805271005)
              ·
                refine ⟨47928863040419821051976627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127810301441119522805271005 47928863040419821051976627)
                ·
                  refine ⟨71893294560629731577964941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47928863040419821051976627 71893294560629731577964941)
                  ·
                    refine ⟨26959985460236149341736853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71893294560629731577964941 26959985460236149341736853)
                    ·
                      refine ⟨1263749318448569500393915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26959985460236149341736853 1263749318448569500393915)
                      ·
                        rfl

theorem cell23_2461143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_2461143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461143 prefixEnd_2461143 := by exact prefixLift 2461143
  have htrace : WordTrace (prefixWord ++ tailWord_2461143) baseStart_2461143 baseEnd_2461143 := by
    simpa [prefixWord, tailWord_2461143, baseEnd_2461143] using wordTrace_append hprefix tailTrace_2461143
  have hstable : (prefixWord ++ tailWord_2461143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461143).length < 2 ^ (prefixWord ++ tailWord_2461143).sum := by decide
  have hdescent : baseEnd_2461143 < baseStart_2461143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461180 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_2461180 : Nat := 118140960795 + 2461180 * 2 ^ 59
def prefixEnd_2461180 : Nat := 4983230072969 + 3 ^ 40 * 2461180 * 2
def baseEnd_2461180 : Nat := 1263768317232785855631245

theorem tailTrace_2461180 : CollatzResearch.WordTrace tailWord_2461180 prefixEnd_2461180 1263768317232785855631245 := by
  unfold tailWord_2461180
  simp only [CollatzResearch.WordTrace]
  refine ⟨44883304611786335462222497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59844406149048447282963329 44883304611786335462222497)
  ·
    refine ⟨33662478458839751596666873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44883304611786335462222497 33662478458839751596666873)
    ·
      refine ⟨25246858844129813697500155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33662478458839751596666873 25246858844129813697500155)
      ·
        refine ⟨37870288266194720546250233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25246858844129813697500155 37870288266194720546250233)
        ·
          refine ⟨28402716199646040409687675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37870288266194720546250233 28402716199646040409687675)
          ·
            refine ⟨42604074299469060614531513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28402716199646040409687675 42604074299469060614531513)
            ·
              refine ⟨31953055724601795460898635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42604074299469060614531513 31953055724601795460898635)
              ·
                refine ⟨47929583586902693191347953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31953055724601795460898635 47929583586902693191347953)
                ·
                  refine ⟨35947187690177019893510965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47929583586902693191347953 35947187690177019893510965)
                  ·
                    refine ⟨3370048845954095615016653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35947187690177019893510965 3370048845954095615016653)
                    ·
                      refine ⟨1263768317232785855631245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3370048845954095615016653 1263768317232785855631245)
                      ·
                        rfl

theorem cell23_2461180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_2461180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461180 prefixEnd_2461180 := by exact prefixLift 2461180
  have htrace : WordTrace (prefixWord ++ tailWord_2461180) baseStart_2461180 baseEnd_2461180 := by
    simpa [prefixWord, tailWord_2461180, baseEnd_2461180] using wordTrace_append hprefix tailTrace_2461180
  have hstable : (prefixWord ++ tailWord_2461180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461180).length < 2 ^ (prefixWord ++ tailWord_2461180).sum := by decide
  have hdescent : baseEnd_2461180 < baseStart_2461180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461208 : List Nat := [2, 1, 2, 3, 4, 2, 2, 2, 1, 4]
def baseStart_2461208 : Nat := 118140960795 + 2461208 * 2 ^ 59
def prefixEnd_2461208 : Nat := 4983230072969 + 3 ^ 40 * 2461208 * 2
def baseEnd_2461208 : Nat := 421260898230370582027039

theorem tailTrace_2461208 : CollatzResearch.WordTrace tailWord_2461208 prefixEnd_2461208 421260898230370582027039 := by
  unfold tailWord_2461208
  simp only [CollatzResearch.WordTrace]
  refine ⟨44883815233735615853232139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59845086978314154470976185 44883815233735615853232139)
  ·
    refine ⟨67325722850603423779848209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44883815233735615853232139 67325722850603423779848209)
    ·
      refine ⟨50494292137952567834886157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67325722850603423779848209 50494292137952567834886157)
      ·
        refine ⟨18935359551732212938082309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50494292137952567834886157 18935359551732212938082309)
        ·
          refine ⟨3550379915949789925890433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18935359551732212938082309 3550379915949789925890433)
          ·
            refine ⟨2662784936962342444417825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3550379915949789925890433 2662784936962342444417825)
            ·
              refine ⟨1997088702721756833313369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2662784936962342444417825 1997088702721756833313369)
              ·
                refine ⟨1497816527041317624985027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1997088702721756833313369 1497816527041317624985027)
                ·
                  refine ⟨2246724790561976437477541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497816527041317624985027 2246724790561976437477541)
                  ·
                    refine ⟨421260898230370582027039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2246724790561976437477541 421260898230370582027039)
                    ·
                      rfl

theorem cell23_2461208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_2461208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461208 prefixEnd_2461208 := by exact prefixLift 2461208
  have htrace : WordTrace (prefixWord ++ tailWord_2461208) baseStart_2461208 baseEnd_2461208 := by
    simpa [prefixWord, tailWord_2461208, baseEnd_2461208] using wordTrace_append hprefix tailTrace_2461208
  have hstable : (prefixWord ++ tailWord_2461208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461208).length < 2 ^ (prefixWord ++ tailWord_2461208).sum := by decide
  have hdescent : baseEnd_2461208 < baseStart_2461208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461237 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_2461237 : Nat := 118140960795 + 2461237 * 2 ^ 59
def prefixEnd_2461237 : Nat := 4983230072969 + 3 ^ 40 * 2461237 * 2
def baseEnd_2461237 : Nat := 1263797585630092132618483

theorem tailTrace_2461237 : CollatzResearch.WordTrace tailWord_2461237 prefixEnd_2461237 1263797585630092132618483 := by
  unfold tailWord_2461237
  simp only [CollatzResearch.WordTrace]
  refine ⟨89768688184366169659269965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59845792122910779772846643 89768688184366169659269965)
  ·
    refine ⟨33663258069137313622226237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89768688184366169659269965 33663258069137313622226237)
    ·
      refine ⟨12623721775926492608334839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33663258069137313622226237 12623721775926492608334839)
      ·
        refine ⟨18935582663889738912502259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12623721775926492608334839 18935582663889738912502259)
        ·
          refine ⟨28403373995834608368753389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18935582663889738912502259 28403373995834608368753389)
          ·
            refine ⟨10651265248437978138282521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28403373995834608368753389 10651265248437978138282521)
            ·
              refine ⟨7988448936328483603711891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10651265248437978138282521 7988448936328483603711891)
              ·
                refine ⟨11982673404492725405567837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7988448936328483603711891 11982673404492725405567837)
                ·
                  refine ⟨4493502526684772027087939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11982673404492725405567837 4493502526684772027087939)
                  ·
                    refine ⟨6740253790027158040631909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4493502526684772027087939 6740253790027158040631909)
                    ·
                      refine ⟨1263797585630092132618483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6740253790027158040631909 1263797585630092132618483)
                      ·
                        rfl

theorem cell23_2461237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_2461237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461237 prefixEnd_2461237 := by exact prefixLift 2461237
  have htrace : WordTrace (prefixWord ++ tailWord_2461237) baseStart_2461237 baseEnd_2461237 := by
    simpa [prefixWord, tailWord_2461237, baseEnd_2461237] using wordTrace_append hprefix tailTrace_2461237
  have hstable : (prefixWord ++ tailWord_2461237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461237).length < 2 ^ (prefixWord ++ tailWord_2461237).sum := by decide
  have hdescent : baseEnd_2461237 < baseStart_2461237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461241 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 2, 3, 2]
def baseStart_2461241 : Nat := 118140960795 + 2461241 * 2 ^ 59
def prefixEnd_2461241 : Nat := 4983230072969 + 3 ^ 40 * 2461241 * 2
def baseEnd_2461241 : Nat := 1263799639552710116968465

theorem tailTrace_2461241 : CollatzResearch.WordTrace tailWord_2461241 prefixEnd_2461241 1263799639552710116968465 := by
  unfold tailWord_2461241
  simp only [CollatzResearch.WordTrace]
  refine ⟨89768834076351678342415577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59845889384234452228277051 89768834076351678342415577)
  ·
    refine ⟨67326625557263758756811683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89768834076351678342415577 67326625557263758756811683)
    ·
      refine ⟨100989938335895638135217525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67326625557263758756811683 100989938335895638135217525)
      ·
        refine ⟨9467806718990216075176643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100989938335895638135217525 9467806718990216075176643)
        ·
          refine ⟨14201710078485324112764965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9467806718990216075176643 14201710078485324112764965)
          ·
            refine ⟨2662820639715998271143431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14201710078485324112764965 2662820639715998271143431)
            ·
              refine ⟨3994230959573997406715147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2662820639715998271143431 3994230959573997406715147)
              ·
                refine ⟨5991346439360996110072721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994230959573997406715147 5991346439360996110072721)
                ·
                  refine ⟨4493509829520747082554541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5991346439360996110072721 4493509829520747082554541)
                  ·
                    refine ⟨1685066186070280155957953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4493509829520747082554541 1685066186070280155957953)
                    ·
                      refine ⟨1263799639552710116968465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685066186070280155957953 1263799639552710116968465)
                      ·
                        rfl

theorem cell23_2461241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_2461241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461241 prefixEnd_2461241 := by exact prefixLift 2461241
  have htrace : WordTrace (prefixWord ++ tailWord_2461241) baseStart_2461241 baseEnd_2461241 := by
    simpa [prefixWord, tailWord_2461241, baseEnd_2461241] using wordTrace_append hprefix tailTrace_2461241
  have hstable : (prefixWord ++ tailWord_2461241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461241).length < 2 ^ (prefixWord ++ tailWord_2461241).sum := by decide
  have hdescent : baseEnd_2461241 < baseStart_2461241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461260 : List Nat := [2, 2, 1, 3, 1, 4, 10]
def baseStart_2461260 : Nat := 118140960795 + 2461260 * 2 ^ 59
def prefixEnd_2461260 : Nat := 4983230072969 + 3 ^ 40 * 2461260 * 2
def baseEnd_2461260 : Nat := 15602585131915377069517

theorem tailTrace_2461260 : CollatzResearch.WordTrace tailWord_2461260 prefixEnd_2461260 15602585131915377069517 := by
  unfold tailWord_2461260
  simp only [CollatzResearch.WordTrace]
  refine ⟨44884763531641422293678617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59846351375521896391571489 44884763531641422293678617)
  ·
    refine ⟨33663572648731066720258963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44884763531641422293678617 33663572648731066720258963)
    ·
      refine ⟨50495358973096600080388445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33663572648731066720258963 50495358973096600080388445)
      ·
        refine ⟨18935759614911225030145667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50495358973096600080388445 18935759614911225030145667)
        ·
          refine ⟨28403639422366837545218501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18935759614911225030145667 28403639422366837545218501)
          ·
            refine ⟨5325682391693782039728469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28403639422366837545218501 5325682391693782039728469)
            ·
              refine ⟨15602585131915377069517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5325682391693782039728469 15602585131915377069517)
              ·
                rfl

theorem cell23_2461260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 10].length) (baseStart_2461260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461260 prefixEnd_2461260 := by exact prefixLift 2461260
  have htrace : WordTrace (prefixWord ++ tailWord_2461260) baseStart_2461260 baseEnd_2461260 := by
    simpa [prefixWord, tailWord_2461260, baseEnd_2461260] using wordTrace_append hprefix tailTrace_2461260
  have hstable : (prefixWord ++ tailWord_2461260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461260).length < 2 ^ (prefixWord ++ tailWord_2461260).sum := by decide
  have hdescent : baseEnd_2461260 < baseStart_2461260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461271 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 3, 2, 2]
def baseStart_2461271 : Nat := 118140960795 + 2461271 * 2 ^ 59
def prefixEnd_2461271 : Nat := 4983230072969 + 3 ^ 40 * 2461271 * 2
def baseEnd_2461271 : Nat := 1263815043972344999593327

theorem tailTrace_2461271 : CollatzResearch.WordTrace tailWord_2461271 prefixEnd_2461271 1263815043972344999593327 := by
  unfold tailWord_2461271
  simp only [CollatzResearch.WordTrace]
  refine ⟨89769928266242993466007667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59846618844161995644005111 89769928266242993466007667)
  ·
    refine ⟨134654892399364490199011501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89769928266242993466007667 134654892399364490199011501)
    ·
      refine ⟨50495584649761683824629313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134654892399364490199011501 50495584649761683824629313)
      ·
        refine ⟨37871688487321262868471985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50495584649761683824629313 37871688487321262868471985)
        ·
          refine ⟨28403766365490947151353989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37871688487321262868471985 28403766365490947151353989)
          ·
            refine ⟨5325706193529552590878873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28403766365490947151353989 5325706193529552590878873)
            ·
              refine ⟨3994279645147164443159155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5325706193529552590878873 3994279645147164443159155)
              ·
                refine ⟨5991419467720746664738733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994279645147164443159155 5991419467720746664738733)
                ·
                  refine ⟨2246782300395279999277025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5991419467720746664738733 2246782300395279999277025)
                  ·
                    refine ⟨1685086725296459999457769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2246782300395279999277025 1685086725296459999457769)
                    ·
                      refine ⟨1263815043972344999593327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685086725296459999457769 1263815043972344999593327)
                      ·
                        rfl

theorem cell23_2461271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_2461271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461271 prefixEnd_2461271 := by exact prefixLift 2461271
  have htrace : WordTrace (prefixWord ++ tailWord_2461271) baseStart_2461271 baseEnd_2461271 := by
    simpa [prefixWord, tailWord_2461271, baseEnd_2461271] using wordTrace_append hprefix tailTrace_2461271
  have hstable : (prefixWord ++ tailWord_2461271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461271).length < 2 ^ (prefixWord ++ tailWord_2461271).sum := by decide
  have hdescent : baseEnd_2461271 < baseStart_2461271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461284 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_2461284 : Nat := 118140960795 + 2461284 * 2 ^ 59
def prefixEnd_2461284 : Nat := 4983230072969 + 3 ^ 40 * 2461284 * 2
def baseEnd_2461284 : Nat := 1263821719220853448730767

theorem tailTrace_2461284 : CollatzResearch.WordTrace tailWord_2461284 prefixEnd_2461284 1263821719220853448730767 := by
  unfold tailWord_2461284
  simp only [CollatzResearch.WordTrace]
  refine ⟨44885201207597948343115453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59846934943463931124153937 44885201207597948343115453)
  ·
    refine ⟨16831950452849230628668295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44885201207597948343115453 16831950452849230628668295)
    ·
      refine ⟨25247925679273845943002443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16831950452849230628668295 25247925679273845943002443)
      ·
        refine ⟨37871888518910768914503665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25247925679273845943002443 37871888518910768914503665)
        ·
          refine ⟨28403916389183076685877749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37871888518910768914503665 28403916389183076685877749)
          ·
            refine ⟨2662867161485913439301039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28403916389183076685877749 2662867161485913439301039)
            ·
              refine ⟨3994300742228870158951559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2662867161485913439301039 3994300742228870158951559)
              ·
                refine ⟨5991451113343305238427339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994300742228870158951559 5991451113343305238427339)
                ·
                  refine ⟨8987176670014957857641009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5991451113343305238427339 8987176670014957857641009)
                  ·
                    refine ⟨6740382502511218393230757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8987176670014957857641009 6740382502511218393230757)
                    ·
                      refine ⟨1263821719220853448730767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6740382502511218393230757 1263821719220853448730767)
                      ·
                        rfl

theorem cell23_2461284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_2461284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461284 prefixEnd_2461284 := by exact prefixLift 2461284
  have htrace : WordTrace (prefixWord ++ tailWord_2461284) baseStart_2461284 baseEnd_2461284 := by
    simpa [prefixWord, tailWord_2461284, baseEnd_2461284] using wordTrace_append hprefix tailTrace_2461284
  have hstable : (prefixWord ++ tailWord_2461284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461284).length < 2 ^ (prefixWord ++ tailWord_2461284).sum := by decide
  have hdescent : baseEnd_2461284 < baseStart_2461284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461297 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 2, 7, 2]
def baseStart_2461297 : Nat := 118140960795 + 2461297 * 2 ^ 59
def prefixEnd_2461297 : Nat := 4983230072969 + 3 ^ 40 * 2461297 * 2
def baseEnd_2461297 : Nat := 1263828394469361897868207

theorem tailTrace_2461297 : CollatzResearch.WordTrace tailWord_2461297 prefixEnd_2461297 1263828394469361897868207 := by
  unfold tailWord_2461297
  simp only [CollatzResearch.WordTrace]
  refine ⟨89770876564148799906454145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59847251042765866604302763 89770876564148799906454145)
  ·
    refine ⟨67328157423111599929840609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89770876564148799906454145 67328157423111599929840609)
    ·
      refine ⟨50496118067333699947380457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67328157423111599929840609 50496118067333699947380457)
      ·
        refine ⟨37872088550500274960535343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50496118067333699947380457 37872088550500274960535343)
        ·
          refine ⟨56808132825750412440803015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37872088550500274960535343 56808132825750412440803015)
          ·
            refine ⟨85212199238625618661204523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56808132825750412440803015 85212199238625618661204523)
            ·
              refine ⟨127818298857938427991806785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85212199238625618661204523 127818298857938427991806785)
              ·
                refine ⟨95863724143453820993855089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127818298857938427991806785 95863724143453820993855089)
                ·
                  refine ⟨71897793107590365745391317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95863724143453820993855089 71897793107590365745391317)
                  ·
                    refine ⟨1685104525959149197157609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 71897793107590365745391317 1685104525959149197157609)
                    ·
                      refine ⟨1263828394469361897868207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685104525959149197157609 1263828394469361897868207)
                      ·
                        rfl

theorem cell23_2461297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_2461297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461297 prefixEnd_2461297 := by exact prefixLift 2461297
  have htrace : WordTrace (prefixWord ++ tailWord_2461297) baseStart_2461297 baseEnd_2461297 := by
    simpa [prefixWord, tailWord_2461297, baseEnd_2461297] using wordTrace_append hprefix tailTrace_2461297
  have hstable : (prefixWord ++ tailWord_2461297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461297).length < 2 ^ (prefixWord ++ tailWord_2461297).sum := by decide
  have hdescent : baseEnd_2461297 < baseStart_2461297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461327 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 2, 8, 2]
def baseStart_2461327 : Nat := 118140960795 + 2461327 * 2 ^ 59
def prefixEnd_2461327 : Nat := 4983230072969 + 3 ^ 40 * 2461327 * 2
def baseEnd_2461327 : Nat := 1263843798888996780493069

theorem tailTrace_2461327 : CollatzResearch.WordTrace tailWord_2461327 prefixEnd_2461327 1263843798888996780493069 := by
  unfold tailWord_2461327
  simp only [CollatzResearch.WordTrace]
  refine ⟨89771970754040115030046235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59847980502693410020030823 89771970754040115030046235)
  ·
    refine ⟨134657956131060172545069353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89771970754040115030046235 134657956131060172545069353)
    ·
      refine ⟨100993467098295129408802015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134657956131060172545069353 100993467098295129408802015)
      ·
        refine ⟨151490200647442694113203023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100993467098295129408802015 151490200647442694113203023)
        ·
          refine ⟨227235300971164041169804535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151490200647442694113203023 227235300971164041169804535)
          ·
            refine ⟨340852951456746061754706803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227235300971164041169804535 340852951456746061754706803)
            ·
              refine ⟨511279427185119092632060205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340852951456746061754706803 511279427185119092632060205)
              ·
                refine ⟨191729785194419659737022577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 511279427185119092632060205 191729785194419659737022577)
                ·
                  refine ⟨143797338895814744802766933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191729785194419659737022577 143797338895814744802766933)
                  ·
                    refine ⟨1685125065185329040657425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 143797338895814744802766933 1685125065185329040657425)
                    ·
                      refine ⟨1263843798888996780493069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685125065185329040657425 1263843798888996780493069)
                      ·
                        rfl

theorem cell23_2461327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 8, 2].length) (baseStart_2461327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461327 prefixEnd_2461327 := by exact prefixLift 2461327
  have htrace : WordTrace (prefixWord ++ tailWord_2461327) baseStart_2461327 baseEnd_2461327 := by
    simpa [prefixWord, tailWord_2461327, baseEnd_2461327] using wordTrace_append hprefix tailTrace_2461327
  have hstable : (prefixWord ++ tailWord_2461327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461327).length < 2 ^ (prefixWord ++ tailWord_2461327).sum := by decide
  have hdescent : baseEnd_2461327 < baseStart_2461327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461348 : List Nat := [2, 3, 1, 2, 2, 4, 1, 2, 1, 3, 2]
def baseStart_2461348 : Nat := 118140960795 + 2461348 * 2 ^ 59
def prefixEnd_2461348 : Nat := 4983230072969 + 3 ^ 40 * 2461348 * 2
def baseEnd_2461348 : Nat := 1263854581982741198330473

theorem tailTrace_2461348 : CollatzResearch.WordTrace tailWord_2461348 prefixEnd_2461348 1263854581982741198330473 := by
  unfold tailWord_2461348
  simp only [CollatzResearch.WordTrace]
  refine ⟨44886368343482017808280349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59848491124642690411040465 44886368343482017808280349)
  ·
    refine ⟨16832388128805756678105131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44886368343482017808280349 16832388128805756678105131)
    ·
      refine ⟨25248582193208635017157697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16832388128805756678105131 25248582193208635017157697)
      ·
        refine ⟨18936436644906476262868273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25248582193208635017157697 18936436644906476262868273)
        ·
          refine ⟨14202327483679857197151205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18936436644906476262868273 14202327483679857197151205)
          ·
            refine ⟨2662936403189973224465851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14202327483679857197151205 2662936403189973224465851)
            ·
              refine ⟨3994404604784959836698777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2662936403189973224465851 3994404604784959836698777)
              ·
                refine ⟨2995803453588719877524083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3994404604784959836698777 2995803453588719877524083)
                ·
                  refine ⟨4493705180383079816286125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2995803453588719877524083 4493705180383079816286125)
                  ·
                    refine ⟨1685139442643654931107297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4493705180383079816286125 1685139442643654931107297)
                    ·
                      refine ⟨1263854581982741198330473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685139442643654931107297 1263854581982741198330473)
                      ·
                        rfl

theorem cell23_2461348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_2461348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461348 prefixEnd_2461348 := by exact prefixLift 2461348
  have htrace : WordTrace (prefixWord ++ tailWord_2461348) baseStart_2461348 baseEnd_2461348 := by
    simpa [prefixWord, tailWord_2461348, baseEnd_2461348] using wordTrace_append hprefix tailTrace_2461348
  have hstable : (prefixWord ++ tailWord_2461348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461348).length < 2 ^ (prefixWord ++ tailWord_2461348).sum := by decide
  have hdescent : baseEnd_2461348 < baseStart_2461348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461365 : List Nat := [1, 3, 3, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_2461365 : Nat := 118140960795 + 2461365 * 2 ^ 59
def prefixEnd_2461365 : Nat := 4983230072969 + 3 ^ 40 * 2461365 * 2
def baseEnd_2461365 : Nat := 1263863311153867631817895

theorem tailTrace_2461365 : CollatzResearch.WordTrace tailWord_2461365 prefixEnd_2461365 1263863311153867631817895 := by
  unfold tailWord_2461365
  simp only [CollatzResearch.WordTrace]
  refine ⟨89773356727902447519929549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59848904485268298346619699 89773356727902447519929549)
  ·
    refine ⟨33665008772963417819973581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89773356727902447519929549 33665008772963417819973581)
    ·
      refine ⟨12624378289861281682490093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33665008772963417819973581 12624378289861281682490093)
      ·
        refine ⟨4734141858697980630933785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12624378289861281682490093 4734141858697980630933785)
        ·
          refine ⟨3550606394023485473200339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4734141858697980630933785 3550606394023485473200339)
          ·
            refine ⟨5325909591035228209800509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3550606394023485473200339 5325909591035228209800509)
            ·
              refine ⟨1997216096638210578675191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5325909591035228209800509 1997216096638210578675191)
              ·
                refine ⟨2995824144957315868012787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1997216096638210578675191 2995824144957315868012787)
                ·
                  refine ⟨4493736217435973802019181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2995824144957315868012787 4493736217435973802019181)
                  ·
                    refine ⟨1685151081538490175757193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4493736217435973802019181 1685151081538490175757193)
                    ·
                      refine ⟨1263863311153867631817895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685151081538490175757193 1263863311153867631817895)
                      ·
                        rfl

theorem cell23_2461365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_2461365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461365 prefixEnd_2461365 := by exact prefixLift 2461365
  have htrace : WordTrace (prefixWord ++ tailWord_2461365) baseStart_2461365 baseEnd_2461365 := by
    simpa [prefixWord, tailWord_2461365, baseEnd_2461365] using wordTrace_append hprefix tailTrace_2461365
  have hstable : (prefixWord ++ tailWord_2461365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461365).length < 2 ^ (prefixWord ++ tailWord_2461365).sum := by decide
  have hdescent : baseEnd_2461365 < baseStart_2461365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461384 : List Nat := [2, 1, 3, 1, 2, 2, 3, 4, 5]
def baseStart_2461384 : Nat := 118140960795 + 2461384 * 2 ^ 59
def prefixEnd_2461384 : Nat := 4983230072969 + 3 ^ 40 * 2461384 * 2
def baseEnd_2461384 : Nat := 140430340809589228608923

theorem tailTrace_2461384 : CollatzResearch.WordTrace tailWord_2461384 prefixEnd_2461384 140430340809589228608923 := by
  unfold tailWord_2461384
  simp only [CollatzResearch.WordTrace]
  refine ⟨44887024857416806882435603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59849366476555742509914137 44887024857416806882435603)
  ·
    refine ⟨67330537286125210323653405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44887024857416806882435603 67330537286125210323653405)
    ·
      refine ⟨25248951482296953871370027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67330537286125210323653405 25248951482296953871370027)
      ·
        refine ⟨37873427223445430807055041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25248951482296953871370027 37873427223445430807055041)
        ·
          refine ⟨28405070417584073105291281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37873427223445430807055041 28405070417584073105291281)
          ·
            refine ⟨21303802813188054828968461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28405070417584073105291281 21303802813188054828968461)
            ·
              refine ⟨7988926054945520560863173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21303802813188054828968461 7988926054945520560863173)
              ·
                refine ⟨1497923635302285105161845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7988926054945520560863173 1497923635302285105161845)
                ·
                  refine ⟨140430340809589228608923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1497923635302285105161845 140430340809589228608923)
                  ·
                    rfl

theorem cell23_2461384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 5].length) (baseStart_2461384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461384 prefixEnd_2461384 := by exact prefixLift 2461384
  have htrace : WordTrace (prefixWord ++ tailWord_2461384) baseStart_2461384 baseEnd_2461384 := by
    simpa [prefixWord, tailWord_2461384, baseEnd_2461384] using wordTrace_append hprefix tailTrace_2461384
  have hstable : (prefixWord ++ tailWord_2461384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461384).length < 2 ^ (prefixWord ++ tailWord_2461384).sum := by decide
  have hdescent : baseEnd_2461384 < baseStart_2461384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461394 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_2461394 : Nat := 118140960795 + 2461394 * 2 ^ 59
def prefixEnd_2461394 : Nat := 4983230072969 + 3 ^ 40 * 2461394 * 2
def baseEnd_2461394 : Nat := 1263878202092848018355261

theorem tailTrace_2461394 : CollatzResearch.WordTrace tailWord_2461394 prefixEnd_2461394 1263878202092848018355261 := by
  unfold tailWord_2461394
  simp only [CollatzResearch.WordTrace]
  refine ⟨22443603611199346368183809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59849609629864923648490157 22443603611199346368183809)
  ·
    refine ⟨16832702708399509776137857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22443603611199346368183809 16832702708399509776137857)
    ·
      refine ⟨12624527031299632332103393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16832702708399509776137857 12624527031299632332103393)
      ·
        refine ⟨9468395273474724249077545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12624527031299632332103393 9468395273474724249077545)
        ·
          refine ⟨7101296455106043186808159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9468395273474724249077545 7101296455106043186808159)
          ·
            refine ⟨10651944682659064780212239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7101296455106043186808159 10651944682659064780212239)
            ·
              refine ⟨15977917023988597170318359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10651944682659064780212239 15977917023988597170318359)
              ·
                refine ⟨23966875535982895755477539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15977917023988597170318359 23966875535982895755477539)
                ·
                  refine ⟨35950313303974343633216309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23966875535982895755477539 35950313303974343633216309)
                  ·
                    refine ⟨3370341872247594715614029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35950313303974343633216309 3370341872247594715614029)
                    ·
                      refine ⟨1263878202092848018355261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3370341872247594715614029 1263878202092848018355261)
                      ·
                        rfl

theorem cell23_2461394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_2461394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461394 prefixEnd_2461394 := by exact prefixLift 2461394
  have htrace : WordTrace (prefixWord ++ tailWord_2461394) baseStart_2461394 baseEnd_2461394 := by
    simpa [prefixWord, tailWord_2461394, baseEnd_2461394] using wordTrace_append hprefix tailTrace_2461394
  have hstable : (prefixWord ++ tailWord_2461394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461394).length < 2 ^ (prefixWord ++ tailWord_2461394).sum := by decide
  have hdescent : baseEnd_2461394 < baseStart_2461394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461428 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2461428 : Nat := 118140960795 + 2461428 * 2 ^ 59
def prefixEnd_2461428 : Nat := 4983230072969 + 3 ^ 40 * 2461428 * 2
def baseEnd_2461428 : Nat := 1263895660435100885330105

theorem tailTrace_2461428 : CollatzResearch.WordTrace tailWord_2461428 prefixEnd_2461428 1263895660435100885330105 := by
  unfold tailWord_2461428
  simp only [CollatzResearch.WordTrace]
  refine ⟨44887827263337104639736469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59850436351116139519648625 44887827263337104639736469)
  ·
    refine ⟨2104116902968926779987647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44887827263337104639736469 2104116902968926779987647)
    ·
      refine ⟨3156175354453390169981471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2104116902968926779987647 3156175354453390169981471)
      ·
        refine ⟨4734263031680085254972207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3156175354453390169981471 4734263031680085254972207)
        ·
          refine ⟨7101394547520127882458311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4734263031680085254972207 7101394547520127882458311)
          ·
            refine ⟨10652091821280191823687467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7101394547520127882458311 10652091821280191823687467)
            ·
              refine ⟨15978137731920287735531201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10652091821280191823687467 15978137731920287735531201)
              ·
                refine ⟨11983603298940215801648401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15978137731920287735531201 11983603298940215801648401)
                ·
                  refine ⟨8987702474205161851236301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11983603298940215801648401 8987702474205161851236301)
                  ·
                    refine ⟨3370388427826935694213613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8987702474205161851236301 3370388427826935694213613)
                    ·
                      refine ⟨1263895660435100885330105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3370388427826935694213613 1263895660435100885330105)
                      ·
                        rfl

theorem cell23_2461428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2461428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461428 prefixEnd_2461428 := by exact prefixLift 2461428
  have htrace : WordTrace (prefixWord ++ tailWord_2461428) baseStart_2461428 baseEnd_2461428 := by
    simpa [prefixWord, tailWord_2461428, baseEnd_2461428] using wordTrace_append hprefix tailTrace_2461428
  have hstable : (prefixWord ++ tailWord_2461428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461428).length < 2 ^ (prefixWord ++ tailWord_2461428).sum := by decide
  have hdescent : baseEnd_2461428 < baseStart_2461428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461446 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2461446 : Nat := 118140960795 + 2461446 * 2 ^ 59
def prefixEnd_2461446 : Nat := 4983230072969 + 3 ^ 40 * 2461446 * 2
def baseEnd_2461446 : Nat := 1263904903086881814905023

theorem tailTrace_2461446 : CollatzResearch.WordTrace tailWord_2461446 prefixEnd_2461446 1263904903086881814905023 := by
  unfold tailWord_2461446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2805509720019031198550881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59850874027072665569085461 2805509720019031198550881)
  ·
    refine ⟨2104132290014273398913161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2805509720019031198550881 2104132290014273398913161)
    ·
      refine ⟨1578099217510705049184871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2104132290014273398913161 1578099217510705049184871)
      ·
        refine ⟨2367148826266057573777307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578099217510705049184871 2367148826266057573777307)
        ·
          refine ⟨3550723239399086360665961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367148826266057573777307 3550723239399086360665961)
          ·
            refine ⟨2663042429549314770499471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3550723239399086360665961 2663042429549314770499471)
            ·
              refine ⟨3994563644323972155749207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663042429549314770499471 3994563644323972155749207)
              ·
                refine ⟨5991845466485958233623811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994563644323972155749207 5991845466485958233623811)
                ·
                  refine ⟨8987768199728937350435717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5991845466485958233623811 8987768199728937350435717)
                  ·
                    refine ⟨1685206537449175753206697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8987768199728937350435717 1685206537449175753206697)
                    ·
                      refine ⟨1263904903086881814905023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685206537449175753206697 1263904903086881814905023)
                      ·
                        rfl

theorem cell23_2461446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2461446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461446 prefixEnd_2461446 := by exact prefixLift 2461446
  have htrace : WordTrace (prefixWord ++ tailWord_2461446) baseStart_2461446 baseEnd_2461446 := by
    simpa [prefixWord, tailWord_2461446, baseEnd_2461446] using wordTrace_append hprefix tailTrace_2461446
  have hstable : (prefixWord ++ tailWord_2461446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461446).length < 2 ^ (prefixWord ++ tailWord_2461446).sum := by decide
  have hdescent : baseEnd_2461446 < baseStart_2461446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461454 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_2461454 : Nat := 118140960795 + 2461454 * 2 ^ 59
def prefixEnd_2461454 : Nat := 4983230072969 + 3 ^ 40 * 2461454 * 2
def baseEnd_2461454 : Nat := 1263909010932117783604985

theorem tailTrace_2461454 : CollatzResearch.WordTrace tailWord_2461454 prefixEnd_2461454 1263909010932117783604985 := by
  unfold tailWord_2461454
  simp only [CollatzResearch.WordTrace]
  refine ⟨11222075353072501964989927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59851068549720010479946277 11222075353072501964989927)
  ·
    refine ⟨16833113029608752947484891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11222075353072501964989927 16833113029608752947484891)
    ·
      refine ⟨25249669544413129421227337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16833113029608752947484891 25249669544413129421227337)
      ·
        refine ⟨18937252158309847065920503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25249669544413129421227337 18937252158309847065920503)
        ·
          refine ⟨28405878237464770598880755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18937252158309847065920503 28405878237464770598880755)
          ·
            refine ⟨42608817356197155898321133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28405878237464770598880755 42608817356197155898321133)
            ·
              refine ⟨15978306508573933461870425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42608817356197155898321133 15978306508573933461870425)
              ·
                refine ⟨11983729881430450096402819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15978306508573933461870425 11983729881430450096402819)
                ·
                  refine ⟨17975594822145675144604229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11983729881430450096402819 17975594822145675144604229)
                  ·
                    refine ⟨3370424029152314089613293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17975594822145675144604229 3370424029152314089613293)
                    ·
                      refine ⟨1263909010932117783604985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3370424029152314089613293 1263909010932117783604985)
                      ·
                        rfl

theorem cell23_2461454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_2461454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461454 prefixEnd_2461454 := by exact prefixLift 2461454
  have htrace : WordTrace (prefixWord ++ tailWord_2461454) baseStart_2461454 baseEnd_2461454 := by
    simpa [prefixWord, tailWord_2461454, baseEnd_2461454] using wordTrace_append hprefix tailTrace_2461454
  have hstable : (prefixWord ++ tailWord_2461454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461454).length < 2 ^ (prefixWord ++ tailWord_2461454).sum := by decide
  have hdescent : baseEnd_2461454 < baseStart_2461454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461521 : List Nat := [1, 2, 2, 1, 5, 1, 3, 2, 1, 5]
def baseStart_2461521 : Nat := 118140960795 + 2461521 * 2 ^ 59
def prefixEnd_2461521 : Nat := 4983230072969 + 3 ^ 40 * 2461521 * 2
def baseEnd_2461521 : Nat := 421314471378656340489059

theorem tailTrace_2461521 : CollatzResearch.WordTrace tailWord_2461521 prefixEnd_2461521 421314471378656340489059 := by
  unfold tailWord_2461521
  simp only [CollatzResearch.WordTrace]
  refine ⟨89779046515337286162608417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59852697676891524108405611 89779046515337286162608417)
  ·
    refine ⟨67334284886502964621956313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89779046515337286162608417 67334284886502964621956313)
    ·
      refine ⟨50500713664877223466467235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67334284886502964621956313 50500713664877223466467235)
      ·
        refine ⟨75751070497315835199700853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50500713664877223466467235 75751070497315835199700853)
        ·
          refine ⟨7101662859123359549971955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75751070497315835199700853 7101662859123359549971955)
          ·
            refine ⟨10652494288685039324957933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7101662859123359549971955 10652494288685039324957933)
            ·
              refine ⟨3994685358256889746859225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10652494288685039324957933 3994685358256889746859225)
              ·
                refine ⟨2996014018692667310144419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3994685358256889746859225 2996014018692667310144419)
                ·
                  refine ⟨4494021028039000965216629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996014018692667310144419 4494021028039000965216629)
                  ·
                    refine ⟨421314471378656340489059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4494021028039000965216629 421314471378656340489059)
                    ·
                      rfl

theorem cell23_2461521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_2461521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461521 prefixEnd_2461521 := by exact prefixLift 2461521
  have htrace : WordTrace (prefixWord ++ tailWord_2461521) baseStart_2461521 baseEnd_2461521 := by
    simpa [prefixWord, tailWord_2461521, baseEnd_2461521] using wordTrace_append hprefix tailTrace_2461521
  have hstable : (prefixWord ++ tailWord_2461521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461521).length < 2 ^ (prefixWord ++ tailWord_2461521).sum := by decide
  have hdescent : baseEnd_2461521 < baseStart_2461521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461554 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2461554 : Nat := 118140960795 + 2461554 * 2 ^ 59
def prefixEnd_2461554 : Nat := 4983230072969 + 3 ^ 40 * 2461554 * 2
def baseEnd_2461554 : Nat := 1263960358997567392354525

theorem tailTrace_2461554 : CollatzResearch.WordTrace tailWord_2461554 prefixEnd_2461554 1263960358997567392354525 := by
  unfold tailWord_2461554
  simp only [CollatzResearch.WordTrace]
  refine ⟨22445062531054433199639929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59853500082811821865706477 22445062531054433199639929)
  ·
    refine ⟨16833796898290824899729947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22445062531054433199639929 16833796898290824899729947)
    ·
      refine ⟨25250695347436237349594921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16833796898290824899729947 25250695347436237349594921)
      ·
        refine ⟨18938021510577178012196191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25250695347436237349594921 18938021510577178012196191)
        ·
          refine ⟨28407032265865767018294287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18938021510577178012196191 28407032265865767018294287)
          ·
            refine ⟨42610548398798650527441431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28407032265865767018294287 42610548398798650527441431)
            ·
              refine ⟨63915822598197975791162147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42610548398798650527441431 63915822598197975791162147)
              ·
                refine ⟨95873733897296963686743221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63915822598197975791162147 95873733897296963686743221)
                ·
                  refine ⟨8988162552871590345632177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95873733897296963686743221 8988162552871590345632177)
                  ·
                    refine ⟨6741121914653692759224133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8988162552871590345632177 6741121914653692759224133)
                    ·
                      refine ⟨1263960358997567392354525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6741121914653692759224133 1263960358997567392354525)
                      ·
                        rfl

theorem cell23_2461554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2461554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461554 prefixEnd_2461554 := by exact prefixLift 2461554
  have htrace : WordTrace (prefixWord ++ tailWord_2461554) baseStart_2461554 baseEnd_2461554 := by
    simpa [prefixWord, tailWord_2461554, baseEnd_2461554] using wordTrace_append hprefix tailTrace_2461554
  have hstable : (prefixWord ++ tailWord_2461554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461554).length < 2 ^ (prefixWord ++ tailWord_2461554).sum := by decide
  have hdescent : baseEnd_2461554 < baseStart_2461554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461571 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 4]
def baseStart_2461571 : Nat := 118140960795 + 2461571 * 2 ^ 59
def prefixEnd_2461571 : Nat := 4983230072969 + 3 ^ 40 * 2461571 * 2
def baseEnd_2461571 : Nat := 1263969088168693825841947

theorem tailTrace_2461571 : CollatzResearch.WordTrace tailWord_2461571 prefixEnd_2461571 1263969088168693825841947 := by
  unfold tailWord_2461571
  simp only [CollatzResearch.WordTrace]
  refine ⟨89780870165156144701928567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59853913443437429801285711 89780870165156144701928567)
  ·
    refine ⟨134671305247734217052892851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89780870165156144701928567 134671305247734217052892851)
    ·
      refine ⟨202006957871601325579339277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134671305247734217052892851 202006957871601325579339277)
      ·
        refine ⟨75752609201850497092252229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202006957871601325579339277 75752609201850497092252229)
        ·
          refine ⟨14203614225346968204797293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75752609201850497092252229 14203614225346968204797293)
          ·
            refine ⟨5326355334505113076798985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14203614225346968204797293 5326355334505113076798985)
            ·
              refine ⟨3994766500878834807599239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5326355334505113076798985 3994766500878834807599239)
              ·
                refine ⟨5992149751318252211398859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994766500878834807599239 5992149751318252211398859)
                ·
                  refine ⟨8988224626977378317098289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5992149751318252211398859 8988224626977378317098289)
                  ·
                    refine ⟨6741168470233033737823717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8988224626977378317098289 6741168470233033737823717)
                    ·
                      refine ⟨1263969088168693825841947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6741168470233033737823717 1263969088168693825841947)
                      ·
                        rfl

theorem cell23_2461571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_2461571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461571 prefixEnd_2461571 := by exact prefixLift 2461571
  have htrace : WordTrace (prefixWord ++ tailWord_2461571) baseStart_2461571 baseEnd_2461571 := by
    simpa [prefixWord, tailWord_2461571, baseEnd_2461571] using wordTrace_append hprefix tailTrace_2461571
  have hstable : (prefixWord ++ tailWord_2461571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461571).length < 2 ^ (prefixWord ++ tailWord_2461571).sum := by decide
  have hdescent : baseEnd_2461571 < baseStart_2461571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461575 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 3, 2, 2]
def baseStart_2461575 : Nat := 118140960795 + 2461575 * 2 ^ 59
def prefixEnd_2461575 : Nat := 4983230072969 + 3 ^ 40 * 2461575 * 2
def baseEnd_2461575 : Nat := 1263971142091311810191929

theorem tailTrace_2461575 : CollatzResearch.WordTrace tailWord_2461575 prefixEnd_2461575 1263971142091311810191929 := by
  unfold tailWord_2461575
  simp only [CollatzResearch.WordTrace]
  refine ⟨89781016057141653385074179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59854010704761102256716119 89781016057141653385074179)
  ·
    refine ⟨134671524085712480077611269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89781016057141653385074179 134671524085712480077611269)
    ·
      refine ⟨25250910766071090014552113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134671524085712480077611269 25250910766071090014552113)
      ·
        refine ⟨18938183074553317510914085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25250910766071090014552113 18938183074553317510914085)
        ·
          refine ⟨3550909326478747033296391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18938183074553317510914085 3550909326478747033296391)
          ·
            refine ⟨5326363989718120549944587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3550909326478747033296391 5326363989718120549944587)
            ·
              refine ⟨7989545984577180824916881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5326363989718120549944587 7989545984577180824916881)
              ·
                refine ⟨5992159488432885618687661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7989545984577180824916881 5992159488432885618687661)
                ·
                  refine ⟨2247059808162332107007873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5992159488432885618687661 2247059808162332107007873)
                  ·
                    refine ⟨1685294856121749080255905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2247059808162332107007873 1685294856121749080255905)
                    ·
                      refine ⟨1263971142091311810191929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685294856121749080255905 1263971142091311810191929)
                      ·
                        rfl

theorem cell23_2461575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_2461575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461575 prefixEnd_2461575 := by exact prefixLift 2461575
  have htrace : WordTrace (prefixWord ++ tailWord_2461575) baseStart_2461575 baseEnd_2461575 := by
    simpa [prefixWord, tailWord_2461575, baseEnd_2461575] using wordTrace_append hprefix tailTrace_2461575
  have hstable : (prefixWord ++ tailWord_2461575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461575).length < 2 ^ (prefixWord ++ tailWord_2461575).sum := by decide
  have hdescent : baseEnd_2461575 < baseStart_2461575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461591 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 3]
def baseStart_2461591 : Nat := 118140960795 + 2461591 * 2 ^ 59
def prefixEnd_2461591 : Nat := 4983230072969 + 3 ^ 40 * 2461591 * 2
def baseEnd_2461591 : Nat := 1263979357781783747591855

theorem tailTrace_2461591 : CollatzResearch.WordTrace tailWord_2461591 prefixEnd_2461591 1263979357781783747591855 := by
  unfold tailWord_2461591
  simp only [CollatzResearch.WordTrace]
  refine ⟨89781599625083688117656627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59854399750055792078437751 89781599625083688117656627)
  ·
    refine ⟨134672399437625532176484941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89781599625083688117656627 134672399437625532176484941)
    ·
      refine ⟨50502149789109574566181853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134672399437625532176484941 50502149789109574566181853)
      ·
        refine ⟨18938306170916090462318195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50502149789109574566181853 18938306170916090462318195)
        ·
          refine ⟨28407459256374135693477293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18938306170916090462318195 28407459256374135693477293)
          ·
            refine ⟨10652797221140300885053985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28407459256374135693477293 10652797221140300885053985)
            ·
              refine ⟨7989597915855225663790489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10652797221140300885053985 7989597915855225663790489)
              ·
                refine ⟨5992198436891419247842867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7989597915855225663790489 5992198436891419247842867)
                ·
                  refine ⟨8988297655337128871764301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5992198436891419247842867 8988297655337128871764301)
                  ·
                    refine ⟨3370611620751423326911613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8988297655337128871764301 3370611620751423326911613)
                    ·
                      refine ⟨1263979357781783747591855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3370611620751423326911613 1263979357781783747591855)
                      ·
                        rfl

theorem cell23_2461591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_2461591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461591 prefixEnd_2461591 := by exact prefixLift 2461591
  have htrace : WordTrace (prefixWord ++ tailWord_2461591) baseStart_2461591 baseEnd_2461591 := by
    simpa [prefixWord, tailWord_2461591, baseEnd_2461591] using wordTrace_append hprefix tailTrace_2461591
  have hstable : (prefixWord ++ tailWord_2461591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461591).length < 2 ^ (prefixWord ++ tailWord_2461591).sum := by decide
  have hdescent : baseEnd_2461591 < baseStart_2461591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461592 : List Nat := [2, 1, 2, 6, 1, 2, 2, 1, 1, 1, 4]
def baseStart_2461592 : Nat := 118140960795 + 2461592 * 2 ^ 59
def prefixEnd_2461592 : Nat := 4983230072969 + 3 ^ 40 * 2461592 * 2
def baseEnd_2461592 : Nat := 1263979871262438243679351

theorem tailTrace_2461592 : CollatzResearch.WordTrace tailWord_2461592 prefixEnd_2461592 1263979871262438243679351 := by
  unfold tailWord_2461592
  simp only [CollatzResearch.WordTrace]
  refine ⟨44890818049040032644221515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59854424065386710192295353 44890818049040032644221515)
  ·
    refine ⟨67336227073560048966332273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44890818049040032644221515 67336227073560048966332273)
    ·
      refine ⟨50502170305170036724749205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67336227073560048966332273 50502170305170036724749205)
      ·
        refine ⟨2367289233054845471472619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50502170305170036724749205 2367289233054845471472619)
        ·
          refine ⟨3550933849582268207208929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367289233054845471472619 3550933849582268207208929)
          ·
            refine ⟨2663200387186701155406697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3550933849582268207208929 2663200387186701155406697)
            ·
              refine ⟨1997400290390025866555023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2663200387186701155406697 1997400290390025866555023)
              ·
                refine ⟨2996100435585038799832535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1997400290390025866555023 2996100435585038799832535)
                ·
                  refine ⟨4494150653377558199748803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996100435585038799832535 4494150653377558199748803)
                  ·
                    refine ⟨6741225980066337299623205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4494150653377558199748803 6741225980066337299623205)
                    ·
                      refine ⟨1263979871262438243679351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6741225980066337299623205 1263979871262438243679351)
                      ·
                        rfl

theorem cell23_2461592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_2461592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461592 prefixEnd_2461592 := by exact prefixLift 2461592
  have htrace : WordTrace (prefixWord ++ tailWord_2461592) baseStart_2461592 baseEnd_2461592 := by
    simpa [prefixWord, tailWord_2461592, baseEnd_2461592] using wordTrace_append hprefix tailTrace_2461592
  have hstable : (prefixWord ++ tailWord_2461592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461592).length < 2 ^ (prefixWord ++ tailWord_2461592).sum := by decide
  have hdescent : baseEnd_2461592 < baseStart_2461592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461598 : List Nat := [4, 3, 1, 3, 1, 1, 10]
def baseStart_2461598 : Nat := 118140960795 + 2461598 * 2 ^ 59
def prefixEnd_2461598 : Nat := 4983230072969 + 3 ^ 40 * 2461598 * 2
def baseEnd_2461598 : Nat := 15604727804276113829683

theorem tailTrace_2461598 : CollatzResearch.WordTrace tailWord_2461598 prefixEnd_2461598 15604727804276113829683 := by
  unfold tailWord_2461598
  simp only [CollatzResearch.WordTrace]
  refine ⟨11222731867007291039145181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59854569957372218875440965 11222731867007291039145181)
  ·
    refine ⟨4208524450127734139679443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11222731867007291039145181 4208524450127734139679443)
    ·
      refine ⟨6312786675191601209519165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4208524450127734139679443 6312786675191601209519165)
      ·
        refine ⟨2367295003196850453569687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6312786675191601209519165 2367295003196850453569687)
        ·
          refine ⟨3550942504795275680354531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367295003196850453569687 3550942504795275680354531)
          ·
            refine ⟨5326413757192913520531797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3550942504795275680354531 5326413757192913520531797)
            ·
              refine ⟨15604727804276113829683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5326413757192913520531797 15604727804276113829683)
              ·
                rfl

theorem cell23_2461598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 10].length) (baseStart_2461598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461598 prefixEnd_2461598 := by exact prefixLift 2461598
  have htrace : WordTrace (prefixWord ++ tailWord_2461598) baseStart_2461598 baseEnd_2461598 := by
    simpa [prefixWord, tailWord_2461598, baseEnd_2461598] using wordTrace_append hprefix tailTrace_2461598
  have hstable : (prefixWord ++ tailWord_2461598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461598).length < 2 ^ (prefixWord ++ tailWord_2461598).sum := by decide
  have hdescent : baseEnd_2461598 < baseStart_2461598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461602 : List Nat := [3, 3, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_2461602 : Nat := 118140960795 + 2461602 * 2 ^ 59
def prefixEnd_2461602 : Nat := 4983230072969 + 3 ^ 40 * 2461602 * 2
def baseEnd_2461602 : Nat := 421328335356327734851435

theorem tailTrace_2461602 : CollatzResearch.WordTrace tailWord_2461602 prefixEnd_2461602 421328335356327734851435 := by
  unfold tailWord_2461602
  simp only [CollatzResearch.WordTrace]
  refine ⟨22445500207010959249076765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59854667218695891330871373 22445500207010959249076765)
  ·
    refine ⟨8417062577629109718403787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22445500207010959249076765 8417062577629109718403787)
    ·
      refine ⟨12625593866443664577605681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8417062577629109718403787 12625593866443664577605681)
      ·
        refine ⟨9469195399832748433204261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12625593866443664577605681 9469195399832748433204261)
        ·
          refine ⟨1775474137468640331225799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9469195399832748433204261 1775474137468640331225799)
          ·
            refine ⟨2663211206202960496838699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775474137468640331225799 2663211206202960496838699)
            ·
              refine ⟨3994816809304440745258049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663211206202960496838699 3994816809304440745258049)
              ·
                refine ⟨2996112606978330558943537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3994816809304440745258049 2996112606978330558943537)
                ·
                  refine ⟨2247084455233747919207653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2996112606978330558943537 2247084455233747919207653)
                  ·
                    refine ⟨421328335356327734851435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2247084455233747919207653 421328335356327734851435)
                    ·
                      rfl

theorem cell23_2461602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_2461602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461602 prefixEnd_2461602 := by exact prefixLift 2461602
  have htrace : WordTrace (prefixWord ++ tailWord_2461602) baseStart_2461602 baseEnd_2461602 := by
    simpa [prefixWord, tailWord_2461602, baseEnd_2461602] using wordTrace_append hprefix tailTrace_2461602
  have hstable : (prefixWord ++ tailWord_2461602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461602).length < 2 ^ (prefixWord ++ tailWord_2461602).sum := by decide
  have hdescent : baseEnd_2461602 < baseStart_2461602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461624 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 2, 6]
def baseStart_2461624 : Nat := 118140960795 + 2461624 * 2 ^ 59
def prefixEnd_2461624 : Nat := 4983230072969 + 3 ^ 40 * 2461624 * 2
def baseEnd_2461624 : Nat := 421332100881127372826401

theorem tailTrace_2461624 : CollatzResearch.WordTrace tailWord_2461624 prefixEnd_2461624 421332100881127372826401 := by
  unfold tailWord_2461624
  simp only [CollatzResearch.WordTrace]
  refine ⟨44891401616982067376803963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59855202155976089835738617 44891401616982067376803963)
  ·
    refine ⟨67337102425473101065205945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44891401616982067376803963 67337102425473101065205945)
    ·
      refine ⟨50502826819104825798904459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67337102425473101065205945 50502826819104825798904459)
      ·
        refine ⟨75754240228657238698356689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50502826819104825798904459 75754240228657238698356689)
        ·
          refine ⟨56815680171492929023767517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75754240228657238698356689 56815680171492929023767517)
          ·
            refine ⟨21305880064309848383912819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56815680171492929023767517 21305880064309848383912819)
            ·
              refine ⟨31958820096464772575869229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21305880064309848383912819 31958820096464772575869229)
              ·
                refine ⟨11984557536174289715950961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31958820096464772575869229 11984557536174289715950961)
                ·
                  refine ⟨8988418152130717286963221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11984557536174289715950961 8988418152130717286963221)
                  ·
                    refine ⟨421332100881127372826401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8988418152130717286963221 421332100881127372826401)
                    ·
                      rfl

theorem cell23_2461624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_2461624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461624 prefixEnd_2461624 := by exact prefixLift 2461624
  have htrace : WordTrace (prefixWord ++ tailWord_2461624) baseStart_2461624 baseEnd_2461624 := by
    simpa [prefixWord, tailWord_2461624, baseEnd_2461624] using wordTrace_append hprefix tailTrace_2461624
  have hstable : (prefixWord ++ tailWord_2461624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461624).length < 2 ^ (prefixWord ++ tailWord_2461624).sum := by decide
  have hdescent : baseEnd_2461624 < baseStart_2461624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461625 : List Nat := [1, 2, 1, 4, 2, 1, 5, 1, 2, 1, 3]
def baseStart_2461625 : Nat := 118140960795 + 2461625 * 2 ^ 59
def prefixEnd_2461625 : Nat := 4983230072969 + 3 ^ 40 * 2461625 * 2
def baseEnd_2461625 : Nat := 1263996816124036614566699

theorem tailTrace_2461625 : CollatzResearch.WordTrace tailWord_2461625 prefixEnd_2461625 1263996816124036614566699 := by
  unfold tailWord_2461625
  simp only [CollatzResearch.WordTrace]
  refine ⟨89782839706960511924394329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59855226471307007949596219 89782839706960511924394329)
  ·
    refine ⟨67337129780220383943295747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89782839706960511924394329 67337129780220383943295747)
    ·
      refine ⟨101005694670330575914943621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67337129780220383943295747 101005694670330575914943621)
      ·
        refine ⟨18938567750686982984051929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101005694670330575914943621 18938567750686982984051929)
        ·
          refine ⟨14203925813015237238038947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18938567750686982984051929 14203925813015237238038947)
          ·
            refine ⟨21305888719522855857058421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14203925813015237238038947 21305888719522855857058421)
            ·
              refine ⟨1997427067455267736599227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21305888719522855857058421 1997427067455267736599227)
              ·
                refine ⟨2996140601182901604898841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1997427067455267736599227 2996140601182901604898841)
                ·
                  refine ⟨2247105450887176203674131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2996140601182901604898841 2247105450887176203674131)
                  ·
                    refine ⟨3370658176330764305511197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2247105450887176203674131 3370658176330764305511197)
                    ·
                      refine ⟨1263996816124036614566699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3370658176330764305511197 1263996816124036614566699)
                      ·
                        rfl

theorem cell23_2461625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_2461625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461625 prefixEnd_2461625 := by exact prefixLift 2461625
  have htrace : WordTrace (prefixWord ++ tailWord_2461625) baseStart_2461625 baseEnd_2461625 := by
    simpa [prefixWord, tailWord_2461625, baseEnd_2461625] using wordTrace_append hprefix tailTrace_2461625
  have hstable : (prefixWord ++ tailWord_2461625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461625).length < 2 ^ (prefixWord ++ tailWord_2461625).sum := by decide
  have hdescent : baseEnd_2461625 < baseStart_2461625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461648 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 4, 2, 2]
def baseStart_2461648 : Nat := 118140960795 + 2461648 * 2 ^ 59
def prefixEnd_2461648 : Nat := 4983230072969 + 3 ^ 40 * 2461648 * 2
def baseEnd_2461648 : Nat := 1264008626179090024579093

theorem tailTrace_2461648 : CollatzResearch.WordTrace tailWord_2461648 prefixEnd_2461648 1264008626179090024579093 := by
  unfold tailWord_2461648
  simp only [CollatzResearch.WordTrace]
  refine ⟨44891839292938593426240799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59855785723918124568321065 44891839292938593426240799)
  ·
    refine ⟨67337758939407890139361199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44891839292938593426240799 67337758939407890139361199)
    ·
      refine ⟨101006638409111835209041799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67337758939407890139361199 101006638409111835209041799)
      ·
        refine ⟨151509957613667752813562699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101006638409111835209041799 151509957613667752813562699)
        ·
          refine ⟨227264936420501629220344049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151509957613667752813562699 227264936420501629220344049)
          ·
            refine ⟨170448702315376221915258037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227264936420501629220344049 170448702315376221915258037)
            ·
              refine ⟨15979565842066520804555441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170448702315376221915258037 15979565842066520804555441)
              ·
                refine ⟨11984674381549890603416581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15979565842066520804555441 11984674381549890603416581)
                ·
                  refine ⟨2247126446540604488140609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11984674381549890603416581 2247126446540604488140609)
                  ·
                    refine ⟨1685344834905453366105457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2247126446540604488140609 1685344834905453366105457)
                    ·
                      refine ⟨1264008626179090024579093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685344834905453366105457 1264008626179090024579093)
                      ·
                        rfl

theorem cell23_2461648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 4, 2, 2].length) (baseStart_2461648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461648 prefixEnd_2461648 := by exact prefixLift 2461648
  have htrace : WordTrace (prefixWord ++ tailWord_2461648) baseStart_2461648 baseEnd_2461648 := by
    simpa [prefixWord, tailWord_2461648, baseEnd_2461648] using wordTrace_append hprefix tailTrace_2461648
  have hstable : (prefixWord ++ tailWord_2461648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461648).length < 2 ^ (prefixWord ++ tailWord_2461648).sum := by decide
  have hdescent : baseEnd_2461648 < baseStart_2461648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461701 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 2, 5]
def baseStart_2461701 : Nat := 118140960795 + 2461701 * 2 ^ 59
def prefixEnd_2461701 : Nat := 4983230072969 + 3 ^ 40 * 2461701 * 2
def baseEnd_2461701 : Nat := 421345280217926105738783

theorem tailTrace_2461701 : CollatzResearch.WordTrace tailWord_2461701 prefixEnd_2461701 421345280217926105738783 := by
  unfold tailWord_2461701
  simp only [CollatzResearch.WordTrace]
  refine ⟨89785611654685176904160957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59857074436456784602773971 89785611654685176904160957)
  ·
    refine ⟨33669604370506941339060359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89785611654685176904160957 33669604370506941339060359)
    ·
      refine ⟨50504406555760412008590539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33669604370506941339060359 50504406555760412008590539)
      ·
        refine ⟨75756609833640618012885809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50504406555760412008590539 75756609833640618012885809)
        ·
          refine ⟨56817457375230463509664357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75756609833640618012885809 56817457375230463509664357)
          ·
            refine ⟨10653273257855711908062067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56817457375230463509664357 10653273257855711908062067)
            ·
              refine ⟨15979909886783567862093101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10653273257855711908062067 15979909886783567862093101)
              ·
                refine ⟨5992466207543837948284913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15979909886783567862093101 5992466207543837948284913)
                ·
                  refine ⟨4494349655657878461213685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5992466207543837948284913 4494349655657878461213685)
                  ·
                    refine ⟨421345280217926105738783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4494349655657878461213685 421345280217926105738783)
                    ·
                      rfl

theorem cell23_2461701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_2461701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461701 prefixEnd_2461701 := by exact prefixLift 2461701
  have htrace : WordTrace (prefixWord ++ tailWord_2461701) baseStart_2461701 baseEnd_2461701 := by
    simpa [prefixWord, tailWord_2461701, baseEnd_2461701] using wordTrace_append hprefix tailTrace_2461701
  have hstable : (prefixWord ++ tailWord_2461701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461701).length < 2 ^ (prefixWord ++ tailWord_2461701).sum := by decide
  have hdescent : baseEnd_2461701 < baseStart_2461701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461716 : List Nat := [2, 4, 3, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_2461716 : Nat := 118140960795 + 2461716 * 2 ^ 59
def prefixEnd_2461716 : Nat := 4983230072969 + 3 ^ 40 * 2461716 * 2
def baseEnd_2461716 : Nat := 1264043542863595758528781

theorem tailTrace_2461716 : CollatzResearch.WordTrace tailWord_2461716 prefixEnd_2461716 1264043542863595758528781 := by
  unfold tailWord_2461716
  simp only [CollatzResearch.WordTrace]
  refine ⟨44893079374815417232978501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59857439166420556310638001 44893079374815417232978501)
  ·
    refine ⟨8417452382777890731183469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44893079374815417232978501 8417452382777890731183469)
    ·
      refine ⟨3156544643541709024193801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8417452382777890731183469 3156544643541709024193801)
      ·
        refine ⟨2367408482656281768145351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3156544643541709024193801 2367408482656281768145351)
        ·
          refine ⟨3551112723984422652218027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367408482656281768145351 3551112723984422652218027)
          ·
            refine ⟨5326669085976633978327041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3551112723984422652218027 5326669085976633978327041)
            ·
              refine ⟨3995001814482475483745281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5326669085976633978327041 3995001814482475483745281)
              ·
                refine ⟨2996251360861856612808961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3995001814482475483745281 2996251360861856612808961)
                ·
                  refine ⟨2247188520646392459606721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2996251360861856612808961 2247188520646392459606721)
                  ·
                    refine ⟨1685391390484794344705041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2247188520646392459606721 1685391390484794344705041)
                    ·
                      refine ⟨1264043542863595758528781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685391390484794344705041 1264043542863595758528781)
                      ·
                        rfl

theorem cell23_2461716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_2461716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461716 prefixEnd_2461716 := by exact prefixLift 2461716
  have htrace : WordTrace (prefixWord ++ tailWord_2461716) baseStart_2461716 baseEnd_2461716 := by
    simpa [prefixWord, tailWord_2461716, baseEnd_2461716] using wordTrace_append hprefix tailTrace_2461716
  have hstable : (prefixWord ++ tailWord_2461716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461716).length < 2 ^ (prefixWord ++ tailWord_2461716).sum := by decide
  have hdescent : baseEnd_2461716 < baseStart_2461716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461778 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 8]
def baseStart_2461778 : Nat := 118140960795 + 2461778 * 2 ^ 59
def prefixEnd_2461778 : Nat := 4983230072969 + 3 ^ 40 * 2461778 * 2
def baseEnd_2461778 : Nat := 140452819851574946217055

theorem tailTrace_2461778 : CollatzResearch.WordTrace tailWord_2461778 prefixEnd_2461778 140452819851574946217055 := by
  unfold tailWord_2461778
  simp only [CollatzResearch.WordTrace]
  refine ⟨22447105018851554763678497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59858946716937479369809325 22447105018851554763678497)
  ·
    refine ⟨16835328764138666072758873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22447105018851554763678497 16835328764138666072758873)
    ·
      refine ⟨12626496573103999554569155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16835328764138666072758873 12626496573103999554569155)
      ·
        refine ⟨18939744859655999331853733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12626496573103999554569155 18939744859655999331853733)
        ·
          refine ⟨3551202161185499874722575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18939744859655999331853733 3551202161185499874722575)
          ·
            refine ⟨5326803241778249812083863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3551202161185499874722575 5326803241778249812083863)
            ·
              refine ⟨7990204862667374718125795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5326803241778249812083863 7990204862667374718125795)
              ·
                refine ⟨11985307294001062077188693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7990204862667374718125795 11985307294001062077188693)
                ·
                  refine ⟨140452819851574946217055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11985307294001062077188693 140452819851574946217055)
                  ·
                    rfl

theorem cell23_2461778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_2461778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461778 prefixEnd_2461778 := by exact prefixLift 2461778
  have htrace : WordTrace (prefixWord ++ tailWord_2461778) baseStart_2461778 baseEnd_2461778 := by
    simpa [prefixWord, tailWord_2461778, baseEnd_2461778] using wordTrace_append hprefix tailTrace_2461778
  have hstable : (prefixWord ++ tailWord_2461778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461778).length < 2 ^ (prefixWord ++ tailWord_2461778).sum := by decide
  have hdescent : baseEnd_2461778 < baseStart_2461778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461781 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_2461781 : Nat := 118140960795 + 2461781 * 2 ^ 59
def prefixEnd_2461781 : Nat := 4983230072969 + 3 ^ 40 * 2461781 * 2
def baseEnd_2461781 : Nat := 1264076919106138004215981

theorem tailTrace_2461781 : CollatzResearch.WordTrace tailWord_2461781 prefixEnd_2461781 1264076919106138004215981 := by
  unfold tailWord_2461781
  simp only [CollatzResearch.WordTrace]
  refine ⟨89788529494395350567073197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59859019662930233711382131 89788529494395350567073197)
  ·
    refine ⟨33670698560398256462652449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89788529494395350567073197 33670698560398256462652449)
    ·
      refine ⟨25253023920298692346989337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33670698560398256462652449 25253023920298692346989337)
      ·
        refine ⟨18939767940224019260242003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25253023920298692346989337 18939767940224019260242003)
        ·
          refine ⟨28409651910336028890363005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18939767940224019260242003 28409651910336028890363005)
          ·
            refine ⟨10653619466376010833886127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28409651910336028890363005 10653619466376010833886127)
            ·
              refine ⟨15980429199564016250829191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10653619466376010833886127 15980429199564016250829191)
              ·
                refine ⟨23970643799346024376243787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15980429199564016250829191 23970643799346024376243787)
                ·
                  refine ⟨35955965699019036564365681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23970643799346024376243787 35955965699019036564365681)
                  ·
                    refine ⟨26966974274264277423274261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35955965699019036564365681 26966974274264277423274261)
                    ·
                      refine ⟨1264076919106138004215981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26966974274264277423274261 1264076919106138004215981)
                      ·
                        rfl

theorem cell23_2461781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_2461781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461781 prefixEnd_2461781 := by exact prefixLift 2461781
  have htrace : WordTrace (prefixWord ++ tailWord_2461781) baseStart_2461781 baseEnd_2461781 := by
    simpa [prefixWord, tailWord_2461781, baseEnd_2461781] using wordTrace_append hprefix tailTrace_2461781
  have hstable : (prefixWord ++ tailWord_2461781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461781).length < 2 ^ (prefixWord ++ tailWord_2461781).sum := by decide
  have hdescent : baseEnd_2461781 < baseStart_2461781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461782 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2461782 : Nat := 118140960795 + 2461782 * 2 ^ 59
def prefixEnd_2461782 : Nat := 4983230072969 + 3 ^ 40 * 2461782 * 2
def baseEnd_2461782 : Nat := 421359144195597500101159

theorem tailTrace_2461782 : CollatzResearch.WordTrace tailWord_2461782 prefixEnd_2461782 421359144195597500101159 := by
  unfold tailWord_2461782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5611785372961982983616225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59859043978261151825239733 5611785372961982983616225)
  ·
    refine ⟨4208839029721487237712169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5611785372961982983616225 4208839029721487237712169)
    ·
      refine ⟨3156629272291115428284127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4208839029721487237712169 3156629272291115428284127)
      ·
        refine ⟨4734943908436673142426191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3156629272291115428284127 4734943908436673142426191)
        ·
          refine ⟨7102415862655009713639287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4734943908436673142426191 7102415862655009713639287)
          ·
            refine ⟨10653623793982514570458931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7102415862655009713639287 10653623793982514570458931)
            ·
              refine ⟨15980435690973771855688397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10653623793982514570458931 15980435690973771855688397)
              ·
                refine ⟨5992663384115164445883149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15980435690973771855688397 5992663384115164445883149)
                ·
                  refine ⟨2247248769043186667206181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5992663384115164445883149 2247248769043186667206181)
                  ·
                    refine ⟨421359144195597500101159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2247248769043186667206181 421359144195597500101159)
                    ·
                      rfl

theorem cell23_2461782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2461782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461782 prefixEnd_2461782 := by exact prefixLift 2461782
  have htrace : WordTrace (prefixWord ++ tailWord_2461782) baseStart_2461782 baseEnd_2461782 := by
    simpa [prefixWord, tailWord_2461782, baseEnd_2461782] using wordTrace_append hprefix tailTrace_2461782
  have hstable : (prefixWord ++ tailWord_2461782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461782).length < 2 ^ (prefixWord ++ tailWord_2461782).sum := by decide
  have hdescent : baseEnd_2461782 < baseStart_2461782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461791 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 3, 5]
def baseStart_2461791 : Nat := 118140960795 + 2461791 * 2 ^ 59
def prefixEnd_2461791 : Nat := 4983230072969 + 3 ^ 40 * 2461791 * 2
def baseEnd_2461791 : Nat := 421360684637560988363645

theorem tailTrace_2461791 : CollatzResearch.WordTrace tailWord_2461791 prefixEnd_2461791 421360684637560988363645 := by
  unfold tailWord_2461791
  simp only [CollatzResearch.WordTrace]
  refine ⟨89788894224359122274937227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59859262816239414849958151 89788894224359122274937227)
  ·
    refine ⟨134683341336538683412405841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89788894224359122274937227 134683341336538683412405841)
    ·
      refine ⟨101012506002404012559304381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134683341336538683412405841 101012506002404012559304381)
      ·
        refine ⟨37879689750901504709739143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101012506002404012559304381 37879689750901504709739143)
        ·
          refine ⟨56819534626352257064608715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37879689750901504709739143 56819534626352257064608715)
          ·
            refine ⟨85229301939528385596913073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56819534626352257064608715 85229301939528385596913073)
            ·
              refine ⟨63921976454646289197684805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85229301939528385596913073 63921976454646289197684805)
              ·
                refine ⟨11985370585246179224565901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63921976454646289197684805 11985370585246179224565901)
                ·
                  refine ⟨4494513969467317209212213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11985370585246179224565901 4494513969467317209212213)
                  ·
                    refine ⟨421360684637560988363645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4494513969467317209212213 421360684637560988363645)
                    ·
                      rfl

theorem cell23_2461791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 5].length) (baseStart_2461791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461791 prefixEnd_2461791 := by exact prefixLift 2461791
  have htrace : WordTrace (prefixWord ++ tailWord_2461791) baseStart_2461791 baseEnd_2461791 := by
    simpa [prefixWord, tailWord_2461791, baseEnd_2461791] using wordTrace_append hprefix tailTrace_2461791
  have hstable : (prefixWord ++ tailWord_2461791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461791).length < 2 ^ (prefixWord ++ tailWord_2461791).sum := by decide
  have hdescent : baseEnd_2461791 < baseStart_2461791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461805 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_2461805 : Nat := 118140960795 + 2461805 * 2 ^ 59
def prefixEnd_2461805 : Nat := 4983230072969 + 3 ^ 40 * 2461805 * 2
def baseEnd_2461805 : Nat := 1264089242641845910315871

theorem tailTrace_2461805 : CollatzResearch.WordTrace tailWord_2461805 prefixEnd_2461805 1264089242641845910315871 := by
  unfold tailWord_2461805
  simp only [CollatzResearch.WordTrace]
  refine ⟨89789404846308402665946869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59859603230872268443964579 89789404846308402665946869)
  ·
    refine ⟨8417756704341412749932519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89789404846308402665946869 8417756704341412749932519)
    ·
      refine ⟨12626635056512119124898779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8417756704341412749932519 12626635056512119124898779)
      ·
        refine ⟨18939952584768178687348169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12626635056512119124898779 18939952584768178687348169)
        ·
          refine ⟨14204964438576134015511127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18939952584768178687348169 14204964438576134015511127)
          ·
            refine ⟨21307446657864201023266691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14204964438576134015511127 21307446657864201023266691)
            ·
              refine ⟨31961169986796301534900037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21307446657864201023266691 31961169986796301534900037)
              ·
                refine ⟨5992719372524306537793757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31961169986796301534900037 5992719372524306537793757)
                ·
                  refine ⟨2247269764696614951672659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5992719372524306537793757 2247269764696614951672659)
                  ·
                    refine ⟨3370904647044922427508989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2247269764696614951672659 3370904647044922427508989)
                    ·
                      refine ⟨1264089242641845910315871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3370904647044922427508989 1264089242641845910315871)
                      ·
                        rfl

theorem cell23_2461805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_2461805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461805 prefixEnd_2461805 := by exact prefixLift 2461805
  have htrace : WordTrace (prefixWord ++ tailWord_2461805) baseStart_2461805 baseEnd_2461805 := by
    simpa [prefixWord, tailWord_2461805, baseEnd_2461805] using wordTrace_append hprefix tailTrace_2461805
  have hstable : (prefixWord ++ tailWord_2461805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461805).length < 2 ^ (prefixWord ++ tailWord_2461805).sum := by decide
  have hdescent : baseEnd_2461805 < baseStart_2461805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461808 : List Nat := [2, 1, 1, 1, 5, 2, 1, 4, 1, 5]
def baseStart_2461808 : Nat := 118140960795 + 2461808 * 2 ^ 59
def prefixEnd_2461808 : Nat := 4983230072969 + 3 ^ 40 * 2461808 * 2
def baseEnd_2461808 : Nat := 421363594361269799526119

theorem tailTrace_2461808 : CollatzResearch.WordTrace tailWord_2461808 prefixEnd_2461808 421363594361269799526119 := by
  unfold tailWord_2461808
  simp only [CollatzResearch.WordTrace]
  refine ⟨44894757132648767089153039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59859676176865022785537385 44894757132648767089153039)
  ·
    refine ⟨67342135698973150633729559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44894757132648767089153039 67342135698973150633729559)
    ·
      refine ⟨101013203548459725950594339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67342135698973150633729559 101013203548459725950594339)
      ·
        refine ⟨151519805322689588925891509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101013203548459725950594339 151519805322689588925891509)
        ·
          refine ⟨14204981749002148961802329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151519805322689588925891509 14204981749002148961802329)
          ·
            refine ⟨10653736311751611721351747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14204981749002148961802329 10653736311751611721351747)
            ·
              refine ⟨15980604467627417582027621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10653736311751611721351747 15980604467627417582027621)
              ·
                refine ⟨2996363337680140796630179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15980604467627417582027621 2996363337680140796630179)
                ·
                  refine ⟨4494545006520211194945269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996363337680140796630179 4494545006520211194945269)
                  ·
                    refine ⟨421363594361269799526119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4494545006520211194945269 421363594361269799526119)
                    ·
                      rfl

theorem cell23_2461808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 1, 5].length) (baseStart_2461808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461808 prefixEnd_2461808 := by exact prefixLift 2461808
  have htrace : WordTrace (prefixWord ++ tailWord_2461808) baseStart_2461808 baseEnd_2461808 := by
    simpa [prefixWord, tailWord_2461808, baseEnd_2461808] using wordTrace_append hprefix tailTrace_2461808
  have hstable : (prefixWord ++ tailWord_2461808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461808).length < 2 ^ (prefixWord ++ tailWord_2461808).sum := by decide
  have hdescent : baseEnd_2461808 < baseStart_2461808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461832 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 2, 3, 2]
def baseStart_2461832 : Nat := 118140960795 + 2461832 * 2 ^ 59
def prefixEnd_2461832 : Nat := 4983230072969 + 3 ^ 40 * 2461832 * 2
def baseEnd_2461832 : Nat := 1264103106619517304678247

theorem tailTrace_2461832 : CollatzResearch.WordTrace tailWord_2461832 prefixEnd_2461832 1264103106619517304678247 := by
  unfold tailWord_2461832
  simp only [CollatzResearch.WordTrace]
  refine ⟨44895194808605293138589875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59860259744807057518119833 44895194808605293138589875)
  ·
    refine ⟨67342792212907939707884813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44895194808605293138589875 67342792212907939707884813)
    ·
      refine ⟨25253547079840477390456805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67342792212907939707884813 25253547079840477390456805)
      ·
        refine ⟨4735040077470089510710651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25253547079840477390456805 4735040077470089510710651)
        ·
          refine ⟨7102560116205134266065977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4735040077470089510710651 7102560116205134266065977)
          ·
            refine ⟨5326920087153850699549483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7102560116205134266065977 5326920087153850699549483)
            ·
              refine ⟨7990380130730776049324225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5326920087153850699549483 7990380130730776049324225)
              ·
                refine ⟨5992785098048082036993169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7990380130730776049324225 5992785098048082036993169)
                ·
                  refine ⟨4494588823536061527744877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5992785098048082036993169 4494588823536061527744877)
                  ·
                    refine ⟨1685470808826023072904329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4494588823536061527744877 1685470808826023072904329)
                    ·
                      refine ⟨1264103106619517304678247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685470808826023072904329 1264103106619517304678247)
                      ·
                        rfl

theorem cell23_2461832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_2461832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461832 prefixEnd_2461832 := by exact prefixLift 2461832
  have htrace : WordTrace (prefixWord ++ tailWord_2461832) baseStart_2461832 baseEnd_2461832 := by
    simpa [prefixWord, tailWord_2461832, baseEnd_2461832] using wordTrace_append hprefix tailTrace_2461832
  have hstable : (prefixWord ++ tailWord_2461832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461832).length < 2 ^ (prefixWord ++ tailWord_2461832).sum := by decide
  have hdescent : baseEnd_2461832 < baseStart_2461832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461846 : List Nat := [5, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2461846 : Nat := 118140960795 + 2461846 * 2 ^ 59
def prefixEnd_2461846 : Nat := 4983230072969 + 3 ^ 40 * 2461846 * 2
def baseEnd_2461846 : Nat := 140456699483186694433687

theorem tailTrace_2461846 : CollatzResearch.WordTrace tailWord_2461846 prefixEnd_2461846 140456699483186694433687 := by
  unfold tailWord_2461846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5611931264947491666761837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59860600159439911112126261 5611931264947491666761837)
  ·
    refine ⟨2104474224355309375035689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5611931264947491666761837 2104474224355309375035689)
    ·
      refine ⟨1578355668266482031276767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2104474224355309375035689 1578355668266482031276767)
      ·
        refine ⟨2367533502399723046915151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578355668266482031276767 2367533502399723046915151)
        ·
          refine ⟨3551300253599584570372727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367533502399723046915151 3551300253599584570372727)
          ·
            refine ⟨5326950380399376855559091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3551300253599584570372727 5326950380399376855559091)
            ·
              refine ⟨7990425570599065283338637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5326950380399376855559091 7990425570599065283338637)
              ·
                refine ⟨2996409588974649481251989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7990425570599065283338637 2996409588974649481251989)
                ·
                  refine ⟨140456699483186694433687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2996409588974649481251989 140456699483186694433687)
                  ·
                    rfl

theorem cell23_2461846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2461846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461846 prefixEnd_2461846 := by exact prefixLift 2461846
  have htrace : WordTrace (prefixWord ++ tailWord_2461846) baseStart_2461846 baseEnd_2461846 := by
    simpa [prefixWord, tailWord_2461846, baseEnd_2461846] using wordTrace_append hprefix tailTrace_2461846
  have hstable : (prefixWord ++ tailWord_2461846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461846).length < 2 ^ (prefixWord ++ tailWord_2461846).sum := by decide
  have hdescent : baseEnd_2461846 < baseStart_2461846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461889 : List Nat := [1, 2, 6, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2461889 : Nat := 118140960795 + 2461889 * 2 ^ 59
def prefixEnd_2461889 : Nat := 4983230072969 + 3 ^ 40 * 2461889 * 2
def baseEnd_2461889 : Nat := 421377458338941193888495

theorem tailTrace_2461889 : CollatzResearch.WordTrace tailWord_2461889 prefixEnd_2461889 421377458338941193888495 := by
  unfold tailWord_2461889
  simp only [CollatzResearch.WordTrace]
  refine ⟨89792468578004085012004721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59861645718669390008003147 89792468578004085012004721)
  ·
    refine ⟨67344351433503063759003541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89792468578004085012004721 67344351433503063759003541)
    ·
      refine ⟨3156766473445456113703291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67344351433503063759003541 3156766473445456113703291)
      ·
        refine ⟨4735149710168184170554937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3156766473445456113703291 4735149710168184170554937)
        ·
          refine ⟨3551362282626138127916203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4735149710168184170554937 3551362282626138127916203)
          ·
            refine ⟨5327043423939207191874305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3551362282626138127916203 5327043423939207191874305)
            ·
              refine ⟨3995282567954405393905729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5327043423939207191874305 3995282567954405393905729)
              ·
                refine ⟨2996461925965804045429297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3995282567954405393905729 2996461925965804045429297)
                ·
                  refine ⟨2247346444474353034071973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2996461925965804045429297 2247346444474353034071973)
                  ·
                    refine ⟨421377458338941193888495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2247346444474353034071973 421377458338941193888495)
                    ·
                      rfl

theorem cell23_2461889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2461889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461889 prefixEnd_2461889 := by exact prefixLift 2461889
  have htrace : WordTrace (prefixWord ++ tailWord_2461889) baseStart_2461889 baseEnd_2461889 := by
    simpa [prefixWord, tailWord_2461889, baseEnd_2461889] using wordTrace_append hprefix tailTrace_2461889
  have hstable : (prefixWord ++ tailWord_2461889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461889).length < 2 ^ (prefixWord ++ tailWord_2461889).sum := by decide
  have hdescent : baseEnd_2461889 < baseStart_2461889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461890 : List Nat := [3, 5, 1, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_2461890 : Nat := 118140960795 + 2461890 * 2 ^ 59
def prefixEnd_2461890 : Nat := 4983230072969 + 3 ^ 40 * 2461890 * 2
def baseEnd_2461890 : Nat := 1264132888497478077752981

theorem tailTrace_2461890 : CollatzResearch.WordTrace tailWord_2461890 prefixEnd_2461890 1264132888497478077752981 := by
  unfold tailWord_2461890
  simp only [CollatzResearch.WordTrace]
  refine ⟨22448126262750115545697781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59861670034000308121860749 22448126262750115545697781)
  ·
    refine ⟨2104511837132823332409167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22448126262750115545697781 2104511837132823332409167)
    ·
      refine ⟨3156767755699234998613751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2104511837132823332409167 3156767755699234998613751)
      ·
        refine ⟨4735151633548852497920627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3156767755699234998613751 4735151633548852497920627)
        ·
          refine ⟨7102727450323278746880941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4735151633548852497920627 7102727450323278746880941)
          ·
            refine ⟨2663522793871229530080353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7102727450323278746880941 2663522793871229530080353)
            ·
              refine ⟨1997642095403422147560265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2663522793871229530080353 1997642095403422147560265)
              ·
                refine ⟨1498231571552566610670199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1997642095403422147560265 1498231571552566610670199)
                ·
                  refine ⟨2247347357328849916005299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498231571552566610670199 2247347357328849916005299)
                  ·
                    refine ⟨3371021035993274874007949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2247347357328849916005299 3371021035993274874007949)
                    ·
                      refine ⟨1264132888497478077752981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3371021035993274874007949 1264132888497478077752981)
                      ·
                        rfl

theorem cell23_2461890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_2461890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461890 prefixEnd_2461890 := by exact prefixLift 2461890
  have htrace : WordTrace (prefixWord ++ tailWord_2461890) baseStart_2461890 baseEnd_2461890 := by
    simpa [prefixWord, tailWord_2461890, baseEnd_2461890] using wordTrace_append hprefix tailTrace_2461890
  have hstable : (prefixWord ++ tailWord_2461890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461890).length < 2 ^ (prefixWord ++ tailWord_2461890).sum := by decide
  have hdescent : baseEnd_2461890 < baseStart_2461890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461891 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 5]
def baseStart_2461891 : Nat := 118140960795 + 2461891 * 2 ^ 59
def prefixEnd_2461891 : Nat := 4983230072969 + 3 ^ 40 * 2461891 * 2
def baseEnd_2461891 : Nat := 1264133401978132573840475

theorem tailTrace_2461891 : CollatzResearch.WordTrace tailWord_2461891 prefixEnd_2461891 1264133401978132573840475 := by
  unfold tailWord_2461891
  simp only [CollatzResearch.WordTrace]
  refine ⟨89792541523996839353577527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59861694349331226235718351 89792541523996839353577527)
  ·
    refine ⟨134688812285995259030366291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89792541523996839353577527 134688812285995259030366291)
    ·
      refine ⟨202033218428992888545549437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134688812285995259030366291 202033218428992888545549437)
      ·
        refine ⟨75762456910872333204581039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202033218428992888545549437 75762456910872333204581039)
        ·
          refine ⟨113643685366308499806871559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75762456910872333204581039 113643685366308499806871559)
          ·
            refine ⟨170465528049462749710307339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113643685366308499806871559 170465528049462749710307339)
            ·
              refine ⟨255698292074194124565461009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170465528049462749710307339 255698292074194124565461009)
              ·
                refine ⟨191773719055645593424095757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255698292074194124565461009 191773719055645593424095757)
                ·
                  refine ⟨71915144645867097534035909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191773719055645593424095757 71915144645867097534035909)
                  ·
                    refine ⟨13484089621100080787631733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71915144645867097534035909 13484089621100080787631733)
                    ·
                      refine ⟨1264133401978132573840475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13484089621100080787631733 1264133401978132573840475)
                      ·
                        rfl

theorem cell23_2461891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_2461891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461891 prefixEnd_2461891 := by exact prefixLift 2461891
  have htrace : WordTrace (prefixWord ++ tailWord_2461891) baseStart_2461891 baseEnd_2461891 := by
    simpa [prefixWord, tailWord_2461891, baseEnd_2461891] using wordTrace_append hprefix tailTrace_2461891
  have hstable : (prefixWord ++ tailWord_2461891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461891).length < 2 ^ (prefixWord ++ tailWord_2461891).sum := by decide
  have hdescent : baseEnd_2461891 < baseStart_2461891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461905 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 3, 3, 2]
def baseStart_2461905 : Nat := 118140960795 + 2461905 * 2 ^ 59
def prefixEnd_2461905 : Nat := 4983230072969 + 3 ^ 40 * 2461905 * 2
def baseEnd_2461905 : Nat := 1264140590707295519065411

theorem tailTrace_2461905 : CollatzResearch.WordTrace tailWord_2461905 prefixEnd_2461905 1264140590707295519065411 := by
  unfold tailWord_2461905
  simp only [CollatzResearch.WordTrace]
  refine ⟨89793052145946119744587169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59862034763964079829724779 89793052145946119744587169)
  ·
    refine ⟨67344789109459589808440377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89793052145946119744587169 67344789109459589808440377)
    ·
      refine ⟨50508591832094692356330283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67344789109459589808440377 50508591832094692356330283)
      ·
        refine ⟨75762887748142038534495425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50508591832094692356330283 75762887748142038534495425)
        ·
          refine ⟨56822165811106528900871569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75762887748142038534495425 56822165811106528900871569)
          ·
            refine ⟨42616624358329896675653677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56822165811106528900871569 42616624358329896675653677)
            ·
              refine ⟨15981234134373711253370129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42616624358329896675653677 15981234134373711253370129)
              ·
                refine ⟨11985925600780283440027597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15981234134373711253370129 11985925600780283440027597)
                ·
                  refine ⟨4494722100292606290010349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11985925600780283440027597 4494722100292606290010349)
                  ·
                    refine ⟨1685520787609727358753881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4494722100292606290010349 1685520787609727358753881)
                    ·
                      refine ⟨1264140590707295519065411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685520787609727358753881 1264140590707295519065411)
                      ·
                        rfl

theorem cell23_2461905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 3, 2].length) (baseStart_2461905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461905 prefixEnd_2461905 := by exact prefixLift 2461905
  have htrace : WordTrace (prefixWord ++ tailWord_2461905) baseStart_2461905 baseEnd_2461905 := by
    simpa [prefixWord, tailWord_2461905, baseEnd_2461905] using wordTrace_append hprefix tailTrace_2461905
  have hstable : (prefixWord ++ tailWord_2461905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461905).length < 2 ^ (prefixWord ++ tailWord_2461905).sum := by decide
  have hdescent : baseEnd_2461905 < baseStart_2461905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461912 : List Nat := [2, 1, 2, 2, 4, 1, 2, 3, 2, 1, 3]
def baseStart_2461912 : Nat := 118140960795 + 2461912 * 2 ^ 59
def prefixEnd_2461912 : Nat := 4983230072969 + 3 ^ 40 * 2461912 * 2
def baseEnd_2461912 : Nat := 1264144185071876991677879

theorem tailTrace_2461912 : CollatzResearch.WordTrace tailWord_2461912 prefixEnd_2461912 1264144185071876991677879 := by
  unfold tailWord_2461912
  simp only [CollatzResearch.WordTrace]
  refine ⟨44896653728460379970045995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59862204971280506626727993 44896653728460379970045995)
  ·
    refine ⟨67344980592690569955068993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44896653728460379970045995 67344980592690569955068993)
    ·
      refine ⟨50508735444517927466301745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67344980592690569955068993 50508735444517927466301745)
      ·
        refine ⟨37881551583388445599726309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50508735444517927466301745 37881551583388445599726309)
        ·
          refine ⟨7102790921885333549948683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37881551583388445599726309 7102790921885333549948683)
          ·
            refine ⟨10654186382828000324923025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7102790921885333549948683 10654186382828000324923025)
            ·
              refine ⟨7990639787121000243692269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10654186382828000324923025 7990639787121000243692269)
              ·
                refine ⟨2996489920170375091384601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7990639787121000243692269 2996489920170375091384601)
                ·
                  refine ⟨2247367440127781318538451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2996489920170375091384601 2247367440127781318538451)
                  ·
                    refine ⟨3371051160191671977807677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2247367440127781318538451 3371051160191671977807677)
                    ·
                      refine ⟨1264144185071876991677879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3371051160191671977807677 1264144185071876991677879)
                      ·
                        rfl

theorem cell23_2461912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_2461912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2461912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2461912 prefixEnd_2461912 := by exact prefixLift 2461912
  have htrace : WordTrace (prefixWord ++ tailWord_2461912) baseStart_2461912 baseEnd_2461912 := by
    simpa [prefixWord, tailWord_2461912, baseEnd_2461912] using wordTrace_append hprefix tailTrace_2461912
  have hstable : (prefixWord ++ tailWord_2461912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461912).length < 2 ^ (prefixWord ++ tailWord_2461912).sum := by decide
  have hdescent : baseEnd_2461912 < baseStart_2461912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462005 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 2, 5]
def baseStart_2462005 : Nat := 118140960795 + 2462005 * 2 ^ 59
def prefixEnd_2462005 : Nat := 4983230072969 + 3 ^ 40 * 2462005 * 2
def baseEnd_2462005 : Nat := 421397312924248375938317

theorem tailTrace_2462005 : CollatzResearch.WordTrace tailWord_2462005 prefixEnd_2462005 421397312924248375938317 := by
  unfold tailWord_2462005
  simp only [CollatzResearch.WordTrace]
  refine ⟨89796699445583836823227469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59864466297055891215484979 89796699445583836823227469)
  ·
    refine ⟨33673762292093938808710301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89796699445583836823227469 33673762292093938808710301)
    ·
      refine ⟨12627660859535227053266363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33673762292093938808710301 12627660859535227053266363)
      ·
        refine ⟨18941491289302840579899545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12627660859535227053266363 18941491289302840579899545)
        ·
          refine ⟨14206118466977130434924659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18941491289302840579899545 14206118466977130434924659)
          ·
            refine ⟨21309177700465695652386989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14206118466977130434924659 21309177700465695652386989)
            ·
              refine ⟨7990941637674635869645121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21309177700465695652386989 7990941637674635869645121)
              ·
                refine ⟨5993206228255976902233841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7990941637674635869645121 5993206228255976902233841)
                ·
                  refine ⟨4494904671191982676675381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5993206228255976902233841 4494904671191982676675381)
                  ·
                    refine ⟨421397312924248375938317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4494904671191982676675381 421397312924248375938317)
                    ·
                      rfl

theorem cell23_2462005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_2462005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462005 prefixEnd_2462005 := by exact prefixLift 2462005
  have htrace : WordTrace (prefixWord ++ tailWord_2462005) baseStart_2462005 baseEnd_2462005 := by
    simpa [prefixWord, tailWord_2462005, baseEnd_2462005] using wordTrace_append hprefix tailTrace_2462005
  have hstable : (prefixWord ++ tailWord_2462005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462005).length < 2 ^ (prefixWord ++ tailWord_2462005).sum := by decide
  have hdescent : baseEnd_2462005 < baseStart_2462005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462009 : List Nat := [1, 2, 1, 6, 1, 2, 3, 2, 5]
def baseStart_2462009 : Nat := 118140960795 + 2462009 * 2 ^ 59
def prefixEnd_2462009 : Nat := 4983230072969 + 3 ^ 40 * 2462009 * 2
def baseEnd_2462009 : Nat := 140465999188373679129437

theorem tailTrace_2462009 : CollatzResearch.WordTrace tailWord_2462009 prefixEnd_2462009 140465999188373679129437 := by
  unfold tailWord_2462009
  simp only [CollatzResearch.WordTrace]
  refine ⟨89796845337569345506373081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59864563558379563670915387 89796845337569345506373081)
  ·
    refine ⟨67347634003177009129779811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89796845337569345506373081 67347634003177009129779811)
    ·
      refine ⟨101021451004765513694669717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67347634003177009129779811 101021451004765513694669717)
      ·
        refine ⟨4735380515848383454437643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 101021451004765513694669717 4735380515848383454437643)
        ·
          refine ⟨7103070773772575181656465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4735380515848383454437643 7103070773772575181656465)
          ·
            refine ⟨5327303080329431386242349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7103070773772575181656465 5327303080329431386242349)
            ·
              refine ⟨1997738655123536769840881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5327303080329431386242349 1997738655123536769840881)
              ·
                refine ⟨1498303991342652577380661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1997738655123536769840881 1498303991342652577380661)
                ·
                  refine ⟨140465999188373679129437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1498303991342652577380661 140465999188373679129437)
                  ·
                    rfl

theorem cell23_2462009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 5].length) (baseStart_2462009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462009 prefixEnd_2462009 := by exact prefixLift 2462009
  have htrace : WordTrace (prefixWord ++ tailWord_2462009) baseStart_2462009 baseEnd_2462009 := by
    simpa [prefixWord, tailWord_2462009, baseEnd_2462009] using wordTrace_append hprefix tailTrace_2462009
  have hstable : (prefixWord ++ tailWord_2462009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462009).length < 2 ^ (prefixWord ++ tailWord_2462009).sum := by decide
  have hdescent : baseEnd_2462009 < baseStart_2462009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462020 : List Nat := [2, 3, 4, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_2462020 : Nat := 118140960795 + 2462020 * 2 ^ 59
def prefixEnd_2462020 : Nat := 4983230072969 + 3 ^ 40 * 2462020 * 2
def baseEnd_2462020 : Nat := 1264199640982562569127383

theorem tailTrace_2462020 : CollatzResearch.WordTrace tailWord_2462020 prefixEnd_2462020 1264199640982562569127383 := by
  unfold tailWord_2462020
  simp only [CollatzResearch.WordTrace]
  refine ⟨44898623270264747192511757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59864831027019662923349009 44898623270264747192511757)
  ·
    refine ⟨16836983726349280197191909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44898623270264747192511757 16836983726349280197191909)
    ·
      refine ⟨3156934448690490036973483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16836983726349280197191909 3156934448690490036973483)
      ·
        refine ⟨4735401673035735055460225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3156934448690490036973483 4735401673035735055460225)
        ·
          refine ⟨3551551254776801291595169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4735401673035735055460225 3551551254776801291595169)
          ·
            refine ⟨2663663441082600968696377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3551551254776801291595169 2663663441082600968696377)
            ·
              refine ⟨1997747580811950726522283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2663663441082600968696377 1997747580811950726522283)
              ·
                refine ⟨2996621371217926089783425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1997747580811950726522283 2996621371217926089783425)
                ·
                  refine ⟨2247466028413444567337569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2996621371217926089783425 2247466028413444567337569)
                  ·
                    refine ⟨1685599521310083425503177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2247466028413444567337569 1685599521310083425503177)
                    ·
                      refine ⟨1264199640982562569127383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685599521310083425503177 1264199640982562569127383)
                      ·
                        rfl

theorem cell23_2462020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_2462020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462020 prefixEnd_2462020 := by exact prefixLift 2462020
  have htrace : WordTrace (prefixWord ++ tailWord_2462020) baseStart_2462020 baseEnd_2462020 := by
    simpa [prefixWord, tailWord_2462020, baseEnd_2462020] using wordTrace_append hprefix tailTrace_2462020
  have hstable : (prefixWord ++ tailWord_2462020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462020).length < 2 ^ (prefixWord ++ tailWord_2462020).sum := by decide
  have hdescent : baseEnd_2462020 < baseStart_2462020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462025 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 1, 6, 2]
def baseStart_2462025 : Nat := 118140960795 + 2462025 * 2 ^ 59
def prefixEnd_2462025 : Nat := 4983230072969 + 3 ^ 40 * 2462025 * 2
def baseEnd_2462025 : Nat := 1264202208385835049564859

theorem tailTrace_2462025 : CollatzResearch.WordTrace tailWord_2462025 prefixEnd_2462025 1264202208385835049564859 := by
  unfold tailWord_2462025
  simp only [CollatzResearch.WordTrace]
  refine ⟨89797428905511380238955529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59864952603674253492637019 89797428905511380238955529)
  ·
    refine ⟨67348071679133535179216647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89797428905511380238955529 67348071679133535179216647)
    ·
      refine ⟨101022107518700302768824971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67348071679133535179216647 101022107518700302768824971)
      ·
        refine ⟨151533161278050454153237457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101022107518700302768824971 151533161278050454153237457)
        ·
          refine ⟨113649870958537840614928093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151533161278050454153237457 113649870958537840614928093)
          ·
            refine ⟨42618701609451690230598035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113649870958537840614928093 42618701609451690230598035)
            ·
              refine ⟨63928052414177535345897053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42618701609451690230598035 63928052414177535345897053)
              ·
                refine ⟨23973019655316575754711395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63928052414177535345897053 23973019655316575754711395)
                ·
                  refine ⟨35959529482974863632067093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23973019655316575754711395 35959529482974863632067093)
                  ·
                    refine ⟨1685602944514446732753145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35959529482974863632067093 1685602944514446732753145)
                    ·
                      refine ⟨1264202208385835049564859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685602944514446732753145 1264202208385835049564859)
                      ·
                        rfl

theorem cell23_2462025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 6, 2].length) (baseStart_2462025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462025 prefixEnd_2462025 := by exact prefixLift 2462025
  have htrace : WordTrace (prefixWord ++ tailWord_2462025) baseStart_2462025 baseEnd_2462025 := by
    simpa [prefixWord, tailWord_2462025, baseEnd_2462025] using wordTrace_append hprefix tailTrace_2462025
  have hstable : (prefixWord ++ tailWord_2462025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462025).length < 2 ^ (prefixWord ++ tailWord_2462025).sum := by decide
  have hdescent : baseEnd_2462025 < baseStart_2462025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462092 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 5, 1, 3]
def baseStart_2462092 : Nat := 118140960795 + 2462092 * 2 ^ 59
def prefixEnd_2462092 : Nat := 4983230072969 + 3 ^ 40 * 2462092 * 2
def baseEnd_2462092 : Nat := 1264236611589686287427051

theorem tailTrace_2462092 : CollatzResearch.WordTrace tailWord_2462092 prefixEnd_2462092 1264236611589686287427051 := by
  unfold tailWord_2462092
  simp only [CollatzResearch.WordTrace]
  refine ⟨44899936298134325340822265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59866581730845767121096353 44899936298134325340822265)
  ·
    refine ⟨33674952223600744005616699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44899936298134325340822265 33674952223600744005616699)
    ·
      refine ⟨50512428335401116008425049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33674952223600744005616699 50512428335401116008425049)
      ·
        refine ⟨37884321251550837006318787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50512428335401116008425049 37884321251550837006318787)
        ·
          refine ⟨56826481877326255509478181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37884321251550837006318787 56826481877326255509478181)
          ·
            refine ⟨10654965351998672908027159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56826481877326255509478181 10654965351998672908027159)
            ·
              refine ⟨15982448027998009362040739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10654965351998672908027159 15982448027998009362040739)
              ·
                refine ⟨23973672041997014043061109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15982448027998009362040739 23973672041997014043061109)
                ·
                  refine ⟨2247531753937220066536979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23973672041997014043061109 2247531753937220066536979)
                  ·
                    refine ⟨3371297630905830099805469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2247531753937220066536979 3371297630905830099805469)
                    ·
                      refine ⟨1264236611589686287427051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3371297630905830099805469 1264236611589686287427051)
                      ·
                        rfl

theorem cell23_2462092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_2462092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462092 prefixEnd_2462092 := by exact prefixLift 2462092
  have htrace : WordTrace (prefixWord ++ tailWord_2462092) baseStart_2462092 baseEnd_2462092 := by
    simpa [prefixWord, tailWord_2462092, baseEnd_2462092] using wordTrace_append hprefix tailTrace_2462092
  have hstable : (prefixWord ++ tailWord_2462092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462092).length < 2 ^ (prefixWord ++ tailWord_2462092).sum := by decide
  have hdescent : baseEnd_2462092 < baseStart_2462092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462112 : List Nat := [2, 1, 1, 4, 1, 4, 1, 3, 1, 5]
def baseStart_2462112 : Nat := 118140960795 + 2462112 * 2 ^ 59
def prefixEnd_2462112 : Nat := 4983230072969 + 3 ^ 40 * 2462112 * 2
def baseEnd_2462112 : Nat := 421415627067592069725653

theorem tailTrace_2462112 : CollatzResearch.WordTrace tailWord_2462112 prefixEnd_2462112 421415627067592069725653 := by
  unfold tailWord_2462112
  simp only [CollatzResearch.WordTrace]
  refine ⟨44900301028098097048686295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59867068037464129398248393 44900301028098097048686295)
  ·
    refine ⟨67350451542147145573029443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44900301028098097048686295 67350451542147145573029443)
    ·
      refine ⟨101025677313220718359544165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67350451542147145573029443 101025677313220718359544165)
      ·
        refine ⟨18942314496228884692414531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101025677313220718359544165 18942314496228884692414531)
        ·
          refine ⟨28413471744343327038621797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18942314496228884692414531 28413471744343327038621797)
          ·
            refine ⟨5327525952064373819741587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28413471744343327038621797 5327525952064373819741587)
            ·
              refine ⟨7991288928096560729612381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5327525952064373819741587 7991288928096560729612381)
              ·
                refine ⟨2996733348036210273604643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7991288928096560729612381 2996733348036210273604643)
                ·
                  refine ⟨4495100022054315410406965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996733348036210273604643 4495100022054315410406965)
                  ·
                    refine ⟨421415627067592069725653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4495100022054315410406965 421415627067592069725653)
                    ·
                      rfl

theorem cell23_2462112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 1, 5].length) (baseStart_2462112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462112 prefixEnd_2462112 := by exact prefixLift 2462112
  have htrace : WordTrace (prefixWord ++ tailWord_2462112) baseStart_2462112 baseEnd_2462112 := by
    simpa [prefixWord, tailWord_2462112, baseEnd_2462112] using wordTrace_append hprefix tailTrace_2462112
  have hstable : (prefixWord ++ tailWord_2462112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462112).length < 2 ^ (prefixWord ++ tailWord_2462112).sum := by decide
  have hdescent : baseEnd_2462112 < baseStart_2462112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462135 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_2462135 : Nat := 118140960795 + 2462135 * 2 ^ 59
def prefixEnd_2462135 : Nat := 4983230072969 + 3 ^ 40 * 2462135 * 2
def baseEnd_2462135 : Nat := 1264258691257829619189353

theorem tailTrace_2462135 : CollatzResearch.WordTrace tailWord_2462135 prefixEnd_2462135 1264258691257829619189353 := by
  unfold tailWord_2462135
  simp only [CollatzResearch.WordTrace]
  refine ⟨89801440935112869025459859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59867627290075246016973239 89801440935112869025459859)
  ·
    refine ⟨134702161402669303538189789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89801440935112869025459859 134702161402669303538189789)
    ·
      refine ⟨50513310526000988826821171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134702161402669303538189789 50513310526000988826821171)
      ·
        refine ⟨75769965789001483240231757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50513310526000988826821171 75769965789001483240231757)
        ·
          refine ⟨28413737170875556215086909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75769965789001483240231757 28413737170875556215086909)
          ·
            refine ⟨10655151439078333580657591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28413737170875556215086909 10655151439078333580657591)
            ·
              refine ⟨15982727158617500370986387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10655151439078333580657591 15982727158617500370986387)
              ·
                refine ⟨23974090737926250556479581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15982727158617500370986387 23974090737926250556479581)
                ·
                  refine ⟨8990284026722343958679843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23974090737926250556479581 8990284026722343958679843)
                  ·
                    refine ⟨13485426040083515938019765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8990284026722343958679843 13485426040083515938019765)
                    ·
                      refine ⟨1264258691257829619189353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13485426040083515938019765 1264258691257829619189353)
                      ·
                        rfl

theorem cell23_2462135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_2462135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462135 prefixEnd_2462135 := by exact prefixLift 2462135
  have htrace : WordTrace (prefixWord ++ tailWord_2462135) baseStart_2462135 baseEnd_2462135 := by
    simpa [prefixWord, tailWord_2462135, baseEnd_2462135] using wordTrace_append hprefix tailTrace_2462135
  have hstable : (prefixWord ++ tailWord_2462135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462135).length < 2 ^ (prefixWord ++ tailWord_2462135).sum := by decide
  have hdescent : baseEnd_2462135 < baseStart_2462135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462142 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_2462142 : Nat := 118140960795 + 2462142 * 2 ^ 59
def prefixEnd_2462142 : Nat := 4983230072969 + 3 ^ 40 * 2462142 * 2
def baseEnd_2462142 : Nat := 421420761874137030600607

theorem tailTrace_2462142 : CollatzResearch.WordTrace tailWord_2462142 prefixEnd_2462142 421420761874137030600607 := by
  unfold tailWord_2462142
  simp only [CollatzResearch.WordTrace]
  refine ⟨11225212030760938652620585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59867797497391672813976453 11225212030760938652620585)
  ·
    refine ⟨8418909023070703989465439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11225212030760938652620585 8418909023070703989465439)
    ·
      refine ⟨12628363534606055984198159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8418909023070703989465439 12628363534606055984198159)
      ·
        refine ⟨18942545301909083976297239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12628363534606055984198159 18942545301909083976297239)
        ·
          refine ⟨28413817952863625964445859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18942545301909083976297239 28413817952863625964445859)
          ·
            refine ⟨42620726929295438946668789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28413817952863625964445859 42620726929295438946668789)
            ·
              refine ⟨3995693149621447401250199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42620726929295438946668789 3995693149621447401250199)
              ·
                refine ⟨5993539724432171101875299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3995693149621447401250199 5993539724432171101875299)
                ·
                  refine ⟨8990309586648256652812949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5993539724432171101875299 8990309586648256652812949)
                  ·
                    refine ⟨421420761874137030600607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8990309586648256652812949 421420761874137030600607)
                    ·
                      rfl

theorem cell23_2462142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_2462142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462142 prefixEnd_2462142 := by exact prefixLift 2462142
  have htrace : WordTrace (prefixWord ++ tailWord_2462142) baseStart_2462142 baseEnd_2462142 := by
    simpa [prefixWord, tailWord_2462142, baseEnd_2462142] using wordTrace_append hprefix tailTrace_2462142
  have hstable : (prefixWord ++ tailWord_2462142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462142).length < 2 ^ (prefixWord ++ tailWord_2462142).sum := by decide
  have hdescent : baseEnd_2462142 < baseStart_2462142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462225 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_2462225 : Nat := 118140960795 + 2462225 * 2 ^ 59
def prefixEnd_2462225 : Nat := 4983230072969 + 3 ^ 40 * 2462225 * 2
def baseEnd_2462225 : Nat := 1264304904516734267063939

theorem tailTrace_2462225 : CollatzResearch.WordTrace tailWord_2462225 prefixEnd_2462225 1264304904516734267063939 := by
  unfold tailWord_2462225
  simp only [CollatzResearch.WordTrace]
  refine ⟨89804723504786814396236129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59869815669857876264157419 89804723504786814396236129)
  ·
    refine ⟨67353542628590110797177097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89804723504786814396236129 67353542628590110797177097)
    ·
      refine ⟨50515156971442583097882823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67353542628590110797177097 50515156971442583097882823)
      ·
        refine ⟨75772735457163874646824235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50515156971442583097882823 75772735457163874646824235)
        ·
          refine ⟨113659103185745811970236353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75772735457163874646824235 113659103185745811970236353)
          ·
            refine ⟨85244327389309358977677265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113659103185745811970236353 85244327389309358977677265)
            ·
              refine ⟨63933245541982019233257949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85244327389309358977677265 63933245541982019233257949)
              ·
                refine ⟨23974967078243257212471731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63933245541982019233257949 23974967078243257212471731)
                ·
                  refine ⟨35962450617364885818707597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23974967078243257212471731 35962450617364885818707597)
                  ·
                    refine ⟨13485918981511832182015349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35962450617364885818707597 13485918981511832182015349)
                    ·
                      refine ⟨1264304904516734267063939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13485918981511832182015349 1264304904516734267063939)
                      ·
                        rfl

theorem cell23_2462225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_2462225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462225 prefixEnd_2462225 := by exact prefixLift 2462225
  have htrace : WordTrace (prefixWord ++ tailWord_2462225) baseStart_2462225 baseEnd_2462225 := by
    simpa [prefixWord, tailWord_2462225, baseEnd_2462225] using wordTrace_append hprefix tailTrace_2462225
  have hstable : (prefixWord ++ tailWord_2462225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462225).length < 2 ^ (prefixWord ++ tailWord_2462225).sum := by decide
  have hdescent : baseEnd_2462225 < baseStart_2462225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462235 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 4]
def baseStart_2462235 : Nat := 118140960795 + 2462235 * 2 ^ 59
def prefixEnd_2462235 : Nat := 4983230072969 + 3 ^ 40 * 2462235 * 2
def baseEnd_2462235 : Nat := 1264310039323279227938893

theorem tailTrace_2462235 : CollatzResearch.WordTrace tailWord_2462235 prefixEnd_2462235 1264310039323279227938893 := by
  unfold tailWord_2462235
  simp only [CollatzResearch.WordTrace]
  refine ⟨89805088234750586104100159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59870058823167057402733439 89805088234750586104100159)
  ·
    refine ⟨134707632352125879156150239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89805088234750586104100159 134707632352125879156150239)
    ·
      refine ⟨202061448528188818734225359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134707632352125879156150239 202061448528188818734225359)
      ·
        refine ⟨303092172792283228101338039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202061448528188818734225359 303092172792283228101338039)
        ·
          refine ⟨454638259188424842152007059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303092172792283228101338039 454638259188424842152007059)
          ·
            refine ⟨681957388782637263228010589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454638259188424842152007059 681957388782637263228010589)
            ·
              refine ⟨255734020793488973710503971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 681957388782637263228010589 255734020793488973710503971)
              ·
                refine ⟨383601031190233460565755957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255734020793488973710503971 383601031190233460565755957)
                ·
                  refine ⟨35962596674084386928039621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 383601031190233460565755957 35962596674084386928039621)
                  ·
                    refine ⟨6742986876390822549007429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35962596674084386928039621 6742986876390822549007429)
                    ·
                      refine ⟨1264310039323279227938893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6742986876390822549007429 1264310039323279227938893)
                      ·
                        rfl

theorem cell23_2462235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 4].length) (baseStart_2462235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462235 prefixEnd_2462235 := by exact prefixLift 2462235
  have htrace : WordTrace (prefixWord ++ tailWord_2462235) baseStart_2462235 baseEnd_2462235 := by
    simpa [prefixWord, tailWord_2462235, baseEnd_2462235] using wordTrace_append hprefix tailTrace_2462235
  have hstable : (prefixWord ++ tailWord_2462235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462235).length < 2 ^ (prefixWord ++ tailWord_2462235).sum := by decide
  have hdescent : baseEnd_2462235 < baseStart_2462235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462256 : List Nat := [2, 1, 1, 1, 2, 3, 4, 3, 2, 2, 2]
def baseStart_2462256 : Nat := 118140960795 + 2462256 * 2 ^ 59
def prefixEnd_2462256 : Nat := 4983230072969 + 3 ^ 40 * 2462256 * 2
def baseEnd_2462256 : Nat := 1264320822417023645776297

theorem tailTrace_2462256 : CollatzResearch.WordTrace tailWord_2462256 prefixEnd_2462256 1264320822417023645776297 := by
  unfold tailWord_2462256
  simp only [CollatzResearch.WordTrace]
  refine ⟨44902927083837253345307311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59870569445116337793743081 44902927083837253345307311)
  ·
    refine ⟨67354390625755880017960967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44902927083837253345307311 67354390625755880017960967)
    ·
      refine ⟨101031585938633820026941451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67354390625755880017960967 101031585938633820026941451)
      ·
        refine ⟨151547378907950730040412177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101031585938633820026941451 151547378907950730040412177)
        ·
          refine ⟨113660534180963047530309133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151547378907950730040412177 113660534180963047530309133)
          ·
            refine ⟨42622700317861142823865925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113660534180963047530309133 42622700317861142823865925)
            ·
              refine ⟨7991756309598964279474861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42622700317861142823865925 7991756309598964279474861)
              ·
                refine ⟨2996908616099611604803073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7991756309598964279474861 2996908616099611604803073)
                ·
                  refine ⟨2247681462074708703602305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2996908616099611604803073 2247681462074708703602305)
                  ·
                    refine ⟨1685761096556031527701729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2247681462074708703602305 1685761096556031527701729)
                    ·
                      refine ⟨1264320822417023645776297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685761096556031527701729 1264320822417023645776297)
                      ·
                        rfl

theorem cell23_2462256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 2, 2, 2].length) (baseStart_2462256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462256 prefixEnd_2462256 := by exact prefixLift 2462256
  have htrace : WordTrace (prefixWord ++ tailWord_2462256) baseStart_2462256 baseEnd_2462256 := by
    simpa [prefixWord, tailWord_2462256, baseEnd_2462256] using wordTrace_append hprefix tailTrace_2462256
  have hstable : (prefixWord ++ tailWord_2462256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462256).length < 2 ^ (prefixWord ++ tailWord_2462256).sum := by decide
  have hdescent : baseEnd_2462256 < baseStart_2462256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462279 : List Nat := [1, 1, 4, 1, 4, 1, 1, 5, 5]
def baseStart_2462279 : Nat := 118140960795 + 2462279 * 2 ^ 59
def prefixEnd_2462279 : Nat := 4983230072969 + 3 ^ 40 * 2462279 * 2
def baseEnd_2462279 : Nat := 140481403608008561754299

theorem tailTrace_2462279 : CollatzResearch.WordTrace tailWord_2462279 prefixEnd_2462279 140481403608008561754299 := by
  unfold tailWord_2462279
  simp only [CollatzResearch.WordTrace]
  refine ⟨89806693046591181618701891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59871128697727454412467927 89806693046591181618701891)
  ·
    refine ⟨134710039569886772428052837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89806693046591181618701891 134710039569886772428052837)
    ·
      refine ⟨25258132419353769830259907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134710039569886772428052837 25258132419353769830259907)
      ·
        refine ⟨37887198629030654745389861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25258132419353769830259907 37887198629030654745389861)
        ·
          refine ⟨7103849742943247764760599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37887198629030654745389861 7103849742943247764760599)
          ·
            refine ⟨10655774614414871647140899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7103849742943247764760599 10655774614414871647140899)
            ·
              refine ⟨15983661921622307470711349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10655774614414871647140899 15983661921622307470711349)
              ·
                refine ⟨1498468305152091325379189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15983661921622307470711349 1498468305152091325379189)
                ·
                  refine ⟨140481403608008561754299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1498468305152091325379189 140481403608008561754299)
                  ·
                    rfl

theorem cell23_2462279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 5].length) (baseStart_2462279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462279 prefixEnd_2462279 := by exact prefixLift 2462279
  have htrace : WordTrace (prefixWord ++ tailWord_2462279) baseStart_2462279 baseEnd_2462279 := by
    simpa [prefixWord, tailWord_2462279, baseEnd_2462279] using wordTrace_append hprefix tailTrace_2462279
  have hstable : (prefixWord ++ tailWord_2462279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462279).length < 2 ^ (prefixWord ++ tailWord_2462279).sum := by decide
  have hdescent : baseEnd_2462279 < baseStart_2462279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462346 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_2462346 : Nat := 118140960795 + 2462346 * 2 ^ 59
def prefixEnd_2462346 : Nat := 4983230072969 + 3 ^ 40 * 2462346 * 2
def baseEnd_2462346 : Nat := 1264367035675928293650883

theorem tailTrace_2462346 : CollatzResearch.WordTrace tailWord_2462346 prefixEnd_2462346 1264367035675928293650883 := by
  unfold tailWord_2462346
  simp only [CollatzResearch.WordTrace]
  refine ⟨22452284184337113015347723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59872757824898968040927261 22452284184337113015347723)
  ·
    refine ⟨33678426276505669523021585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22452284184337113015347723 33678426276505669523021585)
    ·
      refine ⟨25258819707379252142266189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33678426276505669523021585 25258819707379252142266189)
      ·
        refine ⟨9472057390267219553349821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25258819707379252142266189 9472057390267219553349821)
        ·
          refine ⟨3552021521350207332506183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9472057390267219553349821 3552021521350207332506183)
          ·
            refine ⟨5328032282025310998759275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3552021521350207332506183 5328032282025310998759275)
            ·
              refine ⟨7992048423037966498138913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5328032282025310998759275 7992048423037966498138913)
              ·
                refine ⟨5994036317278474873604185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7992048423037966498138913 5994036317278474873604185)
                ·
                  refine ⟨4495527237958856155203139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5994036317278474873604185 4495527237958856155203139)
                  ·
                    refine ⟨6743290856938284232804709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4495527237958856155203139 6743290856938284232804709)
                    ·
                      refine ⟨1264367035675928293650883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6743290856938284232804709 1264367035675928293650883)
                      ·
                        rfl

theorem cell23_2462346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_2462346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462346 prefixEnd_2462346 := by exact prefixLift 2462346
  have htrace : WordTrace (prefixWord ++ tailWord_2462346) baseStart_2462346 baseEnd_2462346 := by
    simpa [prefixWord, tailWord_2462346, baseEnd_2462346] using wordTrace_append hprefix tailTrace_2462346
  have hstable : (prefixWord ++ tailWord_2462346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462346).length < 2 ^ (prefixWord ++ tailWord_2462346).sum := by decide
  have hdescent : baseEnd_2462346 < baseStart_2462346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462366 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_2462366 : Nat := 118140960795 + 2462366 * 2 ^ 59
def prefixEnd_2462366 : Nat := 4983230072969 + 3 ^ 40 * 2462366 * 2
def baseEnd_2462366 : Nat := 1264377305289018215400791

theorem tailTrace_2462366 : CollatzResearch.WordTrace tailWord_2462366 prefixEnd_2462366 1264377305289018215400791 := by
  unfold tailWord_2462366
  simp only [CollatzResearch.WordTrace]
  refine ⟨11226233274659499434639869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59873244131517330318079301 11226233274659499434639869)
  ·
    refine ⟨4209837477997312287989951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11226233274659499434639869 4209837477997312287989951)
    ·
      refine ⟨6314756216995968431984927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4209837477997312287989951 6314756216995968431984927)
      ·
        refine ⟨9472134325493952647977391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6314756216995968431984927 9472134325493952647977391)
        ·
          refine ⟨14208201488240928971966087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9472134325493952647977391 14208201488240928971966087)
          ·
            refine ⟨21312302232361393457949131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14208201488240928971966087 21312302232361393457949131)
            ·
              refine ⟨31968453348542090186923697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21312302232361393457949131 31968453348542090186923697)
              ·
                refine ⟨23976340011406567640192773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31968453348542090186923697 23976340011406567640192773)
                ·
                  refine ⟨4495563752138731432536145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23976340011406567640192773 4495563752138731432536145)
                  ·
                    refine ⟨3371672814104048574402109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4495563752138731432536145 3371672814104048574402109)
                    ·
                      refine ⟨1264377305289018215400791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3371672814104048574402109 1264377305289018215400791)
                      ·
                        rfl

theorem cell23_2462366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_2462366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462366 prefixEnd_2462366 := by exact prefixLift 2462366
  have htrace : WordTrace (prefixWord ++ tailWord_2462366) baseStart_2462366 baseEnd_2462366 := by
    simpa [prefixWord, tailWord_2462366, baseEnd_2462366] using wordTrace_append hprefix tailTrace_2462366
  have hstable : (prefixWord ++ tailWord_2462366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462366).length < 2 ^ (prefixWord ++ tailWord_2462366).sum := by decide
  have hdescent : baseEnd_2462366 < baseStart_2462366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462440 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_2462440 : Nat := 118140960795 + 2462440 * 2 ^ 59
def prefixEnd_2462440 : Nat := 4983230072969 + 3 ^ 40 * 2462440 * 2
def baseEnd_2462440 : Nat := 1264415302857450925875451

theorem tailTrace_2462440 : CollatzResearch.WordTrace tailWord_2462440 prefixEnd_2462440 1264415302857450925875451 := by
  unfold tailWord_2462440
  simp only [CollatzResearch.WordTrace]
  refine ⟨44906282599503953057656387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59875043466005270743541849 44906282599503953057656387)
  ·
    refine ⟨67359423899255929586484581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44906282599503953057656387 67359423899255929586484581)
    ·
      refine ⟨12629891981110486797465859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67359423899255929586484581 12629891981110486797465859)
      ·
        refine ⟨18944837971665730196198789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12629891981110486797465859 18944837971665730196198789)
        ·
          refine ⟨3552157119687324411787273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18944837971665730196198789 3552157119687324411787273)
          ·
            refine ⟨2664117839765493308840455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3552157119687324411787273 2664117839765493308840455)
            ·
              refine ⟨3996176759648239963260683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664117839765493308840455 3996176759648239963260683)
              ·
                refine ⟨5994265139472359944891025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3996176759648239963260683 5994265139472359944891025)
                ·
                  refine ⟨4495698854604269958668269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5994265139472359944891025 4495698854604269958668269)
                  ·
                    refine ⟨1685887070476601234500601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4495698854604269958668269 1685887070476601234500601)
                    ·
                      refine ⟨1264415302857450925875451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685887070476601234500601 1264415302857450925875451)
                      ·
                        rfl

theorem cell23_2462440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_2462440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462440 prefixEnd_2462440 := by exact prefixLift 2462440
  have htrace : WordTrace (prefixWord ++ tailWord_2462440) baseStart_2462440 baseEnd_2462440 := by
    simpa [prefixWord, tailWord_2462440, baseEnd_2462440] using wordTrace_append hprefix tailTrace_2462440
  have hstable : (prefixWord ++ tailWord_2462440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462440).length < 2 ^ (prefixWord ++ tailWord_2462440).sum := by decide
  have hdescent : baseEnd_2462440 < baseStart_2462440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462449 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_2462449 : Nat := 118140960795 + 2462449 * 2 ^ 59
def prefixEnd_2462449 : Nat := 4983230072969 + 3 ^ 40 * 2462449 * 2
def baseEnd_2462449 : Nat := 1264419924183341390662909

theorem tailTrace_2462449 : CollatzResearch.WordTrace tailWord_2462449 prefixEnd_2462449 1264419924183341390662909 := by
  unfold tailWord_2462449
  simp only [CollatzResearch.WordTrace]
  refine ⟨89812893455975300652390401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59875262303983533768260267 89812893455975300652390401)
  ·
    refine ⟨67359670091981475489292801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89812893455975300652390401 67359670091981475489292801)
    ·
      refine ⟨50519752568986106616969601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67359670091981475489292801 50519752568986106616969601)
      ·
        refine ⟨37889814426739579962727201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50519752568986106616969601 37889814426739579962727201)
        ·
          refine ⟨28417360820054684972045401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37889814426739579962727201 28417360820054684972045401)
          ·
            refine ⟨21313020615041013729034051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28417360820054684972045401 21313020615041013729034051)
            ·
              refine ⟨31969530922561520593551077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21313020615041013729034051 31969530922561520593551077)
              ·
                refine ⟨5994287047980285111290827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31969530922561520593551077 5994287047980285111290827)
                ·
                  refine ⟨8991430571970427666936241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5994287047980285111290827 8991430571970427666936241)
                  ·
                    refine ⟨6743572928977820750202181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8991430571970427666936241 6743572928977820750202181)
                    ·
                      refine ⟨1264419924183341390662909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6743572928977820750202181 1264419924183341390662909)
                      ·
                        rfl

theorem cell23_2462449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_2462449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462449 prefixEnd_2462449 := by exact prefixLift 2462449
  have htrace : WordTrace (prefixWord ++ tailWord_2462449) baseStart_2462449 baseEnd_2462449 := by
    simpa [prefixWord, tailWord_2462449, baseEnd_2462449] using wordTrace_append hprefix tailTrace_2462449
  have hstable : (prefixWord ++ tailWord_2462449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462449).length < 2 ^ (prefixWord ++ tailWord_2462449).sum := by decide
  have hdescent : baseEnd_2462449 < baseStart_2462449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462456 : List Nat := [2, 1, 2, 1, 1, 2, 5, 3, 1, 2, 3]
def baseStart_2462456 : Nat := 118140960795 + 2462456 * 2 ^ 59
def prefixEnd_2462456 : Nat := 4983230072969 + 3 ^ 40 * 2462456 * 2
def baseEnd_2462456 : Nat := 1264423518547922863275377

theorem tailTrace_2462456 : CollatzResearch.WordTrace tailWord_2462456 prefixEnd_2462456 1264423518547922863275377 := by
  unfold tailWord_2462456
  simp only [CollatzResearch.WordTrace]
  refine ⟨44906574383474970423947611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59875432511299960565263481 44906574383474970423947611)
  ·
    refine ⟨67359861575212455635921417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44906574383474970423947611 67359861575212455635921417)
    ·
      refine ⟨50519896181409341726941063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67359861575212455635921417 50519896181409341726941063)
      ·
        refine ⟨75779844272114012590411595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50519896181409341726941063 75779844272114012590411595)
        ·
          refine ⟨113669766408171018885617393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75779844272114012590411595 113669766408171018885617393)
          ·
            refine ⟨85252324806128264164213045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113669766408171018885617393 85252324806128264164213045)
            ·
              refine ⟨7992405450574524765394973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85252324806128264164213045 7992405450574524765394973)
              ·
                refine ⟨2997152043965446787023115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7992405450574524765394973 2997152043965446787023115)
                ·
                  refine ⟨4495728065948170180534673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2997152043965446787023115 4495728065948170180534673)
                  ·
                    refine ⟨3371796049461127635401005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4495728065948170180534673 3371796049461127635401005)
                    ·
                      refine ⟨1264423518547922863275377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3371796049461127635401005 1264423518547922863275377)
                      ·
                        rfl

theorem cell23_2462456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_2462456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462456 prefixEnd_2462456 := by exact prefixLift 2462456
  have htrace : WordTrace (prefixWord ++ tailWord_2462456) baseStart_2462456 baseEnd_2462456 := by
    simpa [prefixWord, tailWord_2462456, baseEnd_2462456] using wordTrace_append hprefix tailTrace_2462456
  have hstable : (prefixWord ++ tailWord_2462456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462456).length < 2 ^ (prefixWord ++ tailWord_2462456).sum := by decide
  have hdescent : baseEnd_2462456 < baseStart_2462456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462469 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 3, 3, 3]
def baseStart_2462469 : Nat := 118140960795 + 2462469 * 2 ^ 59
def prefixEnd_2462469 : Nat := 4983230072969 + 3 ^ 40 * 2462469 * 2
def baseEnd_2462469 : Nat := 1264430193796431312412817

theorem tailTrace_2462469 : CollatzResearch.WordTrace tailWord_2462469 prefixEnd_2462469 1264430193796431312412817 := by
  unfold tailWord_2462469
  simp only [CollatzResearch.WordTrace]
  refine ⟨89813622915902844068118461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59875748610601896045412307 89813622915902844068118461)
  ·
    refine ⟨33680108593463566525544423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89813622915902844068118461 33680108593463566525544423)
    ·
      refine ⟨50520162890195349788316635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33680108593463566525544423 50520162890195349788316635)
      ·
        refine ⟨75780244335293024682474953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50520162890195349788316635 75780244335293024682474953)
        ·
          refine ⟨56835183251469768511856215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75780244335293024682474953 56835183251469768511856215)
          ·
            refine ⟨85252774877204652767784323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56835183251469768511856215 85252774877204652767784323)
            ·
              refine ⟨127879162315806979151676485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85252774877204652767784323 127879162315806979151676485)
              ·
                refine ⟨23977342934213808590939341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127879162315806979151676485 23977342934213808590939341)
                ·
                  refine ⟨8991503600330178221602253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23977342934213808590939341 8991503600330178221602253)
                  ·
                    refine ⟨3371813850123816833100845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8991503600330178221602253 3371813850123816833100845)
                    ·
                      refine ⟨1264430193796431312412817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3371813850123816833100845 1264430193796431312412817)
                      ·
                        rfl

theorem cell23_2462469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_2462469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462469 prefixEnd_2462469 := by exact prefixLift 2462469
  have htrace : WordTrace (prefixWord ++ tailWord_2462469) baseStart_2462469 baseEnd_2462469 := by
    simpa [prefixWord, tailWord_2462469, baseEnd_2462469] using wordTrace_append hprefix tailTrace_2462469
  have hstable : (prefixWord ++ tailWord_2462469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462469).length < 2 ^ (prefixWord ++ tailWord_2462469).sum := by decide
  have hdescent : baseEnd_2462469 < baseStart_2462469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462513 : List Nat := [1, 2, 2, 3, 2, 1, 1, 5, 1, 3, 2]
def baseStart_2462513 : Nat := 118140960795 + 2462513 * 2 ^ 59
def prefixEnd_2462513 : Nat := 4983230072969 + 3 ^ 40 * 2462513 * 2
def baseEnd_2462513 : Nat := 1264452786945229140262615

theorem tailTrace_2462513 : CollatzResearch.WordTrace tailWord_2462513 prefixEnd_2462513 1264452786945229140262615 := by
  unfold tailWord_2462513
  simp only [CollatzResearch.WordTrace]
  refine ⟨89815227727743439582720193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59876818485162293055146795 89815227727743439582720193)
  ·
    refine ⟨67361420795807579687040145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89815227727743439582720193 67361420795807579687040145)
    ·
      refine ⟨50521065596855684765280109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67361420795807579687040145 50521065596855684765280109)
      ·
        refine ⟨18945399598820881786980041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50521065596855684765280109 18945399598820881786980041)
        ·
          refine ⟨14209049699115661340235031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18945399598820881786980041 14209049699115661340235031)
          ·
            refine ⟨21313574548673492010352547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14209049699115661340235031 21313574548673492010352547)
            ·
              refine ⟨31970361823010238015528821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21313574548673492010352547 31970361823010238015528821)
              ·
                refine ⟨2997221420907209813955827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31970361823010238015528821 2997221420907209813955827)
                ·
                  refine ⟨4495832131360814720933741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2997221420907209813955827 4495832131360814720933741)
                  ·
                    refine ⟨1685937049260305520350153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4495832131360814720933741 1685937049260305520350153)
                    ·
                      refine ⟨1264452786945229140262615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685937049260305520350153 1264452786945229140262615)
                      ·
                        rfl

theorem cell23_2462513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_2462513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462513 prefixEnd_2462513 := by exact prefixLift 2462513
  have htrace : WordTrace (prefixWord ++ tailWord_2462513) baseStart_2462513 baseEnd_2462513 := by
    simpa [prefixWord, tailWord_2462513, baseEnd_2462513] using wordTrace_append hprefix tailTrace_2462513
  have hstable : (prefixWord ++ tailWord_2462513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462513).length < 2 ^ (prefixWord ++ tailWord_2462513).sum := by decide
  have hdescent : baseEnd_2462513 < baseStart_2462513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462549 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 9]
def baseStart_2462549 : Nat := 118140960795 + 2462549 * 2 ^ 59
def prefixEnd_2462549 : Nat := 4983230072969 + 3 ^ 40 * 2462549 * 2
def baseEnd_2462549 : Nat := 140496808027643444379161

theorem tailTrace_2462549 : CollatzResearch.WordTrace tailWord_2462549 prefixEnd_2462549 140496808027643444379161 := by
  unfold tailWord_2462549
  simp only [CollatzResearch.WordTrace]
  refine ⟨89816540755613017731030701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59877693837075345154020467 89816540755613017731030701)
  ·
    refine ⟨33681202783354881649136513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89816540755613017731030701 33681202783354881649136513)
    ·
      refine ⟨25260902087516161236852385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33681202783354881649136513 25260902087516161236852385)
      ·
        refine ⟨18945676565637120927639289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25260902087516161236852385 18945676565637120927639289)
        ·
          refine ⟨14209257424227840695729467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18945676565637120927639289 14209257424227840695729467)
          ·
            refine ⟨21313886136341761043594201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14209257424227840695729467 21313886136341761043594201)
            ·
              refine ⟨15985414602256320782695651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21313886136341761043594201 15985414602256320782695651)
              ·
                refine ⟨23978121903384481174043477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15985414602256320782695651 23978121903384481174043477)
                ·
                  refine ⟨140496808027643444379161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23978121903384481174043477 140496808027643444379161)
                  ·
                    rfl

theorem cell23_2462549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_2462549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462549 prefixEnd_2462549 := by exact prefixLift 2462549
  have htrace : WordTrace (prefixWord ++ tailWord_2462549) baseStart_2462549 baseEnd_2462549 := by
    simpa [prefixWord, tailWord_2462549, baseEnd_2462549] using wordTrace_append hprefix tailTrace_2462549
  have hstable : (prefixWord ++ tailWord_2462549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462549).length < 2 ^ (prefixWord ++ tailWord_2462549).sum := by decide
  have hdescent : baseEnd_2462549 < baseStart_2462549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462590 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2462590 : Nat := 118140960795 + 2462590 * 2 ^ 59
def prefixEnd_2462590 : Nat := 4983230072969 + 3 ^ 40 * 2462590 * 2
def baseEnd_2462590 : Nat := 1264492324955625338999761

theorem tailTrace_2462590 : CollatzResearch.WordTrace tailWord_2462590 prefixEnd_2462590 1264492324955625338999761 := by
  unfold tailWord_2462590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11227254518558060216659153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59878690765642987822182149 11227254518558060216659153)
  ·
    refine ⟨8420440888918545162494365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11227254518558060216659153 8420440888918545162494365)
    ·
      refine ⟨3157665333344454435935387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8420440888918545162494365 3157665333344454435935387)
      ·
        refine ⟨4736498000016681653903081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3157665333344454435935387 4736498000016681653903081)
        ·
          refine ⟨3552373500012511240427311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4736498000016681653903081 3552373500012511240427311)
          ·
            refine ⟨5328560250018766860640967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3552373500012511240427311 5328560250018766860640967)
            ·
              refine ⟨7992840375028150290961451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5328560250018766860640967 7992840375028150290961451)
              ·
                refine ⟨11989260562542225436442177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7992840375028150290961451 11989260562542225436442177)
                ·
                  refine ⟨8991945421906669077331633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11989260562542225436442177 8991945421906669077331633)
                  ·
                    refine ⟨6743959066430001807998725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8991945421906669077331633 6743959066430001807998725)
                    ·
                      refine ⟨1264492324955625338999761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6743959066430001807998725 1264492324955625338999761)
                      ·
                        rfl

theorem cell23_2462590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2462590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462590 prefixEnd_2462590 := by exact prefixLift 2462590
  have htrace : WordTrace (prefixWord ++ tailWord_2462590) baseStart_2462590 baseEnd_2462590 := by
    simpa [prefixWord, tailWord_2462590, baseEnd_2462590] using wordTrace_append hprefix tailTrace_2462590
  have hstable : (prefixWord ++ tailWord_2462590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462590).length < 2 ^ (prefixWord ++ tailWord_2462590).sum := by decide
  have hdescent : baseEnd_2462590 < baseStart_2462590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462594 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_2462594 : Nat := 118140960795 + 2462594 * 2 ^ 59
def prefixEnd_2462594 : Nat := 4983230072969 + 3 ^ 40 * 2462594 * 2
def baseEnd_2462594 : Nat := 1264494378878243323349743

theorem tailTrace_2462594 : CollatzResearch.WordTrace tailWord_2462594 prefixEnd_2462594 1264494378878243323349743 := by
  unfold tailWord_2462594
  simp only [CollatzResearch.WordTrace]
  refine ⟨22454545510112497604104709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59878788026966660277612557 22454545510112497604104709)
  ·
    refine ⟨4210227283146093300769633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22454545510112497604104709 4210227283146093300769633)
    ·
      refine ⟨3157670462359569975577225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4210227283146093300769633 3157670462359569975577225)
      ·
        refine ⟨2368252846769677481682919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3157670462359569975577225 2368252846769677481682919)
        ·
          refine ⟨3552379270154516222524379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2368252846769677481682919 3552379270154516222524379)
          ·
            refine ⟨5328568905231774333786569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3552379270154516222524379 5328568905231774333786569)
            ·
              refine ⟨3996426678923830750339927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5328568905231774333786569 3996426678923830750339927)
              ·
                refine ⟨5994640018385746125509891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3996426678923830750339927 5994640018385746125509891)
                ·
                  refine ⟨8991960027578619188264837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5994640018385746125509891 8991960027578619188264837)
                  ·
                    refine ⟨1685992505170991097799657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8991960027578619188264837 1685992505170991097799657)
                    ·
                      refine ⟨1264494378878243323349743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1685992505170991097799657 1264494378878243323349743)
                      ·
                        rfl

theorem cell23_2462594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_2462594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462594 prefixEnd_2462594 := by exact prefixLift 2462594
  have htrace : WordTrace (prefixWord ++ tailWord_2462594) baseStart_2462594 baseEnd_2462594 := by
    simpa [prefixWord, tailWord_2462594, baseEnd_2462594] using wordTrace_append hprefix tailTrace_2462594
  have hstable : (prefixWord ++ tailWord_2462594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462594).length < 2 ^ (prefixWord ++ tailWord_2462594).sum := by decide
  have hdescent : baseEnd_2462594 < baseStart_2462594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462613 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 2, 5]
def baseStart_2462613 : Nat := 118140960795 + 2462613 * 2 ^ 59
def prefixEnd_2462613 : Nat := 4983230072969 + 3 ^ 40 * 2462613 * 2
def baseEnd_2462613 : Nat := 421501378336892916337385

theorem tailTrace_2462613 : CollatzResearch.WordTrace tailWord_2462613 prefixEnd_2462613 421501378336892916337385 := by
  unfold tailWord_2462613
  simp only [CollatzResearch.WordTrace]
  refine ⟨89818875027381156661360493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59879250018254104440906995 89818875027381156661360493)
  ·
    refine ⟨33682078135267933748010185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89818875027381156661360493 33682078135267933748010185)
    ·
      refine ⟨25261558601450950311007639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33682078135267933748010185 25261558601450950311007639)
      ·
        refine ⟨37892337902176425466511459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25261558601450950311007639 37892337902176425466511459)
        ·
          refine ⟨56838506853264638199767189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37892337902176425466511459 56838506853264638199767189)
          ·
            refine ⟨2664305008746779915614087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56838506853264638199767189 2664305008746779915614087)
            ·
              refine ⟨3996457513120169873421131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664305008746779915614087 3996457513120169873421131)
              ·
                refine ⟨5994686269680254810131697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3996457513120169873421131 5994686269680254810131697)
                ·
                  refine ⟨4496014702260191107598773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5994686269680254810131697 4496014702260191107598773)
                  ·
                    refine ⟨421501378336892916337385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4496014702260191107598773 421501378336892916337385)
                    ·
                      rfl

theorem cell23_2462613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_2462613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462613 prefixEnd_2462613 := by exact prefixLift 2462613
  have htrace : WordTrace (prefixWord ++ tailWord_2462613) baseStart_2462613 baseEnd_2462613 := by
    simpa [prefixWord, tailWord_2462613, baseEnd_2462613] using wordTrace_append hprefix tailTrace_2462613
  have hstable : (prefixWord ++ tailWord_2462613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462613).length < 2 ^ (prefixWord ++ tailWord_2462613).sum := by decide
  have hdescent : baseEnd_2462613 < baseStart_2462613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462666 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_2462666 : Nat := 118140960795 + 2462666 * 2 ^ 59
def prefixEnd_2462666 : Nat := 4983230072969 + 3 ^ 40 * 2462666 * 2
def baseEnd_2462666 : Nat := 1264531349485367041649411

theorem tailTrace_2462666 : CollatzResearch.WordTrace tailWord_2462666 prefixEnd_2462666 1264531349485367041649411 := by
  unfold tailWord_2462666
  simp only [CollatzResearch.WordTrace]
  refine ⟨22455202024047286678259963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59880538730792764475359901 22455202024047286678259963)
  ·
    refine ⟨33682803036070930017389945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22455202024047286678259963 33682803036070930017389945)
    ·
      refine ⟨25262102277053197513042459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33682803036070930017389945 25262102277053197513042459)
      ·
        refine ⟨37893153415579796269563689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25262102277053197513042459 37893153415579796269563689)
        ·
          refine ⟨28419865061684847202172767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37893153415579796269563689 28419865061684847202172767)
          ·
            refine ⟨42629797592527270803259151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28419865061684847202172767 42629797592527270803259151)
            ·
              refine ⟨63944696388790906204888727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42629797592527270803259151 63944696388790906204888727)
              ·
                refine ⟨95917044583186359307333091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63944696388790906204888727 95917044583186359307333091)
                ·
                  refine ⟨143875566874779538960999637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95917044583186359307333091 143875566874779538960999637)
                  ·
                    refine ⟨3372083598627645444398429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 143875566874779538960999637 3372083598627645444398429)
                    ·
                      refine ⟨1264531349485367041649411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3372083598627645444398429 1264531349485367041649411)
                      ·
                        rfl

theorem cell23_2462666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_2462666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462666 prefixEnd_2462666 := by exact prefixLift 2462666
  have htrace : WordTrace (prefixWord ++ tailWord_2462666) baseStart_2462666 baseEnd_2462666 := by
    simpa [prefixWord, tailWord_2462666, baseEnd_2462666] using wordTrace_append hprefix tailTrace_2462666
  have hstable : (prefixWord ++ tailWord_2462666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462666).length < 2 ^ (prefixWord ++ tailWord_2462666).sum := by decide
  have hdescent : baseEnd_2462666 < baseStart_2462666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462774 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_2462774 : Nat := 118140960795 + 2462774 * 2 ^ 59
def prefixEnd_2462774 : Nat := 4983230072969 + 3 ^ 40 * 2462774 * 2
def baseEnd_2462774 : Nat := 1264586805396052619098915

theorem tailTrace_2462774 : CollatzResearch.WordTrace tailWord_2462774 prefixEnd_2462774 1264586805396052619098915 := by
  unfold tailWord_2462774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5614046698737367572373211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59883164786531920771980917 5614046698737367572373211)
  ·
    refine ⟨8421070048106051358559817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5614046698737367572373211 8421070048106051358559817)
    ·
      refine ⟨6315802536079538518919863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8421070048106051358559817 6315802536079538518919863)
      ·
        refine ⟨9473703804119307778379795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6315802536079538518919863 9473703804119307778379795)
        ·
          refine ⟨14210555706178961667569693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9473703804119307778379795 14210555706178961667569693)
          ·
            refine ⟨5328958389817110625338635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14210555706178961667569693 5328958389817110625338635)
            ·
              refine ⟨7993437584725665938007953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5328958389817110625338635 7993437584725665938007953)
              ·
                refine ⟨5995078188544249453505965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7993437584725665938007953 5995078188544249453505965)
                ·
                  refine ⟨2248154320704093545064737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5995078188544249453505965 2248154320704093545064737)
                  ·
                    refine ⟨1686115740528070158798553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2248154320704093545064737 1686115740528070158798553)
                    ·
                      refine ⟨1264586805396052619098915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1686115740528070158798553 1264586805396052619098915)
                      ·
                        rfl

theorem cell23_2462774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_2462774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462774 prefixEnd_2462774 := by exact prefixLift 2462774
  have htrace : WordTrace (prefixWord ++ tailWord_2462774) baseStart_2462774 baseEnd_2462774 := by
    simpa [prefixWord, tailWord_2462774, baseEnd_2462774] using wordTrace_append hprefix tailTrace_2462774
  have hstable : (prefixWord ++ tailWord_2462774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462774).length < 2 ^ (prefixWord ++ tailWord_2462774).sum := by decide
  have hdescent : baseEnd_2462774 < baseStart_2462774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462823 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 2, 6]
def baseStart_2462823 : Nat := 118140960795 + 2462823 * 2 ^ 59
def prefixEnd_2462823 : Nat := 4983230072969 + 3 ^ 40 * 2462823 * 2
def baseEnd_2462823 : Nat := 421537321982707642462063

theorem tailTrace_2462823 : CollatzResearch.WordTrace tailWord_2462823 prefixEnd_2462823 421537321982707642462063 := by
  unfold tailWord_2462823
  simp only [CollatzResearch.WordTrace]
  refine ⟨89826534356620362526505123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59884356237746908351003415 89826534356620362526505123)
  ·
    refine ⟨134739801534930543789757685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89826534356620362526505123 134739801534930543789757685)
    ·
      refine ⟨12631856393899738480289783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134739801534930543789757685 12631856393899738480289783)
      ·
        refine ⟨18947784590849607720434675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12631856393899738480289783 18947784590849607720434675)
        ·
          refine ⟨28421676886274411580652013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18947784590849607720434675 28421676886274411580652013)
          ·
            refine ⟨10658128832352904342744505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28421676886274411580652013 10658128832352904342744505)
            ·
              refine ⟨7993596624264678257058379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10658128832352904342744505 7993596624264678257058379)
              ·
                refine ⟨11990394936397017385587569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7993596624264678257058379 11990394936397017385587569)
                ·
                  refine ⟨8992796202297763039190677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11990394936397017385587569 8992796202297763039190677)
                  ·
                    refine ⟨421537321982707642462063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8992796202297763039190677 421537321982707642462063)
                    ·
                      rfl

theorem cell23_2462823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_2462823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462823 prefixEnd_2462823 := by exact prefixLift 2462823
  have htrace : WordTrace (prefixWord ++ tailWord_2462823) baseStart_2462823 baseEnd_2462823 := by
    simpa [prefixWord, tailWord_2462823, baseEnd_2462823] using wordTrace_append hprefix tailTrace_2462823
  have hstable : (prefixWord ++ tailWord_2462823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462823).length < 2 ^ (prefixWord ++ tailWord_2462823).sum := by decide
  have hdescent : baseEnd_2462823 < baseStart_2462823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462824 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2462824 : Nat := 118140960795 + 2462824 * 2 ^ 59
def prefixEnd_2462824 : Nat := 4983230072969 + 3 ^ 40 * 2462824 * 2
def baseEnd_2462824 : Nat := 1264612479428777423473685

theorem tailTrace_2462824 : CollatzResearch.WordTrace tailWord_2462824 prefixEnd_2462824 1264612479428777423473685 := by
  unfold tailWord_2462824
  simp only [CollatzResearch.WordTrace]
  refine ⟨44913285414808369848645763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59884380553077826464861017 44913285414808369848645763)
  ·
    refine ⟨67369928122212554772968645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44913285414808369848645763 67369928122212554772968645)
    ·
      refine ⟨12631861522914854019931621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67369928122212554772968645 12631861522914854019931621)
      ·
        refine ⟨2368474035546535128737179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12631861522914854019931621 2368474035546535128737179)
        ·
          refine ⟨3552711053319802693105769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2368474035546535128737179 3552711053319802693105769)
          ·
            refine ⟨2664533289989852019829327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3552711053319802693105769 2664533289989852019829327)
            ·
              refine ⟨3996799934984778029743991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664533289989852019829327 3996799934984778029743991)
              ·
                refine ⟨5995199902477167044615987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3996799934984778029743991 5995199902477167044615987)
                ·
                  refine ⟨8992799853715750566923981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5995199902477167044615987 8992799853715750566923981)
                  ·
                    refine ⟨3372299945143406462596493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8992799853715750566923981 3372299945143406462596493)
                    ·
                      refine ⟨1264612479428777423473685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3372299945143406462596493 1264612479428777423473685)
                      ·
                        rfl

theorem cell23_2462824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2462824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462824 prefixEnd_2462824 := by exact prefixLift 2462824
  have htrace : WordTrace (prefixWord ++ tailWord_2462824) baseStart_2462824 baseEnd_2462824 := by
    simpa [prefixWord, tailWord_2462824, baseEnd_2462824] using wordTrace_append hprefix tailTrace_2462824
  have hstable : (prefixWord ++ tailWord_2462824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462824).length < 2 ^ (prefixWord ++ tailWord_2462824).sum := by decide
  have hdescent : baseEnd_2462824 < baseStart_2462824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462910 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_2462910 : Nat := 118140960795 + 2462910 * 2 ^ 59
def prefixEnd_2462910 : Nat := 4983230072969 + 3 ^ 40 * 2462910 * 2
def baseEnd_2462910 : Nat := 1264656638765064086998289

theorem tailTrace_2462910 : CollatzResearch.WordTrace tailWord_2462910 prefixEnd_2462910 1264656638765064086998289 := by
  unfold tailWord_2462910
  simp only [CollatzResearch.WordTrace]
  refine ⟨11228713438413147048115273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59886471671536784256614789 11228713438413147048115273)
  ·
    refine ⟨8421535078809860286086455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11228713438413147048115273 8421535078809860286086455)
    ·
      refine ⟨12632302618214790429129683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8421535078809860286086455 12632302618214790429129683)
      ·
        refine ⟨18948453927322185643694525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12632302618214790429129683 18948453927322185643694525)
        ·
          refine ⟨7105670222745819616385447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18948453927322185643694525 7105670222745819616385447)
          ·
            refine ⟨10658505334118729424578171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7105670222745819616385447 10658505334118729424578171)
            ·
              refine ⟨15987758001178094136867257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10658505334118729424578171 15987758001178094136867257)
              ·
                refine ⟨11990818500883570602650443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15987758001178094136867257 11990818500883570602650443)
                ·
                  refine ⟨17986227751325355903975665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11990818500883570602650443 17986227751325355903975665)
                  ·
                    refine ⟨13489670813494016927981749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17986227751325355903975665 13489670813494016927981749)
                    ·
                      refine ⟨1264656638765064086998289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13489670813494016927981749 1264656638765064086998289)
                      ·
                        rfl

theorem cell23_2462910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_2462910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462910 prefixEnd_2462910 := by exact prefixLift 2462910
  have htrace : WordTrace (prefixWord ++ tailWord_2462910) baseStart_2462910 baseEnd_2462910 := by
    simpa [prefixWord, tailWord_2462910, baseEnd_2462910] using wordTrace_append hprefix tailTrace_2462910
  have hstable : (prefixWord ++ tailWord_2462910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462910).length < 2 ^ (prefixWord ++ tailWord_2462910).sum := by decide
  have hdescent : baseEnd_2462910 < baseStart_2462910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462920 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_2462920 : Nat := 118140960795 + 2462920 * 2 ^ 59
def prefixEnd_2462920 : Nat := 4983230072969 + 3 ^ 40 * 2462920 * 2
def baseEnd_2462920 : Nat := 1264661773571609047873243

theorem tailTrace_2462920 : CollatzResearch.WordTrace tailWord_2462920 prefixEnd_2462920 1264661773571609047873243 := by
  unfold tailWord_2462920
  simp only [CollatzResearch.WordTrace]
  refine ⟨44915036118634474046393107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59886714824845965395190809 44915036118634474046393107)
  ·
    refine ⟨67372554177951711069589661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44915036118634474046393107 67372554177951711069589661)
    ·
      refine ⟨25264707816731891651096123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67372554177951711069589661 25264707816731891651096123)
      ·
        refine ⟨37897061725097837476644185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25264707816731891651096123 37897061725097837476644185)
        ·
          refine ⟨28422796293823378107483139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37897061725097837476644185 28422796293823378107483139)
          ·
            refine ⟨42634194440735067161224709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28422796293823378107483139 42634194440735067161224709)
            ·
              refine ⟨7993911457637825092729633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42634194440735067161224709 7993911457637825092729633)
              ·
                refine ⟨5995433593228368819547225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7993911457637825092729633 5995433593228368819547225)
                ·
                  refine ⟨4496575194921276614660419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5995433593228368819547225 4496575194921276614660419)
                  ·
                    refine ⟨6744862792381914921990629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4496575194921276614660419 6744862792381914921990629)
                    ·
                      refine ⟨1264661773571609047873243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6744862792381914921990629 1264661773571609047873243)
                      ·
                        rfl

theorem cell23_2462920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_2462920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462920 prefixEnd_2462920 := by exact prefixLift 2462920
  have htrace : WordTrace (prefixWord ++ tailWord_2462920) baseStart_2462920 baseEnd_2462920 := by
    simpa [prefixWord, tailWord_2462920, baseEnd_2462920] using wordTrace_append hprefix tailTrace_2462920
  have hstable : (prefixWord ++ tailWord_2462920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462920).length < 2 ^ (prefixWord ++ tailWord_2462920).sum := by decide
  have hdescent : baseEnd_2462920 < baseStart_2462920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462957 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2462957 : Nat := 118140960795 + 2462957 * 2 ^ 59
def prefixEnd_2462957 : Nat := 4983230072969 + 3 ^ 40 * 2462957 * 2
def baseEnd_2462957 : Nat := 1264680772355825403110573

theorem tailTrace_2462957 : CollatzResearch.WordTrace tailWord_2462957 prefixEnd_2462957 1264680772355825403110573 := by
  unfold tailWord_2462957
  simp only [CollatzResearch.WordTrace]
  refine ⟨89831421738134903411883125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59887614492089935607922083 89831421738134903411883125)
  ·
    refine ⟨8421695787950147194864043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89831421738134903411883125 8421695787950147194864043)
    ·
      refine ⟨12632543681925220792296065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8421695787950147194864043 12632543681925220792296065)
      ·
        refine ⟨9474407761443915594222049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12632543681925220792296065 9474407761443915594222049)
        ·
          refine ⟨7105805821082936695666537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9474407761443915594222049 7105805821082936695666537)
          ·
            refine ⟨5329354365812202521749903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7105805821082936695666537 5329354365812202521749903)
            ·
              refine ⟨7994031548718303782624855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5329354365812202521749903 7994031548718303782624855)
              ·
                refine ⟨11991047323077455673937283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7994031548718303782624855 11991047323077455673937283)
                ·
                  refine ⟨17986570984616183510905925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11991047323077455673937283 17986570984616183510905925)
                  ·
                    refine ⟨3372482059615534408294861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17986570984616183510905925 3372482059615534408294861)
                    ·
                      refine ⟨1264680772355825403110573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3372482059615534408294861 1264680772355825403110573)
                      ·
                        rfl

theorem cell23_2462957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2462957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462957 prefixEnd_2462957 := by exact prefixLift 2462957
  have htrace : WordTrace (prefixWord ++ tailWord_2462957) baseStart_2462957 baseEnd_2462957 := by
    simpa [prefixWord, tailWord_2462957, baseEnd_2462957] using wordTrace_append hprefix tailTrace_2462957
  have hstable : (prefixWord ++ tailWord_2462957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462957).length < 2 ^ (prefixWord ++ tailWord_2462957).sum := by decide
  have hdescent : baseEnd_2462957 < baseStart_2462957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462977 : List Nat := [1, 2, 4, 1, 1, 5, 1, 2, 6]
def baseStart_2462977 : Nat := 118140960795 + 2462977 * 2 ^ 59
def prefixEnd_2462977 : Nat := 4983230072969 + 3 ^ 40 * 2462977 * 2
def baseEnd_2462977 : Nat := 140521226885435036095609

theorem tailTrace_2462977 : CollatzResearch.WordTrace tailWord_2462977 prefixEnd_2462977 140521226885435036095609 := by
  unfold tailWord_2462977
  simp only [CollatzResearch.WordTrace]
  refine ⟨89832151198062446827611185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59888100798708297885074123 89832151198062446827611185)
  ·
    refine ⟨67374113398546835120708389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89832151198062446827611185 67374113398546835120708389)
    ·
      refine ⟨12632646262227531585132823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67374113398546835120708389 12632646262227531585132823)
      ·
        refine ⟨18948969393341297377699235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12632646262227531585132823 18948969393341297377699235)
        ·
          refine ⟨28423454090011946066548853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18948969393341297377699235 28423454090011946066548853)
          ·
            refine ⟨2664698820938619943738955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28423454090011946066548853 2664698820938619943738955)
            ·
              refine ⟨3997048231407929915608433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664698820938619943738955 3997048231407929915608433)
              ·
                refine ⟨2997786173555947436706325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3997048231407929915608433 2997786173555947436706325)
                ·
                  refine ⟨140521226885435036095609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2997786173555947436706325 140521226885435036095609)
                  ·
                    rfl

theorem cell23_2462977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 6].length) (baseStart_2462977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462977 prefixEnd_2462977 := by exact prefixLift 2462977
  have htrace : WordTrace (prefixWord ++ tailWord_2462977) baseStart_2462977 baseEnd_2462977 := by
    simpa [prefixWord, tailWord_2462977, baseEnd_2462977] using wordTrace_append hprefix tailTrace_2462977
  have hstable : (prefixWord ++ tailWord_2462977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462977).length < 2 ^ (prefixWord ++ tailWord_2462977).sum := by decide
  have hdescent : baseEnd_2462977 < baseStart_2462977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462980 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2462980 : Nat := 118140960795 + 2462980 * 2 ^ 59
def prefixEnd_2462980 : Nat := 4983230072969 + 3 ^ 40 * 2462980 * 2
def baseEnd_2462980 : Nat := 1264692582410878813122967

theorem tailTrace_2462980 : CollatzResearch.WordTrace tailWord_2462980 prefixEnd_2462980 1264692582410878813122967 := by
  unfold tailWord_2462980
  simp only [CollatzResearch.WordTrace]
  refine ⟨44916130308525789169985197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59888173744701052226646929 44916130308525789169985197)
  ·
    refine ⟨16843548865697170938744449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44916130308525789169985197 16843548865697170938744449)
    ·
      refine ⟨12632661649272878204058337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16843548865697170938744449 12632661649272878204058337)
      ·
        refine ⟨9474496236954658653043753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12632661649272878204058337 9474496236954658653043753)
        ·
          refine ⟨7105872177715993989782815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9474496236954658653043753 7105872177715993989782815)
          ·
            refine ⟨10658808266573990984674223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7105872177715993989782815 10658808266573990984674223)
            ·
              refine ⟨15988212399860986477011335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10658808266573990984674223 15988212399860986477011335)
              ·
                refine ⟨23982318599791479715517003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15988212399860986477011335 23982318599791479715517003)
                ·
                  refine ⟨35973477899687219573275505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23982318599791479715517003 35973477899687219573275505)
                  ·
                    refine ⟨26980108424765414679956629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35973477899687219573275505 26980108424765414679956629)
                    ·
                      refine ⟨1264692582410878813122967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26980108424765414679956629 1264692582410878813122967)
                      ·
                        rfl

theorem cell23_2462980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2462980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462980 prefixEnd_2462980 := by exact prefixLift 2462980
  have htrace : WordTrace (prefixWord ++ tailWord_2462980) baseStart_2462980 baseEnd_2462980 := by
    simpa [prefixWord, tailWord_2462980, baseEnd_2462980] using wordTrace_append hprefix tailTrace_2462980
  have hstable : (prefixWord ++ tailWord_2462980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462980).length < 2 ^ (prefixWord ++ tailWord_2462980).sum := by decide
  have hdescent : baseEnd_2462980 < baseStart_2462980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462987 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 3, 1, 3]
def baseStart_2462987 : Nat := 118140960795 + 2462987 * 2 ^ 59
def prefixEnd_2462987 : Nat := 4983230072969 + 3 ^ 40 * 2462987 * 2
def baseEnd_2462987 : Nat := 1264696176775460285735435

theorem tailTrace_2462987 : CollatzResearch.WordTrace tailWord_2462987 prefixEnd_2462987 1264696176775460285735435 := by
  unfold tailWord_2462987
  simp only [CollatzResearch.WordTrace]
  refine ⟨89832515928026218535475215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59888343952017479023650143 89832515928026218535475215)
  ·
    refine ⟨134748773892039327803212823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89832515928026218535475215 134748773892039327803212823)
    ·
      refine ⟨202123160838058991704819235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134748773892039327803212823 202123160838058991704819235)
      ·
        refine ⟨303184741257088487557228853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202123160838058991704819235 303184741257088487557228853)
        ·
          refine ⟨28423569492852045708490205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 303184741257088487557228853 28423569492852045708490205)
          ·
            refine ⟨10658838559819517140683827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28423569492852045708490205 10658838559819517140683827)
            ·
              refine ⟨15988257839729275711025741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10658838559819517140683827 15988257839729275711025741)
              ·
                refine ⟨5995596689898478391634653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15988257839729275711025741 5995596689898478391634653)
                ·
                  refine ⟨2248348758711929396862995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5995596689898478391634653 2248348758711929396862995)
                  ·
                    refine ⟨3372523138067894095294493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2248348758711929396862995 3372523138067894095294493)
                    ·
                      refine ⟨1264696176775460285735435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3372523138067894095294493 1264696176775460285735435)
                      ·
                        rfl

theorem cell23_2462987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 1, 3].length) (baseStart_2462987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2462987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2462987 prefixEnd_2462987 := by exact prefixLift 2462987
  have htrace : WordTrace (prefixWord ++ tailWord_2462987) baseStart_2462987 baseEnd_2462987 := by
    simpa [prefixWord, tailWord_2462987, baseEnd_2462987] using wordTrace_append hprefix tailTrace_2462987
  have hstable : (prefixWord ++ tailWord_2462987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462987).length < 2 ^ (prefixWord ++ tailWord_2462987).sum := by decide
  have hdescent : baseEnd_2462987 < baseStart_2462987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463027 : List Nat := [1, 1, 1, 2, 5, 2, 2, 3, 1, 1, 4]
def baseStart_2463027 : Nat := 118140960795 + 2463027 * 2 ^ 59
def prefixEnd_2463027 : Nat := 4983230072969 + 3 ^ 40 * 2463027 * 2
def baseEnd_2463027 : Nat := 1264716716001640129235251

theorem tailTrace_2463027 : CollatzResearch.WordTrace tailWord_2463027 prefixEnd_2463027 1264716716001640129235251 := by
  unfold tailWord_2463027
  simp only [CollatzResearch.WordTrace]
  refine ⟨89833974847881305366931335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59889316565254203577954223 89833974847881305366931335)
  ·
    refine ⟨134750962271821958050397003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89833974847881305366931335 134750962271821958050397003)
    ·
      refine ⟨202126443407732937075595505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134750962271821958050397003 202126443407732937075595505)
      ·
        refine ⟨151594832555799702806696629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202126443407732937075595505 151594832555799702806696629)
        ·
          refine ⟨14212015552106222138127809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151594832555799702806696629 14212015552106222138127809)
          ·
            refine ⟨10659011664079666603595857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14212015552106222138127809 10659011664079666603595857)
            ·
              refine ⟨7994258748059749952696893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10659011664079666603595857 7994258748059749952696893)
              ·
                refine ⟨2997847030522406232261335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7994258748059749952696893 2997847030522406232261335)
                ·
                  refine ⟨4496770545783609348392003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2997847030522406232261335 4496770545783609348392003)
                  ·
                    refine ⟨6745155818675414022588005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4496770545783609348392003 6745155818675414022588005)
                    ·
                      refine ⟨1264716716001640129235251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6745155818675414022588005 1264716716001640129235251)
                      ·
                        rfl

theorem cell23_2463027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 1, 4].length) (baseStart_2463027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463027 prefixEnd_2463027 := by exact prefixLift 2463027
  have htrace : WordTrace (prefixWord ++ tailWord_2463027) baseStart_2463027 baseEnd_2463027 := by
    simpa [prefixWord, tailWord_2463027, baseEnd_2463027] using wordTrace_append hprefix tailTrace_2463027
  have hstable : (prefixWord ++ tailWord_2463027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463027).length < 2 ^ (prefixWord ++ tailWord_2463027).sum := by decide
  have hdescent : baseEnd_2463027 < baseStart_2463027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463038 : List Nat := [4, 2, 1, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_2463038 : Nat := 118140960795 + 2463038 * 2 ^ 59
def prefixEnd_2463038 : Nat := 4983230072969 + 3 ^ 40 * 2463038 * 2
def baseEnd_2463038 : Nat := 1264722364288839586197701

theorem tailTrace_2463038 : CollatzResearch.WordTrace tailWord_2463038 prefixEnd_2463038 1264722364288839586197701 := by
  unfold tailWord_2463038
  simp only [CollatzResearch.WordTrace]
  refine ⟨11229297006355181780697721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59889584033894302830387845 11229297006355181780697721)
  ·
    refine ⟨8421972754766386335523291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11229297006355181780697721 8421972754766386335523291)
    ·
      refine ⟨12632959132149579503284937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8421972754766386335523291 12632959132149579503284937)
      ·
        refine ⟨9474719349112184627463703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12632959132149579503284937 9474719349112184627463703)
        ·
          refine ⟨14212079023668276941195555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9474719349112184627463703 14212079023668276941195555)
          ·
            refine ⟨21318118535502415411793333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14212079023668276941195555 21318118535502415411793333)
            ·
              refine ⟨1998573612703351444855625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21318118535502415411793333 1998573612703351444855625)
              ·
                refine ⟨1498930209527513583641719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1998573612703351444855625 1498930209527513583641719)
                ·
                  refine ⟨2248395314291270375462579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498930209527513583641719 2248395314291270375462579)
                  ·
                    refine ⟨3372592971436905563193869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2248395314291270375462579 3372592971436905563193869)
                    ·
                      refine ⟨1264722364288839586197701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3372592971436905563193869 1264722364288839586197701)
                      ·
                        rfl

theorem cell23_2463038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_2463038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463038 prefixEnd_2463038 := by exact prefixLift 2463038
  have htrace : WordTrace (prefixWord ++ tailWord_2463038) baseStart_2463038 baseEnd_2463038 := by
    simpa [prefixWord, tailWord_2463038, baseEnd_2463038] using wordTrace_append hprefix tailTrace_2463038
  have hstable : (prefixWord ++ tailWord_2463038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463038).length < 2 ^ (prefixWord ++ tailWord_2463038).sum := by decide
  have hdescent : baseEnd_2463038 < baseStart_2463038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463077 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 1, 3, 3]
def baseStart_2463077 : Nat := 118140960795 + 2463077 * 2 ^ 59
def prefixEnd_2463077 : Nat := 4983230072969 + 3 ^ 40 * 2463077 * 2
def baseEnd_2463077 : Nat := 1264742390034364933610021

theorem tailTrace_2463077 : CollatzResearch.WordTrace tailWord_2463077 prefixEnd_2463077 1264742390034364933610021 := by
  unfold tailWord_2463077
  simp only [CollatzResearch.WordTrace]
  refine ⟨89835798497700163906251485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59890532331800109270834323 89835798497700163906251485)
  ·
    refine ⟨33688424436637561464844307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89835798497700163906251485 33688424436637561464844307)
    ·
      refine ⟨50532636654956342197266461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33688424436637561464844307 50532636654956342197266461)
      ·
        refine ⟨18949738745608628323974923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50532636654956342197266461 18949738745608628323974923)
        ·
          refine ⟨28424608118412942485962385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18949738745608628323974923 28424608118412942485962385)
          ·
            refine ⟨21318456088809706864471789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28424608118412942485962385 21318456088809706864471789)
            ·
              refine ⟨7994421033303640074176921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21318456088809706864471789 7994421033303640074176921)
              ·
                refine ⟨5995815774977730055632691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7994421033303640074176921 5995815774977730055632691)
                ·
                  refine ⟨8993723662466595083449037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5995815774977730055632691 8993723662466595083449037)
                  ·
                    refine ⟨3372646373424973156293389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8993723662466595083449037 3372646373424973156293389)
                    ·
                      refine ⟨1264742390034364933610021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3372646373424973156293389 1264742390034364933610021)
                      ·
                        rfl

theorem cell23_2463077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_2463077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463077 prefixEnd_2463077 := by exact prefixLift 2463077
  have htrace : WordTrace (prefixWord ++ tailWord_2463077) baseStart_2463077 baseEnd_2463077 := by
    simpa [prefixWord, tailWord_2463077, baseEnd_2463077] using wordTrace_append hprefix tailTrace_2463077
  have hstable : (prefixWord ++ tailWord_2463077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463077).length < 2 ^ (prefixWord ++ tailWord_2463077).sum := by decide
  have hdescent : baseEnd_2463077 < baseStart_2463077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463100 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_2463100 : Nat := 118140960795 + 2463100 * 2 ^ 59
def prefixEnd_2463100 : Nat := 4983230072969 + 3 ^ 40 * 2463100 * 2
def baseEnd_2463100 : Nat := 1264754200089418343622415

theorem tailTrace_2463100 : CollatzResearch.WordTrace tailWord_2463100 prefixEnd_2463100 1264754200089418343622415 := by
  unfold tailWord_2463100
  simp only [CollatzResearch.WordTrace]
  refine ⟨44918318688308419417169377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59891091584411225889559169 44918318688308419417169377)
  ·
    refine ⟨33688739016231314562877033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44918318688308419417169377 33688739016231314562877033)
    ·
      refine ⟨25266554262173485922157775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33688739016231314562877033 25266554262173485922157775)
      ·
        refine ⟨37899831393260228883236663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25266554262173485922157775 37899831393260228883236663)
        ·
          refine ⟨56849747089890343324854995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37899831393260228883236663 56849747089890343324854995)
          ·
            refine ⟨85274620634835514987282493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56849747089890343324854995 85274620634835514987282493)
            ·
              refine ⟨31977982738063318120230935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85274620634835514987282493 31977982738063318120230935)
              ·
                refine ⟨47966974107094977180346403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31977982738063318120230935 47966974107094977180346403)
                ·
                  refine ⟨71950461160642465770519605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47966974107094977180346403 71950461160642465770519605)
                  ·
                    refine ⟨6745355733810231165986213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71950461160642465770519605 6745355733810231165986213)
                    ·
                      refine ⟨1264754200089418343622415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6745355733810231165986213 1264754200089418343622415)
                      ·
                        rfl

theorem cell23_2463100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_2463100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463100 prefixEnd_2463100 := by exact prefixLift 2463100
  have htrace : WordTrace (prefixWord ++ tailWord_2463100) baseStart_2463100 baseEnd_2463100 := by
    simpa [prefixWord, tailWord_2463100, baseEnd_2463100] using wordTrace_append hprefix tailTrace_2463100
  have hstable : (prefixWord ++ tailWord_2463100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463100).length < 2 ^ (prefixWord ++ tailWord_2463100).sum := by decide
  have hdescent : baseEnd_2463100 < baseStart_2463100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463138 : List Nat := [3, 3, 1, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_2463138 : Nat := 118140960795 + 2463138 * 2 ^ 59
def prefixEnd_2463138 : Nat := 4983230072969 + 3 ^ 40 * 2463138 * 2
def baseEnd_2463138 : Nat := 1264773712354289194947241

theorem tailTrace_2463138 : CollatzResearch.WordTrace tailWord_2463138 prefixEnd_2463138 1264773712354289194947241 := by
  unfold tailWord_2463138
  simp only [CollatzResearch.WordTrace]
  refine ⟨22459505837619792831055517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59892015566986114216148045 22459505837619792831055517)
  ·
    refine ⟨8422314689107422311645819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22459505837619792831055517 8422314689107422311645819)
    ·
      refine ⟨12633472033661133467468729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8422314689107422311645819 12633472033661133467468729)
      ·
        refine ⟨9475104025245850100601547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12633472033661133467468729 9475104025245850100601547)
        ·
          refine ⟨14212656037868775150902321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9475104025245850100601547 14212656037868775150902321)
          ·
            refine ⟨10659492028401581363176741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14212656037868775150902321 10659492028401581363176741)
            ·
              refine ⟨1998654755325296505595639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10659492028401581363176741 1998654755325296505595639)
              ·
                refine ⟨2997982132987944758393459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998654755325296505595639 2997982132987944758393459)
                ·
                  refine ⟨4496973199481917137590189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2997982132987944758393459 4496973199481917137590189)
                  ·
                    refine ⟨1686364949805718926596321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4496973199481917137590189 1686364949805718926596321)
                    ·
                      refine ⟨1264773712354289194947241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1686364949805718926596321 1264773712354289194947241)
                      ·
                        rfl

theorem cell23_2463138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_2463138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463138 prefixEnd_2463138 := by exact prefixLift 2463138
  have htrace : WordTrace (prefixWord ++ tailWord_2463138) baseStart_2463138 baseEnd_2463138 := by
    simpa [prefixWord, tailWord_2463138, baseEnd_2463138] using wordTrace_append hprefix tailTrace_2463138
  have hstable : (prefixWord ++ tailWord_2463138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463138).length < 2 ^ (prefixWord ++ tailWord_2463138).sum := by decide
  have hdescent : baseEnd_2463138 < baseStart_2463138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463140 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 11]
def baseStart_2463140 : Nat := 118140960795 + 2463140 * 2 ^ 59
def prefixEnd_2463140 : Nat := 4983230072969 + 3 ^ 40 * 2463140 * 2
def baseEnd_2463140 : Nat := 140530526590622020791359

theorem tailTrace_2463140 : CollatzResearch.WordTrace tailWord_2463140 prefixEnd_2463140 140530526590622020791359 := by
  unfold tailWord_2463140
  simp only [CollatzResearch.WordTrace]
  refine ⟨44919048148235962832897437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59892064197647950443863249 44919048148235962832897437)
  ·
    refine ⟨16844643055588486062336539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44919048148235962832897437 16844643055588486062336539)
    ·
      refine ⟨25266964583382729093504809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16844643055588486062336539 25266964583382729093504809)
      ·
        refine ⟨18950223437537046820128607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25266964583382729093504809 18950223437537046820128607)
        ·
          refine ⟨28425335156305570230192911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18950223437537046820128607 28425335156305570230192911)
          ·
            refine ⟨42638002734458355345289367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28425335156305570230192911 42638002734458355345289367)
            ·
              refine ⟨63957004101687533017934051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42638002734458355345289367 63957004101687533017934051)
              ·
                refine ⟨95935506152531299526901077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63957004101687533017934051 95935506152531299526901077)
                ·
                  refine ⟨140530526590622020791359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 95935506152531299526901077 140530526590622020791359)
                  ·
                    rfl

theorem cell23_2463140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_2463140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463140 prefixEnd_2463140 := by exact prefixLift 2463140
  have htrace : WordTrace (prefixWord ++ tailWord_2463140) baseStart_2463140 baseEnd_2463140 := by
    simpa [prefixWord, tailWord_2463140, baseEnd_2463140] using wordTrace_append hprefix tailTrace_2463140
  have hstable : (prefixWord ++ tailWord_2463140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463140).length < 2 ^ (prefixWord ++ tailWord_2463140).sum := by decide
  have hdescent : baseEnd_2463140 < baseStart_2463140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463157 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 7]
def baseStart_2463157 : Nat := 118140960795 + 2463157 * 2 ^ 59
def prefixEnd_2463157 : Nat := 4983230072969 + 3 ^ 40 * 2463157 * 2
def baseEnd_2463157 : Nat := 140531496498524957845517

theorem tailTrace_2463157 : CollatzResearch.WordTrace tailWord_2463157 prefixEnd_2463157 140531496498524957845517 := by
  unfold tailWord_2463157
  simp only [CollatzResearch.WordTrace]
  refine ⟨89838716337410337569163725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59892477558273558379442483 89838716337410337569163725)
  ·
    refine ⟨33689518626528876588436397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89838716337410337569163725 33689518626528876588436397)
    ·
      refine ⟨12633569484948328720663649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33689518626528876588436397 12633569484948328720663649)
      ·
        refine ⟨9475177113711246540497737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12633569484948328720663649 9475177113711246540497737)
        ·
          refine ⟨7106382835283434905373303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9475177113711246540497737 7106382835283434905373303)
          ·
            refine ⟨10659574252925152358059955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7106382835283434905373303 10659574252925152358059955)
            ·
              refine ⟨15989361379387728537089933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10659574252925152358059955 15989361379387728537089933)
              ·
                refine ⟨5996010517270398201408725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15989361379387728537089933 5996010517270398201408725)
                ·
                  refine ⟨140531496498524957845517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5996010517270398201408725 140531496498524957845517)
                  ·
                    rfl

theorem cell23_2463157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_2463157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463157 prefixEnd_2463157 := by exact prefixLift 2463157
  have htrace : WordTrace (prefixWord ++ tailWord_2463157) baseStart_2463157 baseEnd_2463157 := by
    simpa [prefixWord, tailWord_2463157, baseEnd_2463157] using wordTrace_append hprefix tailTrace_2463157
  have hstable : (prefixWord ++ tailWord_2463157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463157).length < 2 ^ (prefixWord ++ tailWord_2463157).sum := by decide
  have hdescent : baseEnd_2463157 < baseStart_2463157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463264 : List Nat := [2, 1, 1, 6, 1, 1, 1, 4, 6]
def baseStart_2463264 : Nat := 118140960795 + 2463264 * 2 ^ 59
def prefixEnd_2463264 : Nat := 4983230072969 + 3 ^ 40 * 2463264 * 2
def baseEnd_2463264 : Nat := 140537601212972855774629

theorem tailTrace_2463264 : CollatzResearch.WordTrace tailWord_2463264 prefixEnd_2463264 140537601212972855774629 := by
  unfold tailWord_2463264
  simp only [CollatzResearch.WordTrace]
  refine ⟨44921309474011347421654423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59895079298681796562205897 44921309474011347421654423)
  ·
    refine ⟨67381964211017021132481635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44921309474011347421654423 67381964211017021132481635)
    ·
      refine ⟨101072946316525531698722453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67381964211017021132481635 101072946316525531698722453)
      ·
        refine ⟨4737794358587134298377615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 101072946316525531698722453 4737794358587134298377615)
        ·
          refine ⟨7106691537880701447566423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4737794358587134298377615 7106691537880701447566423)
          ·
            refine ⟨10660037306821052171349635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7106691537880701447566423 10660037306821052171349635)
            ·
              refine ⟨15990055960231578257024453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10660037306821052171349635 15990055960231578257024453)
              ·
                refine ⟨2998135492543420923192085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15990055960231578257024453 2998135492543420923192085)
                ·
                  refine ⟨140537601212972855774629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2998135492543420923192085 140537601212972855774629)
                  ·
                    rfl

theorem cell23_2463264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 6].length) (baseStart_2463264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463264 prefixEnd_2463264 := by exact prefixLift 2463264
  have htrace : WordTrace (prefixWord ++ tailWord_2463264) baseStart_2463264 baseEnd_2463264 := by
    simpa [prefixWord, tailWord_2463264, baseEnd_2463264] using wordTrace_append hprefix tailTrace_2463264
  have hstable : (prefixWord ++ tailWord_2463264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463264).length < 2 ^ (prefixWord ++ tailWord_2463264).sum := by decide
  have hdescent : baseEnd_2463264 < baseStart_2463264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463302 : List Nat := [6, 1, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_2463302 : Nat := 118140960795 + 2463302 * 2 ^ 59
def prefixEnd_2463302 : Nat := 4983230072969 + 3 ^ 40 * 2463302 * 2
def baseEnd_2463302 : Nat := 421619307727208851098829

theorem tailTrace_2463302 : CollatzResearch.WordTrace tailWord_2463302 prefixEnd_2463302 421619307727208851098829 := by
  unfold tailWord_2463302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2807625153808907104162255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59896003281256684888794773 2807625153808907104162255)
  ·
    refine ⟨4211437730713360656243383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2807625153808907104162255 4211437730713360656243383)
    ·
      refine ⟨6317156596070040984365075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4211437730713360656243383 6317156596070040984365075)
      ·
        refine ⟨9475734894105061476547613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6317156596070040984365075 9475734894105061476547613)
        ·
          refine ⟨3553400585289398053705355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9475734894105061476547613 3553400585289398053705355)
          ·
            refine ⟨5330100877934097080558033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3553400585289398053705355 5330100877934097080558033)
            ·
              refine ⟨3997575658450572810418525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5330100877934097080558033 3997575658450572810418525)
              ·
                refine ⟨1499090871918964803906947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3997575658450572810418525 1499090871918964803906947)
                ·
                  refine ⟨2248636307878447205860421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499090871918964803906947 2248636307878447205860421)
                  ·
                    refine ⟨421619307727208851098829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2248636307878447205860421 421619307727208851098829)
                    ·
                      rfl

theorem cell23_2463302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_2463302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463302 prefixEnd_2463302 := by exact prefixLift 2463302
  have htrace : WordTrace (prefixWord ++ tailWord_2463302) baseStart_2463302 baseEnd_2463302 := by
    simpa [prefixWord, tailWord_2463302, baseEnd_2463302] using wordTrace_append hprefix tailTrace_2463302
  have hstable : (prefixWord ++ tailWord_2463302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463302).length < 2 ^ (prefixWord ++ tailWord_2463302).sum := by decide
  have hdescent : baseEnd_2463302 < baseStart_2463302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463308 : List Nat := [2, 2, 1, 3, 1, 3, 1, 5, 1, 1, 3]
def baseStart_2463308 : Nat := 118140960795 + 2463308 * 2 ^ 59
def prefixEnd_2463308 : Nat := 4983230072969 + 3 ^ 40 * 2463308 * 2
def baseEnd_2463308 : Nat := 1264861004065553529821459

theorem tailTrace_2463308 : CollatzResearch.WordTrace tailWord_2463308 prefixEnd_2463308 1264861004065553529821459 := by
  unfold tailWord_2463308
  simp only [CollatzResearch.WordTrace]
  refine ⟨44922111879931645178955289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59896149173242193571940385 44922111879931645178955289)
  ·
    refine ⟨33691583909948733884216467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44922111879931645178955289 33691583909948733884216467)
    ·
      refine ⟨50537375864923100826324701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33691583909948733884216467 50537375864923100826324701)
      ·
        refine ⟨18951515949346162809871763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50537375864923100826324701 18951515949346162809871763)
        ·
          refine ⟨28427273924019244214807645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18951515949346162809871763 28427273924019244214807645)
          ·
            refine ⟨10660227721507216580552867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28427273924019244214807645 10660227721507216580552867)
            ·
              refine ⟨15990341582260824870829301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10660227721507216580552867 15990341582260824870829301)
              ·
                refine ⟨1499094523336952331640247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15990341582260824870829301 1499094523336952331640247)
                ·
                  refine ⟨2248641785005428497460371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499094523336952331640247 2248641785005428497460371)
                  ·
                    refine ⟨3372962677508142746190557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2248641785005428497460371 3372962677508142746190557)
                    ·
                      refine ⟨1264861004065553529821459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3372962677508142746190557 1264861004065553529821459)
                      ·
                        rfl

theorem cell23_2463308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_2463308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463308 prefixEnd_2463308 := by exact prefixLift 2463308
  have htrace : WordTrace (prefixWord ++ tailWord_2463308) baseStart_2463308 baseEnd_2463308 := by
    simpa [prefixWord, tailWord_2463308, baseEnd_2463308] using wordTrace_append hprefix tailTrace_2463308
  have hstable : (prefixWord ++ tailWord_2463308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463308).length < 2 ^ (prefixWord ++ tailWord_2463308).sum := by decide
  have hdescent : baseEnd_2463308 < baseStart_2463308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463327 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 4]
def baseStart_2463327 : Nat := 118140960795 + 2463327 * 2 ^ 59
def prefixEnd_2463327 : Nat := 4983230072969 + 3 ^ 40 * 2463327 * 2
def baseEnd_2463327 : Nat := 1264870760197988955483871

theorem tailTrace_2463327 : CollatzResearch.WordTrace tailWord_2463327 prefixEnd_2463327 1264870760197988955483871 := by
  unfold tailWord_2463327
  simp only [CollatzResearch.WordTrace]
  refine ⟨89844916746794456602852235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59896611164529637735234823 89844916746794456602852235)
  ·
    refine ⟨134767375120191684904278353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89844916746794456602852235 134767375120191684904278353)
    ·
      refine ⟨101075531340143763678208765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134767375120191684904278353 101075531340143763678208765)
      ·
        refine ⟨37903324252553911379328287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101075531340143763678208765 37903324252553911379328287)
        ·
          refine ⟨56854986378830867068992431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37903324252553911379328287 56854986378830867068992431)
          ·
            refine ⟨85282479568246300603488647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56854986378830867068992431 85282479568246300603488647)
            ·
              refine ⟨127923719352369450905232971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85282479568246300603488647 127923719352369450905232971)
              ·
                refine ⟨191885579028554176357849457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127923719352369450905232971 191885579028554176357849457)
                ·
                  refine ⟨143914184271415632268387093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191885579028554176357849457 143914184271415632268387093)
                  ·
                    refine ⟨6745977387722607762580645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 143914184271415632268387093 6745977387722607762580645)
                    ·
                      refine ⟨1264870760197988955483871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6745977387722607762580645 1264870760197988955483871)
                      ·
                        rfl

theorem cell23_2463327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_2463327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463327 prefixEnd_2463327 := by exact prefixLift 2463327
  have htrace : WordTrace (prefixWord ++ tailWord_2463327) baseStart_2463327 baseEnd_2463327 := by
    simpa [prefixWord, tailWord_2463327, baseEnd_2463327] using wordTrace_append hprefix tailTrace_2463327
  have hstable : (prefixWord ++ tailWord_2463327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463327).length < 2 ^ (prefixWord ++ tailWord_2463327).sum := by decide
  have hdescent : baseEnd_2463327 < baseStart_2463327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463344 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 6]
def baseStart_2463344 : Nat := 118140960795 + 2463344 * 2 ^ 59
def prefixEnd_2463344 : Nat := 4983230072969 + 3 ^ 40 * 2463344 * 2
def baseEnd_2463344 : Nat := 1264879489369115388971293

theorem tailTrace_2463344 : CollatzResearch.WordTrace tailWord_2463344 prefixEnd_2463344 1264879489369115388971293 := by
  unfold tailWord_2463344
  simp only [CollatzResearch.WordTrace]
  refine ⟨44922768393866434253110543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59897024525155245670814057 44922768393866434253110543)
  ·
    refine ⟨67384152590799651379665815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44922768393866434253110543 67384152590799651379665815)
    ·
      refine ⟨101076228886199477069498723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67384152590799651379665815 101076228886199477069498723)
      ·
        refine ⟨151614343329299215604248085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101076228886199477069498723 151614343329299215604248085)
        ·
          refine ⟨7106922343560900731449129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 151614343329299215604248085 7106922343560900731449129)
          ·
            refine ⟨5330191757670675548586847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7106922343560900731449129 5330191757670675548586847)
            ·
              refine ⟨7995287636506013322880271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5330191757670675548586847 7995287636506013322880271)
              ·
                refine ⟨11992931454759019984320407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7995287636506013322880271 11992931454759019984320407)
                ·
                  refine ⟨17989397182138529976480611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11992931454759019984320407 17989397182138529976480611)
                  ·
                    refine ⟨26984095773207794964720917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17989397182138529976480611 26984095773207794964720917)
                    ·
                      refine ⟨1264879489369115388971293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26984095773207794964720917 1264879489369115388971293)
                      ·
                        rfl

theorem cell23_2463344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_2463344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463344 prefixEnd_2463344 := by exact prefixLift 2463344
  have htrace : WordTrace (prefixWord ++ tailWord_2463344) baseStart_2463344 baseEnd_2463344 := by
    simpa [prefixWord, tailWord_2463344, baseEnd_2463344] using wordTrace_append hprefix tailTrace_2463344
  have hstable : (prefixWord ++ tailWord_2463344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463344).length < 2 ^ (prefixWord ++ tailWord_2463344).sum := by decide
  have hdescent : baseEnd_2463344 < baseStart_2463344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463368 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2463368 : Nat := 118140960795 + 2463368 * 2 ^ 59
def prefixEnd_2463368 : Nat := 4983230072969 + 3 ^ 40 * 2463368 * 2
def baseEnd_2463368 : Nat := 1264891812904823295071183

theorem tailTrace_2463368 : CollatzResearch.WordTrace tailWord_2463368 prefixEnd_2463368 1264891812904823295071183 := by
  unfold tailWord_2463368
  simp only [CollatzResearch.WordTrace]
  refine ⟨44923206069822960302547379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59897608093097280403396505 44923206069822960302547379)
  ·
    refine ⟨67384809104734440453821069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44923206069822960302547379 67384809104734440453821069)
    ·
      refine ⟨25269303414275415170182901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67384809104734440453821069 25269303414275415170182901)
      ·
        refine ⟨2368997195088320172204647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25269303414275415170182901 2368997195088320172204647)
        ·
          refine ⟨3553495792632480258306971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2368997195088320172204647 3553495792632480258306971)
          ·
            refine ⟨5330243688948720387460457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3553495792632480258306971 5330243688948720387460457)
            ·
              refine ⟨3997682766711540290595343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5330243688948720387460457 3997682766711540290595343)
              ·
                refine ⟨5996524150067310435893015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3997682766711540290595343 5996524150067310435893015)
                ·
                  refine ⟨8994786225100965653839523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5996524150067310435893015 8994786225100965653839523)
                  ·
                    refine ⟨13492179337651448480759285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8994786225100965653839523 13492179337651448480759285)
                    ·
                      refine ⟨1264891812904823295071183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13492179337651448480759285 1264891812904823295071183)
                      ·
                        rfl

theorem cell23_2463368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2463368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463368 prefixEnd_2463368 := by exact prefixLift 2463368
  have htrace : WordTrace (prefixWord ++ tailWord_2463368) baseStart_2463368 baseEnd_2463368 := by
    simpa [prefixWord, tailWord_2463368, baseEnd_2463368] using wordTrace_append hprefix tailTrace_2463368
  have hstable : (prefixWord ++ tailWord_2463368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463368).length < 2 ^ (prefixWord ++ tailWord_2463368).sum := by decide
  have hdescent : baseEnd_2463368 < baseStart_2463368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463408 : List Nat := [2, 1, 1, 1, 2, 1, 7, 2, 1, 3, 2]
def baseStart_2463408 : Nat := 118140960795 + 2463408 * 2 ^ 59
def prefixEnd_2463408 : Nat := 4983230072969 + 3 ^ 40 * 2463408 * 2
def baseEnd_2463408 : Nat := 1264912352131003138570999

theorem tailTrace_2463408 : CollatzResearch.WordTrace tailWord_2463408 prefixEnd_2463408 1264912352131003138570999 := by
  unfold tailWord_2463408
  simp only [CollatzResearch.WordTrace]
  refine ⟨44923935529750503718275439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59898580706334004957700585 44923935529750503718275439)
  ·
    refine ⟨67385903294625755577413159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44923935529750503718275439 67385903294625755577413159)
    ·
      refine ⟨101078854941938633366119739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67385903294625755577413159 101078854941938633366119739)
      ·
        refine ⟨151618282412907950049179609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101078854941938633366119739 151618282412907950049179609)
        ·
          refine ⟨113713711809680962536884707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151618282412907950049179609 113713711809680962536884707)
          ·
            refine ⟨170570567714521443805327061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113713711809680962536884707 170570567714521443805327061)
            ·
              refine ⟨3997747680809096339187353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 170570567714521443805327061 3997747680809096339187353)
              ·
                refine ⟨2998310760606822254390515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3997747680809096339187353 2998310760606822254390515)
                ·
                  refine ⟨4497466140910233381585773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2998310760606822254390515 4497466140910233381585773)
                  ·
                    refine ⟨1686549802841337518094665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4497466140910233381585773 1686549802841337518094665)
                    ·
                      refine ⟨1264912352131003138570999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1686549802841337518094665 1264912352131003138570999)
                      ·
                        rfl

theorem cell23_2463408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 1, 3, 2].length) (baseStart_2463408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463408 prefixEnd_2463408 := by exact prefixLift 2463408
  have htrace : WordTrace (prefixWord ++ tailWord_2463408) baseStart_2463408 baseEnd_2463408 := by
    simpa [prefixWord, tailWord_2463408, baseEnd_2463408] using wordTrace_append hprefix tailTrace_2463408
  have hstable : (prefixWord ++ tailWord_2463408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463408).length < 2 ^ (prefixWord ++ tailWord_2463408).sum := by decide
  have hdescent : baseEnd_2463408 < baseStart_2463408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463424 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 5]
def baseStart_2463424 : Nat := 118140960795 + 2463424 * 2 ^ 59
def prefixEnd_2463424 : Nat := 4983230072969 + 3 ^ 40 * 2463424 * 2
def baseEnd_2463424 : Nat := 1264920567821475075970925

theorem tailTrace_2463424 : CollatzResearch.WordTrace tailWord_2463424 prefixEnd_2463424 1264920567821475075970925 := by
  unfold tailWord_2463424
  simp only [CollatzResearch.WordTrace]
  refine ⟨44924227313721521084566663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59898969751628694779422217 44924227313721521084566663)
  ·
    refine ⟨67386340970582281626849995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44924227313721521084566663 67386340970582281626849995)
    ·
      refine ⟨101079511455873422440274993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67386340970582281626849995 101079511455873422440274993)
      ·
        refine ⟨75809633591905066830206245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101079511455873422440274993 75809633591905066830206245)
        ·
          refine ⟨14214306298482200030663671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75809633591905066830206245 14214306298482200030663671)
          ·
            refine ⟨21321459447723300045995507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14214306298482200030663671 21321459447723300045995507)
            ·
              refine ⟨31982189171584950068993261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21321459447723300045995507 31982189171584950068993261)
              ·
                refine ⟨11993320939344356275872473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31982189171584950068993261 11993320939344356275872473)
                ·
                  refine ⟨8994990704508267206904355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11993320939344356275872473 8994990704508267206904355)
                  ·
                    refine ⟨13492486056762400810356533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8994990704508267206904355 13492486056762400810356533)
                    ·
                      refine ⟨1264920567821475075970925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13492486056762400810356533 1264920567821475075970925)
                      ·
                        rfl

theorem cell23_2463424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_2463424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463424 prefixEnd_2463424 := by exact prefixLift 2463424
  have htrace : WordTrace (prefixWord ++ tailWord_2463424) baseStart_2463424 baseEnd_2463424 := by
    simpa [prefixWord, tailWord_2463424, baseEnd_2463424] using wordTrace_append hprefix tailTrace_2463424
  have hstable : (prefixWord ++ tailWord_2463424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463424).length < 2 ^ (prefixWord ++ tailWord_2463424).sum := by decide
  have hdescent : baseEnd_2463424 < baseStart_2463424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463476 : List Nat := [2, 6, 1, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_2463476 : Nat := 118140960795 + 2463476 * 2 ^ 59
def prefixEnd_2463476 : Nat := 4983230072969 + 3 ^ 40 * 2463476 * 2
def baseEnd_2463476 : Nat := 1264947268815508872520687

theorem tailTrace_2463476 : CollatzResearch.WordTrace tailWord_2463476 prefixEnd_2463476 1264947268815508872520687 := by
  unfold tailWord_2463476
  simp only [CollatzResearch.WordTrace]
  refine ⟨44925175611627327525013141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59900234148836436700017521 44925175611627327525013141)
  ·
    refine ⟨2105867606795030977734991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44925175611627327525013141 2105867606795030977734991)
    ·
      refine ⟨3158801410192546466602487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2105867606795030977734991 3158801410192546466602487)
      ·
        refine ⟨4738202115288819699903731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3158801410192546466602487 4738202115288819699903731)
        ·
          refine ⟨7107303172933229549855597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4738202115288819699903731 7107303172933229549855597)
          ·
            refine ⟨2665238689849961081195849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7107303172933229549855597 2665238689849961081195849)
            ·
              refine ⟨1998929017387470810896887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2665238689849961081195849 1998929017387470810896887)
              ·
                refine ⟨2998393526081206216345331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998929017387470810896887 2998393526081206216345331)
                ·
                  refine ⟨4497590289121809324517997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2998393526081206216345331 4497590289121809324517997)
                  ·
                    refine ⟨1686596358420678496694249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4497590289121809324517997 1686596358420678496694249)
                    ·
                      refine ⟨1264947268815508872520687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1686596358420678496694249 1264947268815508872520687)
                      ·
                        rfl

theorem cell23_2463476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_2463476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463476 prefixEnd_2463476 := by exact prefixLift 2463476
  have htrace : WordTrace (prefixWord ++ tailWord_2463476) baseStart_2463476 baseEnd_2463476 := by
    simpa [prefixWord, tailWord_2463476, baseEnd_2463476] using wordTrace_append hprefix tailTrace_2463476
  have hstable : (prefixWord ++ tailWord_2463476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463476).length < 2 ^ (prefixWord ++ tailWord_2463476).sum := by decide
  have hdescent : baseEnd_2463476 < baseStart_2463476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463478 : List Nat := [5, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_2463478 : Nat := 118140960795 + 2463478 * 2 ^ 59
def prefixEnd_2463478 : Nat := 4983230072969 + 3 ^ 40 * 2463478 * 2
def baseEnd_2463478 : Nat := 140549810641868651632853

theorem tailTrace_2463478 : CollatzResearch.WordTrace tailWord_2463478 prefixEnd_2463478 140549810641868651632853 := by
  unfold tailWord_2463478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5615651510577963086974943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59900282779498272927732725 5615651510577963086974943)
  ·
    refine ⟨8423477265866944630462415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5615651510577963086974943 8423477265866944630462415)
    ·
      refine ⟨12635215898800416945693623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8423477265866944630462415 12635215898800416945693623)
      ·
        refine ⟨18952823848200625418540435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12635215898800416945693623 18952823848200625418540435)
        ·
          refine ⟨28429235772300938127810653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18952823848200625418540435 28429235772300938127810653)
          ·
            refine ⟨10660963414612851797928995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28429235772300938127810653 10660963414612851797928995)
            ·
              refine ⟨15991445121919277696893493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10660963414612851797928995 15991445121919277696893493)
              ·
                refine ⟨1499197980179932284083765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15991445121919277696893493 1499197980179932284083765)
                ·
                  refine ⟨140549810641868651632853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1499197980179932284083765 140549810641868651632853)
                  ·
                    rfl

theorem cell23_2463478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_2463478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463478 prefixEnd_2463478 := by exact prefixLift 2463478
  have htrace : WordTrace (prefixWord ++ tailWord_2463478) baseStart_2463478 baseEnd_2463478 := by
    simpa [prefixWord, tailWord_2463478, baseEnd_2463478] using wordTrace_append hprefix tailTrace_2463478
  have hstable : (prefixWord ++ tailWord_2463478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463478).length < 2 ^ (prefixWord ++ tailWord_2463478).sum := by decide
  have hdescent : baseEnd_2463478 < baseStart_2463478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463511 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2463511 : Nat := 118140960795 + 2463511 * 2 ^ 59
def prefixEnd_2463511 : Nat := 4983230072969 + 3 ^ 40 * 2463511 * 2
def baseEnd_2463511 : Nat := 1264965240638416235583025

theorem tailTrace_2463511 : CollatzResearch.WordTrace tailWord_2463511 prefixEnd_2463511 1264965240638416235583025 := by
  unfold tailWord_2463511
  simp only [CollatzResearch.WordTrace]
  refine ⟨89851627778127856027550387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59901085185418570685033591 89851627778127856027550387)
  ·
    refine ⟨134777441667191784041325581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89851627778127856027550387 134777441667191784041325581)
    ·
      refine ⟨50541540625196919015497093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134777441667191784041325581 50541540625196919015497093)
      ·
        refine ⟨9476538867224422315405705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50541540625196919015497093 9476538867224422315405705)
        ·
          refine ⟨7107404150418316736554279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9476538867224422315405705 7107404150418316736554279)
          ·
            refine ⟨10661106225627475104831419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7107404150418316736554279 10661106225627475104831419)
            ·
              refine ⟨15991659338441212657247129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10661106225627475104831419 15991659338441212657247129)
              ·
                refine ⟨11993744503830909492935347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15991659338441212657247129 11993744503830909492935347)
                ·
                  refine ⟨17990616755746364239403021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11993744503830909492935347 17990616755746364239403021)
                  ·
                    refine ⟨6746481283404886589776133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17990616755746364239403021 6746481283404886589776133)
                    ·
                      refine ⟨1264965240638416235583025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6746481283404886589776133 1264965240638416235583025)
                      ·
                        rfl

theorem cell23_2463511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2463511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463511 prefixEnd_2463511 := by exact prefixLift 2463511
  have htrace : WordTrace (prefixWord ++ tailWord_2463511) baseStart_2463511 baseEnd_2463511 := by
    simpa [prefixWord, tailWord_2463511, baseEnd_2463511] using wordTrace_append hprefix tailTrace_2463511
  have hstable : (prefixWord ++ tailWord_2463511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463511).length < 2 ^ (prefixWord ++ tailWord_2463511).sum := by decide
  have hdescent : baseEnd_2463511 < baseStart_2463511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463545 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2463545 : Nat := 118140960795 + 2463545 * 2 ^ 59
def prefixEnd_2463545 : Nat := 4983230072969 + 3 ^ 40 * 2463545 * 2
def baseEnd_2463545 : Nat := 1264982698980669102557869

theorem tailTrace_2463545 : CollatzResearch.WordTrace tailWord_2463545 prefixEnd_2463545 1264982698980669102557869 := by
  unfold tailWord_2463545
  simp only [CollatzResearch.WordTrace]
  refine ⟨89852867860004679834288089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59901911906669786556192059 89852867860004679834288089)
  ·
    refine ⟨67389650895003509875716067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89852867860004679834288089 67389650895003509875716067)
    ·
      refine ⟨101084476342505264813574101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67389650895003509875716067 101084476342505264813574101)
      ·
        refine ⟨2369167414277467144068143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 101084476342505264813574101 2369167414277467144068143)
        ·
          refine ⟨3553751121416200716102215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2369167414277467144068143 3553751121416200716102215)
          ·
            refine ⟨5330626682124301074153323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3553751121416200716102215 5330626682124301074153323)
            ·
              refine ⟨7995940023186451611229985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5330626682124301074153323 7995940023186451611229985)
              ·
                refine ⟨5996955017389838708422489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7995940023186451611229985 5996955017389838708422489)
                ·
                  refine ⟨4497716263042379031316867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5996955017389838708422489 4497716263042379031316867)
                  ·
                    refine ⟨6746574394563568546975301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4497716263042379031316867 6746574394563568546975301)
                    ·
                      refine ⟨1264982698980669102557869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6746574394563568546975301 1264982698980669102557869)
                      ·
                        rfl

theorem cell23_2463545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2463545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463545 prefixEnd_2463545 := by exact prefixLift 2463545
  have htrace : WordTrace (prefixWord ++ tailWord_2463545) baseStart_2463545 baseEnd_2463545 := by
    simpa [prefixWord, tailWord_2463545, baseEnd_2463545] using wordTrace_append hprefix tailTrace_2463545
  have hstable : (prefixWord ++ tailWord_2463545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463545).length < 2 ^ (prefixWord ++ tailWord_2463545).sum := by decide
  have hdescent : baseEnd_2463545 < baseStart_2463545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463578 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3]
def baseStart_2463578 : Nat := 118140960795 + 2463578 * 2 ^ 59
def prefixEnd_2463578 : Nat := 4983230072969 + 3 ^ 40 * 2463578 * 2
def baseEnd_2463578 : Nat := 1264999643842267473445217

theorem tailTrace_2463578 : CollatzResearch.WordTrace tailWord_2463578 prefixEnd_2463578 1264999643842267473445217 := by
  unfold tailWord_2463578
  simp only [CollatzResearch.WordTrace]
  refine ⟨22463517867221281617559847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59902714312590084313492925 22463517867221281617559847)
  ·
    refine ⟨33695276800831922426339771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22463517867221281617559847 33695276800831922426339771)
    ·
      refine ⟨50542915201247883639509657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33695276800831922426339771 50542915201247883639509657)
      ·
        refine ⟨37907186400935912729632243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50542915201247883639509657 37907186400935912729632243)
        ·
          refine ⟨56860779601403869094448365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37907186400935912729632243 56860779601403869094448365)
          ·
            refine ⟨21322792350526450910418137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56860779601403869094448365 21322792350526450910418137)
            ·
              refine ⟨15992094262894838182813603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21322792350526450910418137 15992094262894838182813603)
              ·
                refine ⟨23988141394342257274220405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15992094262894838182813603 23988141394342257274220405)
                ·
                  refine ⟨2248888255719586619458163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23988141394342257274220405 2248888255719586619458163)
                  ·
                    refine ⟨3373332383579379929187245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2248888255719586619458163 3373332383579379929187245)
                    ·
                      refine ⟨1264999643842267473445217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3373332383579379929187245 1264999643842267473445217)
                      ·
                        rfl

theorem cell23_2463578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_2463578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463578 prefixEnd_2463578 := by exact prefixLift 2463578
  have htrace : WordTrace (prefixWord ++ tailWord_2463578) baseStart_2463578 baseEnd_2463578 := by
    simpa [prefixWord, tailWord_2463578, baseEnd_2463578] using wordTrace_append hprefix tailTrace_2463578
  have hstable : (prefixWord ++ tailWord_2463578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463578).length < 2 ^ (prefixWord ++ tailWord_2463578).sum := by decide
  have hdescent : baseEnd_2463578 < baseStart_2463578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463595 : List Nat := [1, 1, 1, 1, 2, 2, 3, 7, 1, 1, 3]
def baseStart_2463595 : Nat := 118140960795 + 2463595 * 2 ^ 59
def prefixEnd_2463595 : Nat := 4983230072969 + 3 ^ 40 * 2463595 * 2
def baseEnd_2463595 : Nat := 1265008373013393906932639

theorem tailTrace_2463595 : CollatzResearch.WordTrace tailWord_2463595 prefixEnd_2463595 1265008373013393906932639 := by
  unfold tailWord_2463595
  simp only [CollatzResearch.WordTrace]
  refine ⟨89854691509823538373608239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59903127673215692249072159 89854691509823538373608239)
  ·
    refine ⟨134782037264735307560412359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89854691509823538373608239 134782037264735307560412359)
    ·
      refine ⟨202173055897102961340618539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134782037264735307560412359 202173055897102961340618539)
      ·
        refine ⟨303259583845654442010927809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202173055897102961340618539 303259583845654442010927809)
        ·
          refine ⟨227444687884240831508195857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303259583845654442010927809 227444687884240831508195857)
          ·
            refine ⟨170583515913180623631146893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227444687884240831508195857 170583515913180623631146893)
            ·
              refine ⟨63968818467442733861680085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170583515913180623631146893 63968818467442733861680085)
              ·
                refine ⟨1499269182830689074883127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 63968818467442733861680085 1499269182830689074883127)
                ·
                  refine ⟨2248903774246033612324691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499269182830689074883127 2248903774246033612324691)
                  ·
                    refine ⟨3373355661369050418487037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2248903774246033612324691 3373355661369050418487037)
                    ·
                      refine ⟨1265008373013393906932639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3373355661369050418487037 1265008373013393906932639)
                      ·
                        rfl

theorem cell23_2463595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 1, 1, 3].length) (baseStart_2463595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463595 prefixEnd_2463595 := by exact prefixLift 2463595
  have htrace : WordTrace (prefixWord ++ tailWord_2463595) baseStart_2463595 baseEnd_2463595 := by
    simpa [prefixWord, tailWord_2463595, baseEnd_2463595] using wordTrace_append hprefix tailTrace_2463595
  have hstable : (prefixWord ++ tailWord_2463595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463595).length < 2 ^ (prefixWord ++ tailWord_2463595).sum := by decide
  have hdescent : baseEnd_2463595 < baseStart_2463595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463605 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_2463605 : Nat := 118140960795 + 2463605 * 2 ^ 59
def prefixEnd_2463605 : Nat := 4983230072969 + 3 ^ 40 * 2463605 * 2
def baseEnd_2463605 : Nat := 1265013507819938867807593

theorem tailTrace_2463605 : CollatzResearch.WordTrace tailWord_2463605 prefixEnd_2463605 1265013507819938867807593 := by
  unfold tailWord_2463605
  simp only [CollatzResearch.WordTrace]
  refine ⟨89855056239787310081472269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59903370826524873387648179 89855056239787310081472269)
  ·
    refine ⟨33695646089920241280552101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89855056239787310081472269 33695646089920241280552101)
    ·
      refine ⟨6317933641860045240103519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33695646089920241280552101 6317933641860045240103519)
      ·
        refine ⟨9476900462790067860155279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6317933641860045240103519 9476900462790067860155279)
        ·
          refine ⟨14215350694185101790232919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9476900462790067860155279 14215350694185101790232919)
          ·
            refine ⟨21323026041277652685349379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14215350694185101790232919 21323026041277652685349379)
            ·
              refine ⟨31984539061916479028024069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21323026041277652685349379 31984539061916479028024069)
              ·
                refine ⟨5997101074109339817754513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31984539061916479028024069 5997101074109339817754513)
                ·
                  refine ⟨4497825805582004863315885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5997101074109339817754513 4497825805582004863315885)
                  ·
                    refine ⟨1686684677093251823743457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4497825805582004863315885 1686684677093251823743457)
                    ·
                      refine ⟨1265013507819938867807593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1686684677093251823743457 1265013507819938867807593)
                      ·
                        rfl

theorem cell23_2463605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_2463605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463605 prefixEnd_2463605 := by exact prefixLift 2463605
  have htrace : WordTrace (prefixWord ++ tailWord_2463605) baseStart_2463605 baseEnd_2463605 := by
    simpa [prefixWord, tailWord_2463605, baseEnd_2463605] using wordTrace_append hprefix tailTrace_2463605
  have hstable : (prefixWord ++ tailWord_2463605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463605).length < 2 ^ (prefixWord ++ tailWord_2463605).sum := by decide
  have hdescent : baseEnd_2463605 < baseStart_2463605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463606 : List Nat := [5, 1, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_2463606 : Nat := 118140960795 + 2463606 * 2 ^ 59
def prefixEnd_2463606 : Nat := 4983230072969 + 3 ^ 40 * 2463606 * 2
def baseEnd_2463606 : Nat := 421671340433531121298363

theorem tailTrace_2463606 : CollatzResearch.WordTrace tailWord_2463606 prefixEnd_2463606 421671340433531121298363 := by
  unfold tailWord_2463606
  simp only [CollatzResearch.WordTrace]
  refine ⟨5615943294548980453266167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59903395141855791501505781 5615943294548980453266167)
  ·
    refine ⟨8423914941823470679899251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5615943294548980453266167 8423914941823470679899251)
    ·
      refine ⟨12635872412735206019848877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8423914941823470679899251 12635872412735206019848877)
      ·
        refine ⟨4738452154775702257443329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12635872412735206019848877 4738452154775702257443329)
        ·
          refine ⟨3553839116081776693082497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4738452154775702257443329 3553839116081776693082497)
          ·
            refine ⟨2665379337061332519811873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3553839116081776693082497 2665379337061332519811873)
            ·
              refine ⟨1999034502795999389858905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2665379337061332519811873 1999034502795999389858905)
              ·
                refine ⟨1499275877096999542394179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999034502795999389858905 1499275877096999542394179)
                ·
                  refine ⟨2248913815645499313591269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499275877096999542394179 2248913815645499313591269)
                  ·
                    refine ⟨421671340433531121298363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2248913815645499313591269 421671340433531121298363)
                    ·
                      rfl

theorem cell23_2463606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_2463606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463606 prefixEnd_2463606 := by exact prefixLift 2463606
  have htrace : WordTrace (prefixWord ++ tailWord_2463606) baseStart_2463606 baseEnd_2463606 := by
    simpa [prefixWord, tailWord_2463606, baseEnd_2463606] using wordTrace_append hprefix tailTrace_2463606
  have hstable : (prefixWord ++ tailWord_2463606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463606).length < 2 ^ (prefixWord ++ tailWord_2463606).sum := by decide
  have hdescent : baseEnd_2463606 < baseStart_2463606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463621 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_2463621 : Nat := 118140960795 + 2463621 * 2 ^ 59
def prefixEnd_2463621 : Nat := 4983230072969 + 3 ^ 40 * 2463621 * 2
def baseEnd_2463621 : Nat := 1265021723510410805207519

theorem tailTrace_2463621 : CollatzResearch.WordTrace tailWord_2463621 prefixEnd_2463621 1265021723510410805207519 := by
  unfold tailWord_2463621
  simp only [CollatzResearch.WordTrace]
  refine ⟨89855639807729344814054717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59903759871819563209369811 89855639807729344814054717)
  ·
    refine ⟨33695864927898504305270519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89855639807729344814054717 33695864927898504305270519)
    ·
      refine ⟨50543797391847756457905779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33695864927898504305270519 50543797391847756457905779)
      ·
        refine ⟨75815696087771634686858669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50543797391847756457905779 75815696087771634686858669)
        ·
          refine ⟨28430886032914363007572001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75815696087771634686858669 28430886032914363007572001)
          ·
            refine ⟨21323164524685772255679001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28430886032914363007572001 21323164524685772255679001)
            ·
              refine ⟨15992373393514329191759251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21323164524685772255679001 15992373393514329191759251)
              ·
                refine ⟨23988560090271493787638877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15992373393514329191759251 23988560090271493787638877)
                ·
                  refine ⟨8995710033851810170364579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23988560090271493787638877 8995710033851810170364579)
                  ·
                    refine ⟨13493565050777715255546869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8995710033851810170364579 13493565050777715255546869)
                    ·
                      refine ⟨1265021723510410805207519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13493565050777715255546869 1265021723510410805207519)
                      ·
                        rfl

theorem cell23_2463621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_2463621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463621 prefixEnd_2463621 := by exact prefixLift 2463621
  have htrace : WordTrace (prefixWord ++ tailWord_2463621) baseStart_2463621 baseEnd_2463621 := by
    simpa [prefixWord, tailWord_2463621, baseEnd_2463621] using wordTrace_append hprefix tailTrace_2463621
  have hstable : (prefixWord ++ tailWord_2463621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463621).length < 2 ^ (prefixWord ++ tailWord_2463621).sum := by decide
  have hdescent : baseEnd_2463621 < baseStart_2463621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463649 : List Nat := [1, 2, 3, 4, 3, 1, 2, 1, 1, 5]
def baseStart_2463649 : Nat := 118140960795 + 2463649 * 2 ^ 59
def prefixEnd_2463649 : Nat := 4983230072969 + 3 ^ 40 * 2463649 * 2
def baseEnd_2463649 : Nat := 421678700322912231885797

theorem tailTrace_2463649 : CollatzResearch.WordTrace tailWord_2463649 prefixEnd_2463649 421678700322912231885797 := by
  unfold tailWord_2463649
  simp only [CollatzResearch.WordTrace]
  refine ⟨89856661051627905596074001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59904440701085270397382667 89856661051627905596074001)
  ·
    refine ⟨67392495788720929197055501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89856661051627905596074001 67392495788720929197055501)
    ·
      refine ⟨25272185920770348448895813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67392495788720929197055501 25272185920770348448895813)
      ·
        refine ⟨4738534860144440334167965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25272185920770348448895813 4738534860144440334167965)
        ·
          refine ⟨1776950572554165125312987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4738534860144440334167965 1776950572554165125312987)
          ·
            refine ⟨2665425858831247687969481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776950572554165125312987 2665425858831247687969481)
            ·
              refine ⟨1999069394123435765977111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2665425858831247687969481 1999069394123435765977111)
              ·
                refine ⟨2998604091185153648965667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1999069394123435765977111 2998604091185153648965667)
                ·
                  refine ⟨4497906136777730473448501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2998604091185153648965667 4497906136777730473448501)
                  ·
                    refine ⟨421678700322912231885797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4497906136777730473448501 421678700322912231885797)
                    ·
                      rfl

theorem cell23_2463649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_2463649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463649 prefixEnd_2463649 := by exact prefixLift 2463649
  have htrace : WordTrace (prefixWord ++ tailWord_2463649) baseStart_2463649 baseEnd_2463649 := by
    simpa [prefixWord, tailWord_2463649, baseEnd_2463649] using wordTrace_append hprefix tailTrace_2463649
  have hstable : (prefixWord ++ tailWord_2463649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463649).length < 2 ^ (prefixWord ++ tailWord_2463649).sum := by decide
  have hdescent : baseEnd_2463649 < baseStart_2463649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463652 : List Nat := [2, 3, 1, 2, 1, 5, 2, 1, 1, 1, 4]
def baseStart_2463652 : Nat := 118140960795 + 2463652 * 2 ^ 59
def prefixEnd_2463652 : Nat := 4983230072969 + 3 ^ 40 * 2463652 * 2
def baseEnd_2463652 : Nat := 1265037641410700183919877

theorem tailTrace_2463652 : CollatzResearch.WordTrace tailWord_2463652 prefixEnd_2463652 1265037641410700183919877 := by
  unfold tailWord_2463652
  simp only [CollatzResearch.WordTrace]
  refine ⟨44928385235308518554216605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59904513647078024738955473 44928385235308518554216605)
  ·
    refine ⟨16848144463240694457831227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44928385235308518554216605 16848144463240694457831227)
    ·
      refine ⟨25272216694861041686746841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16848144463240694457831227 25272216694861041686746841)
      ·
        refine ⟨18954162521145781265060131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25272216694861041686746841 18954162521145781265060131)
        ·
          refine ⟨28431243781718671897590197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18954162521145781265060131 28431243781718671897590197)
          ·
            refine ⟨2665429104536125490399081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28431243781718671897590197 2665429104536125490399081)
            ·
              refine ⟨1999071828402094117799311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2665429104536125490399081 1999071828402094117799311)
              ·
                refine ⟨2998607742603141176698967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1999071828402094117799311 2998607742603141176698967)
                ·
                  refine ⟨4497911613904711765048451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2998607742603141176698967 4497911613904711765048451)
                  ·
                    refine ⟨6746867420857067647572677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4497911613904711765048451 6746867420857067647572677)
                    ·
                      refine ⟨1265037641410700183919877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6746867420857067647572677 1265037641410700183919877)
                      ·
                        rfl

theorem cell23_2463652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_2463652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463652 prefixEnd_2463652 := by exact prefixLift 2463652
  have htrace : WordTrace (prefixWord ++ tailWord_2463652) baseStart_2463652 baseEnd_2463652 := by
    simpa [prefixWord, tailWord_2463652, baseEnd_2463652] using wordTrace_append hprefix tailTrace_2463652
  have hstable : (prefixWord ++ tailWord_2463652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463652).length < 2 ^ (prefixWord ++ tailWord_2463652).sum := by decide
  have hdescent : baseEnd_2463652 < baseStart_2463652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463669 : List Nat := [1, 3, 3, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_2463669 : Nat := 118140960795 + 2463669 * 2 ^ 59
def prefixEnd_2463669 : Nat := 4983230072969 + 3 ^ 40 * 2463669 * 2
def baseEnd_2463669 : Nat := 1265046370581826617407299

theorem tailTrace_2463669 : CollatzResearch.WordTrace tailWord_2463669 prefixEnd_2463669 1265046370581826617407299 := by
  unfold tailWord_2463669
  simp only [CollatzResearch.WordTrace]
  refine ⟨89857390511555449011802061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59904927007703632674534707 89857390511555449011802061)
  ·
    refine ⟨33696521441833293379425773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89857390511555449011802061 33696521441833293379425773)
    ·
      refine ⟨12636195540687485017284665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33696521441833293379425773 12636195540687485017284665)
      ·
        refine ⟨9477146655515613762963499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12636195540687485017284665 9477146655515613762963499)
        ·
          refine ⟨14215719983273420644445249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9477146655515613762963499 14215719983273420644445249)
          ·
            refine ⟨10661789987455065483333937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14215719983273420644445249 10661789987455065483333937)
            ·
              refine ⟨7996342490591299112500453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10661789987455065483333937 7996342490591299112500453)
              ·
                refine ⟨1499314216985868583593835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7996342490591299112500453 1499314216985868583593835)
                ·
                  refine ⟨2248971325478802875390753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499314216985868583593835 2248971325478802875390753)
                  ·
                    refine ⟨1686728494109102156543065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2248971325478802875390753 1686728494109102156543065)
                    ·
                      refine ⟨1265046370581826617407299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1686728494109102156543065 1265046370581826617407299)
                      ·
                        rfl

theorem cell23_2463669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_2463669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463669 prefixEnd_2463669 := by exact prefixLift 2463669
  have htrace : WordTrace (prefixWord ++ tailWord_2463669) baseStart_2463669 baseEnd_2463669 := by
    simpa [prefixWord, tailWord_2463669, baseEnd_2463669] using wordTrace_append hprefix tailTrace_2463669
  have hstable : (prefixWord ++ tailWord_2463669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463669).length < 2 ^ (prefixWord ++ tailWord_2463669).sum := by decide
  have hdescent : baseEnd_2463669 < baseStart_2463669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463815 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 1, 6, 2]
def baseStart_2463815 : Nat := 118140960795 + 2463815 * 2 ^ 59
def prefixEnd_2463815 : Nat := 4983230072969 + 3 ^ 40 * 2463815 * 2
def baseEnd_2463815 : Nat := 1265121338757383046181627

theorem tailTrace_2463815 : CollatzResearch.WordTrace tailWord_2463815 prefixEnd_2463815 1265121338757383046181627 := by
  unfold tailWord_2463815
  simp only [CollatzResearch.WordTrace]
  refine ⟨89862715569026515946616899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59908477046017677297744599 89862715569026515946616899)
  ·
    refine ⟨134794073353539773919925349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89862715569026515946616899 134794073353539773919925349)
    ·
      refine ⟨25273888753788707609986003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134794073353539773919925349 25273888753788707609986003)
      ·
        refine ⟨37910833130683061414979005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25273888753788707609986003 37910833130683061414979005)
        ·
          refine ⟨14216562424006148030617127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37910833130683061414979005 14216562424006148030617127)
          ·
            refine ⟨21324843636009222045925691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14216562424006148030617127 21324843636009222045925691)
            ·
              refine ⟨31987265454013833068888537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21324843636009222045925691 31987265454013833068888537)
              ·
                refine ⟨23990449090510374801666403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31987265454013833068888537 23990449090510374801666403)
                ·
                  refine ⟨35985673635765562202499605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23990449090510374801666403 35985673635765562202499605)
                  ·
                    refine ⟨1686828451676510728242169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35985673635765562202499605 1686828451676510728242169)
                    ·
                      refine ⟨1265121338757383046181627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1686828451676510728242169 1265121338757383046181627)
                      ·
                        rfl

theorem cell23_2463815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_2463815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463815 prefixEnd_2463815 := by exact prefixLift 2463815
  have htrace : WordTrace (prefixWord ++ tailWord_2463815) baseStart_2463815 baseEnd_2463815 := by
    simpa [prefixWord, tailWord_2463815, baseEnd_2463815] using wordTrace_append hprefix tailTrace_2463815
  have hstable : (prefixWord ++ tailWord_2463815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463815).length < 2 ^ (prefixWord ++ tailWord_2463815).sum := by decide
  have hdescent : baseEnd_2463815 < baseStart_2463815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463928 : List Nat := [2, 1, 2, 1, 2, 1, 3, 11]
def baseStart_2463928 : Nat := 118140960795 + 2463928 * 2 ^ 59
def prefixEnd_2463928 : Nat := 4983230072969 + 3 ^ 40 * 2463928 * 2
def baseEnd_2463928 : Nat := 46858494891531152002541

theorem tailTrace_2463928 : CollatzResearch.WordTrace tailWord_2463928 prefixEnd_2463928 46858494891531152002541 := by
  unfold tailWord_2463928
  simp only [CollatzResearch.WordTrace]
  refine ⟨44933418508808568122740219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59911224678411424163653625 44933418508808568122740219)
  ·
    refine ⟨67400127763212852184110329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44933418508808568122740219 67400127763212852184110329)
    ·
      refine ⟨50550095822409639138082747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67400127763212852184110329 50550095822409639138082747)
      ·
        refine ⟨75825143733614458707124121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50550095822409639138082747 75825143733614458707124121)
        ·
          refine ⟨56868857800210844030343091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75825143733614458707124121 56868857800210844030343091)
          ·
            refine ⟨85303286700316266045514637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56868857800210844030343091 85303286700316266045514637)
            ·
              refine ⟨31988732512618599767067989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85303286700316266045514637 31988732512618599767067989)
              ·
                refine ⟨46858494891531152002541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 31988732512618599767067989 46858494891531152002541)
                ·
                  rfl

theorem cell23_2463928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 11].length) (baseStart_2463928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463928 prefixEnd_2463928 := by exact prefixLift 2463928
  have htrace : WordTrace (prefixWord ++ tailWord_2463928) baseStart_2463928 baseEnd_2463928 := by
    simpa [prefixWord, tailWord_2463928, baseEnd_2463928] using wordTrace_append hprefix tailTrace_2463928
  have hstable : (prefixWord ++ tailWord_2463928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463928).length < 2 ^ (prefixWord ++ tailWord_2463928).sum := by decide
  have hdescent : baseEnd_2463928 < baseStart_2463928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463932 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 1, 6]
def baseStart_2463932 : Nat := 118140960795 + 2463932 * 2 ^ 59
def prefixEnd_2463932 : Nat := 4983230072969 + 3 ^ 40 * 2463932 * 2
def baseEnd_2463932 : Nat := 421727138664653029472863

theorem tailTrace_2463932 : CollatzResearch.WordTrace tailWord_2463932 prefixEnd_2463932 421727138664653029472863 := by
  unfold tailWord_2463932
  simp only [CollatzResearch.WordTrace]
  refine ⟨44933491454801322464313025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59911321939735096619084033 44933491454801322464313025)
  ·
    refine ⟨33700118591100991848234769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44933491454801322464313025 33700118591100991848234769)
    ·
      refine ⟨25275088943325743886176077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33700118591100991848234769 25275088943325743886176077)
      ·
        refine ⟨9478158353747153957316029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25275088943325743886176077 9478158353747153957316029)
        ·
          refine ⟨3554309382655182733993511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9478158353747153957316029 3554309382655182733993511)
          ·
            refine ⟨5331464073982774100990267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3554309382655182733993511 5331464073982774100990267)
            ·
              refine ⟨7997196110974161151485401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5331464073982774100990267 7997196110974161151485401)
              ·
                refine ⟨5997897083230620863614051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7997196110974161151485401 5997897083230620863614051)
                ·
                  refine ⟨8996845624845931295421077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5997897083230620863614051 8996845624845931295421077)
                  ·
                    refine ⟨421727138664653029472863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8996845624845931295421077 421727138664653029472863)
                    ·
                      rfl

theorem cell23_2463932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_2463932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463932 prefixEnd_2463932 := by exact prefixLift 2463932
  have htrace : WordTrace (prefixWord ++ tailWord_2463932) baseStart_2463932 baseEnd_2463932 := by
    simpa [prefixWord, tailWord_2463932, baseEnd_2463932] using wordTrace_append hprefix tailTrace_2463932
  have hstable : (prefixWord ++ tailWord_2463932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463932).length < 2 ^ (prefixWord ++ tailWord_2463932).sum := by decide
  have hdescent : baseEnd_2463932 < baseStart_2463932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463972 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_2463972 : Nat := 118140960795 + 2463972 * 2 ^ 59
def prefixEnd_2463972 : Nat := 4983230072969 + 3 ^ 40 * 2463972 * 2
def baseEnd_2463972 : Nat := 1265201955220138931918405

theorem tailTrace_2463972 : CollatzResearch.WordTrace tailWord_2463972 prefixEnd_2463972 1265201955220138931918405 := by
  unfold tailWord_2463972
  simp only [CollatzResearch.WordTrace]
  refine ⟨44934220914728865880041085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59912294552971821173388113 44934220914728865880041085)
  ·
    refine ⟨16850332843023324705015407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44934220914728865880041085 16850332843023324705015407)
    ·
      refine ⟨25275499264534987057523111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16850332843023324705015407 25275499264534987057523111)
      ·
        refine ⟨37913248896802480586284667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25275499264534987057523111 37913248896802480586284667)
        ·
          refine ⟨56869873345203720879427001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37913248896802480586284667 56869873345203720879427001)
          ·
            refine ⟨42652405008902790659570251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56869873345203720879427001 42652405008902790659570251)
            ·
              refine ⟨63978607513354185989355377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42652405008902790659570251 63978607513354185989355377)
              ·
                refine ⟨47983955635015639492016533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63978607513354185989355377 47983955635015639492016533)
                ·
                  refine ⟨2249247920391358101188275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47983955635015639492016533 2249247920391358101188275)
                  ·
                    refine ⟨3373871880587037151782413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2249247920391358101188275 3373871880587037151782413)
                    ·
                      refine ⟨1265201955220138931918405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3373871880587037151782413 1265201955220138931918405)
                      ·
                        rfl

theorem cell23_2463972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_2463972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463972 prefixEnd_2463972 := by exact prefixLift 2463972
  have htrace : WordTrace (prefixWord ++ tailWord_2463972) baseStart_2463972 baseEnd_2463972 := by
    simpa [prefixWord, tailWord_2463972, baseEnd_2463972] using wordTrace_append hprefix tailTrace_2463972
  have hstable : (prefixWord ++ tailWord_2463972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463972).length < 2 ^ (prefixWord ++ tailWord_2463972).sum := by decide
  have hdescent : baseEnd_2463972 < baseStart_2463972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463999 : List Nat := [1, 1, 2, 2, 1, 4, 3, 3, 1, 3, 2]
def baseStart_2463999 : Nat := 118140960795 + 2463999 * 2 ^ 59
def prefixEnd_2463999 : Nat := 4983230072969 + 3 ^ 40 * 2463999 * 2
def baseEnd_2463999 : Nat := 1265215819197810326280781

theorem tailTrace_2463999 : CollatzResearch.WordTrace tailWord_2463999 prefixEnd_2463999 1265215819197810326280781 := by
  unfold tailWord_2463999
  simp only [CollatzResearch.WordTrace]
  refine ⟨89869426600359915371315051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59912951066906610247543367 89869426600359915371315051)
  ·
    refine ⟨134804139900539873056972577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89869426600359915371315051 134804139900539873056972577)
    ·
      refine ⟨101103104925404904792729433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134804139900539873056972577 101103104925404904792729433)
      ·
        refine ⟨75827328694053678594547075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101103104925404904792729433 75827328694053678594547075)
        ·
          refine ⟨113740993041080517891820613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75827328694053678594547075 113740993041080517891820613)
          ·
            refine ⟨21326436195202597104716365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113740993041080517891820613 21326436195202597104716365)
            ·
              refine ⟨7997413573200973914268637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21326436195202597104716365 7997413573200973914268637)
              ·
                refine ⟨2999030089950365217850739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7997413573200973914268637 2999030089950365217850739)
                ·
                  refine ⟨4498545134925547826776109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2999030089950365217850739 4498545134925547826776109)
                  ·
                    refine ⟨1686954425597080435041041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4498545134925547826776109 1686954425597080435041041)
                    ·
                      refine ⟨1265215819197810326280781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1686954425597080435041041 1265215819197810326280781)
                      ·
                        rfl

theorem cell23_2463999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 3, 2].length) (baseStart_2463999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2463999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2463999 prefixEnd_2463999 := by exact prefixLift 2463999
  have htrace : WordTrace (prefixWord ++ tailWord_2463999) baseStart_2463999 baseEnd_2463999 := by
    simpa [prefixWord, tailWord_2463999, baseEnd_2463999] using wordTrace_append hprefix tailTrace_2463999
  have hstable : (prefixWord ++ tailWord_2463999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463999).length < 2 ^ (prefixWord ++ tailWord_2463999).sum := by decide
  have hdescent : baseEnd_2463999 < baseStart_2463999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464015 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 3]
def baseStart_2464015 : Nat := 118140960795 + 2464015 * 2 ^ 59
def prefixEnd_2464015 : Nat := 4983230072969 + 3 ^ 40 * 2464015 * 2
def baseEnd_2464015 : Nat := 1265224034888282263680707

theorem tailTrace_2464015 : CollatzResearch.WordTrace tailWord_2464015 prefixEnd_2464015 1265224034888282263680707 := by
  unfold tailWord_2464015
  simp only [CollatzResearch.WordTrace]
  refine ⟨89870010168301950103897499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59913340112201300069264999 89870010168301950103897499)
  ·
    refine ⟨134805015252452925155846249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89870010168301950103897499 134805015252452925155846249)
    ·
      refine ⟨101103761439339693866884687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134805015252452925155846249 101103761439339693866884687)
      ·
        refine ⟨151655642159009540800327031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101103761439339693866884687 151655642159009540800327031)
        ·
          refine ⟨227483463238514311200490547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151655642159009540800327031 227483463238514311200490547)
          ·
            refine ⟨341225194857771466800735821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227483463238514311200490547 341225194857771466800735821)
            ·
              refine ⟨127959448071664300050275933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 341225194857771466800735821 127959448071664300050275933)
              ·
                refine ⟨47984793026874112518853475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127959448071664300050275933 47984793026874112518853475)
                ·
                  refine ⟨71977189540311168778280213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47984793026874112518853475 71977189540311168778280213)
                  ·
                    refine ⟨3373930759702086036481885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71977189540311168778280213 3373930759702086036481885)
                    ·
                      refine ⟨1265224034888282263680707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3373930759702086036481885 1265224034888282263680707)
                      ·
                        rfl

theorem cell23_2464015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 3].length) (baseStart_2464015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464015 prefixEnd_2464015 := by exact prefixLift 2464015
  have htrace : WordTrace (prefixWord ++ tailWord_2464015) baseStart_2464015 baseEnd_2464015 := by
    simpa [prefixWord, tailWord_2464015, baseEnd_2464015] using wordTrace_append hprefix tailTrace_2464015
  have hstable : (prefixWord ++ tailWord_2464015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464015).length < 2 ^ (prefixWord ++ tailWord_2464015).sum := by decide
  have hdescent : baseEnd_2464015 < baseStart_2464015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464035 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 7]
def baseStart_2464035 : Nat := 118140960795 + 2464035 * 2 ^ 59
def prefixEnd_2464035 : Nat := 4983230072969 + 3 ^ 40 * 2464035 * 2
def baseEnd_2464035 : Nat := 140581589389041353936735

theorem tailTrace_2464035 : CollatzResearch.WordTrace tailWord_2464035 prefixEnd_2464035 140581589389041353936735 := by
  unfold tailWord_2464035
  simp only [CollatzResearch.WordTrace]
  refine ⟨89870739628229493519625559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59913826418819662346417039 89870739628229493519625559)
  ·
    refine ⟨134806109442344240279438339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89870739628229493519625559 134806109442344240279438339)
    ·
      refine ⟨202209164163516360419157509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134806109442344240279438339 202209164163516360419157509)
      ·
        refine ⟨37914218280659317578592033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202209164163516360419157509 37914218280659317578592033)
        ·
          refine ⟨28435663710494488183944025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37914218280659317578592033 28435663710494488183944025)
          ·
            refine ⟨21326747782870866137958019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28435663710494488183944025 21326747782870866137958019)
            ·
              refine ⟨31990121674306299206937029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21326747782870866137958019 31990121674306299206937029)
              ·
                refine ⟨5998147813932431101300693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31990121674306299206937029 5998147813932431101300693)
                ·
                  refine ⟨140581589389041353936735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5998147813932431101300693 140581589389041353936735)
                  ·
                    rfl

theorem cell23_2464035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 7].length) (baseStart_2464035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464035 prefixEnd_2464035 := by exact prefixLift 2464035
  have htrace : WordTrace (prefixWord ++ tailWord_2464035) baseStart_2464035 baseEnd_2464035 := by
    simpa [prefixWord, tailWord_2464035, baseEnd_2464035] using wordTrace_append hprefix tailTrace_2464035
  have hstable : (prefixWord ++ tailWord_2464035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464035).length < 2 ^ (prefixWord ++ tailWord_2464035).sum := by decide
  have hdescent : baseEnd_2464035 < baseStart_2464035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464095 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 2, 8]
def baseStart_2464095 : Nat := 118140960795 + 2464095 * 2 ^ 59
def prefixEnd_2464095 : Nat := 4983230072969 + 3 ^ 40 * 2464095 * 2
def baseEnd_2464095 : Nat := 421755037780213983560113

theorem tailTrace_2464095 : CollatzResearch.WordTrace tailWord_2464095 prefixEnd_2464095 421755037780213983560113 := by
  unfold tailWord_2464095
  simp only [CollatzResearch.WordTrace]
  refine ⟨89872928008012123766809739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59915285338674749177873159 89872928008012123766809739)
  ·
    refine ⟨134809392012018185650214609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89872928008012123766809739 134809392012018185650214609)
    ·
      refine ⟨101107044009013639237660957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134809392012018185650214609 101107044009013639237660957)
      ·
        refine ⟨37915141503380114714122859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101107044009013639237660957 37915141503380114714122859)
        ·
          refine ⟨56872712255070172071184289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37915141503380114714122859 56872712255070172071184289)
          ·
            refine ⟨42654534191302629053388217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56872712255070172071184289 42654534191302629053388217)
            ·
              refine ⟨31990900643476971790041163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42654534191302629053388217 31990900643476971790041163)
              ·
                refine ⟨47986350965215457685061745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31990900643476971790041163 47986350965215457685061745)
                ·
                  refine ⟨35989763223911593263796309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47986350965215457685061745 35989763223911593263796309)
                  ·
                    refine ⟨421755037780213983560113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35989763223911593263796309 421755037780213983560113)
                    ·
                      rfl

theorem cell23_2464095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_2464095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464095 prefixEnd_2464095 := by exact prefixLift 2464095
  have htrace : WordTrace (prefixWord ++ tailWord_2464095) baseStart_2464095 baseEnd_2464095 := by
    simpa [prefixWord, tailWord_2464095, baseEnd_2464095] using wordTrace_append hprefix tailTrace_2464095
  have hstable : (prefixWord ++ tailWord_2464095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464095).length < 2 ^ (prefixWord ++ tailWord_2464095).sum := by decide
  have hdescent : baseEnd_2464095 < baseStart_2464095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464115 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 6]
def baseStart_2464115 : Nat := 118140960795 + 2464115 * 2 ^ 59
def prefixEnd_2464115 : Nat := 4983230072969 + 3 ^ 40 * 2464115 * 2
def baseEnd_2464115 : Nat := 1265275382953731872430247

theorem tailTrace_2464115 : CollatzResearch.WordTrace tailWord_2464115 prefixEnd_2464115 1265275382953731872430247 := by
  unfold tailWord_2464115
  simp only [CollatzResearch.WordTrace]
  refine ⟨89873657467939667182537799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59915771645293111455025199 89873657467939667182537799)
  ·
    refine ⟨134810486201909500773806699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89873657467939667182537799 134810486201909500773806699)
    ·
      refine ⟨202215729302864251160710049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134810486201909500773806699 202215729302864251160710049)
      ·
        refine ⟨151661796977148188370532537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202215729302864251160710049 151661796977148188370532537)
        ·
          refine ⟨113746347732861141277899403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151661796977148188370532537 113746347732861141277899403)
          ·
            refine ⟨170619521599291711916849105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113746347732861141277899403 170619521599291711916849105)
            ·
              refine ⟨127964641199468783937636829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170619521599291711916849105 127964641199468783937636829)
              ·
                refine ⟨47986740449800793976613811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127964641199468783937636829 47986740449800793976613811)
                ·
                  refine ⟨71980110674701190964920717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47986740449800793976613811 71980110674701190964920717)
                  ·
                    refine ⟨26992541503012946611845269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71980110674701190964920717 26992541503012946611845269)
                    ·
                      refine ⟨1265275382953731872430247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26992541503012946611845269 1265275382953731872430247)
                      ·
                        rfl

theorem cell23_2464115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_2464115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464115 prefixEnd_2464115 := by exact prefixLift 2464115
  have htrace : WordTrace (prefixWord ++ tailWord_2464115) baseStart_2464115 baseEnd_2464115 := by
    simpa [prefixWord, tailWord_2464115, baseEnd_2464115] using wordTrace_append hprefix tailTrace_2464115
  have hstable : (prefixWord ++ tailWord_2464115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464115).length < 2 ^ (prefixWord ++ tailWord_2464115).sum := by decide
  have hdescent : baseEnd_2464115 < baseStart_2464115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464180 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2464180 : Nat := 118140960795 + 2464180 * 2 ^ 59
def prefixEnd_2464180 : Nat := 4983230072969 + 3 ^ 40 * 2464180 * 2
def baseEnd_2464180 : Nat := 421769586398758039372483

theorem tailTrace_2464180 : CollatzResearch.WordTrace tailWord_2464180 prefixEnd_2464180 421769586398758039372483 := by
  unfold tailWord_2464180
  simp only [CollatzResearch.WordTrace]
  refine ⟨44938014106352091641826997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59917352141802788855769329 44938014106352091641826997)
  ·
    refine ⟨4212938822470508591421281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44938014106352091641826997 4212938822470508591421281)
    ·
      refine ⟨3159704116852881443565961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4212938822470508591421281 3159704116852881443565961)
      ·
        refine ⟨2369778087639661082674471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3159704116852881443565961 2369778087639661082674471)
        ·
          refine ⟨3554667131459491624011707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2369778087639661082674471 3554667131459491624011707)
          ·
            refine ⟨5332000697189237436017561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3554667131459491624011707 5332000697189237436017561)
            ·
              refine ⟨3999000522891928077013171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5332000697189237436017561 3999000522891928077013171)
              ·
                refine ⟨5998500784337892115519757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3999000522891928077013171 5998500784337892115519757)
                ·
                  refine ⟨2249437794126709543319909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5998500784337892115519757 2249437794126709543319909)
                  ·
                    refine ⟨421769586398758039372483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2249437794126709543319909 421769586398758039372483)
                    ·
                      rfl

theorem cell23_2464180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2464180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464180 prefixEnd_2464180 := by exact prefixLift 2464180
  have htrace : WordTrace (prefixWord ++ tailWord_2464180) baseStart_2464180 baseEnd_2464180 := by
    simpa [prefixWord, tailWord_2464180, baseEnd_2464180] using wordTrace_append hprefix tailTrace_2464180
  have hstable : (prefixWord ++ tailWord_2464180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464180).length < 2 ^ (prefixWord ++ tailWord_2464180).sum := by decide
  have hdescent : baseEnd_2464180 < baseStart_2464180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464232 : List Nat := [2, 1, 4, 1, 1, 3, 11]
def baseStart_2464232 : Nat := 118140960795 + 2464232 * 2 ^ 59
def prefixEnd_2464232 : Nat := 4983230072969 + 3 ^ 40 * 2464232 * 2
def baseEnd_2464232 : Nat := 15621425434448245860089

theorem tailTrace_2464232 : CollatzResearch.WordTrace tailWord_2464232 prefixEnd_2464232 15621425434448245860089 := by
  unfold tailWord_2464232
  simp only [CollatzResearch.WordTrace]
  refine ⟨44938962404257898082273475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59918616539010530776364633 44938962404257898082273475)
  ·
    refine ⟨67408443606386847123410213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44938962404257898082273475 67408443606386847123410213)
    ·
      refine ⟨12639083176197533835639415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67408443606386847123410213 12639083176197533835639415)
      ·
        refine ⟨18958624764296300753459123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12639083176197533835639415 18958624764296300753459123)
        ·
          refine ⟨28437937146444451130188685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18958624764296300753459123 28437937146444451130188685)
          ·
            refine ⟨10664226429916669173820757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28437937146444451130188685 10664226429916669173820757)
            ·
              refine ⟨15621425434448245860089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10664226429916669173820757 15621425434448245860089)
              ·
                rfl

theorem cell23_2464232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 11].length) (baseStart_2464232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464232 prefixEnd_2464232 := by exact prefixLift 2464232
  have htrace : WordTrace (prefixWord ++ tailWord_2464232) baseStart_2464232 baseEnd_2464232 := by
    simpa [prefixWord, tailWord_2464232, baseEnd_2464232] using wordTrace_append hprefix tailTrace_2464232
  have hstable : (prefixWord ++ tailWord_2464232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464232).length < 2 ^ (prefixWord ++ tailWord_2464232).sum := by decide
  have hdescent : baseEnd_2464232 < baseStart_2464232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464237 : List Nat := [1, 5, 1, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_2464237 : Nat := 118140960795 + 2464237 * 2 ^ 59
def prefixEnd_2464237 : Nat := 4983230072969 + 3 ^ 40 * 2464237 * 2
def baseEnd_2464237 : Nat := 1265338027593580395104687

theorem tailTrace_2464237 : CollatzResearch.WordTrace tailWord_2464237 prefixEnd_2464237 1265338027593580395104687 := by
  unfold tailWord_2464237
  simp only [CollatzResearch.WordTrace]
  refine ⟨89878107173497682018478965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59918738115665121345652643 89878107173497682018478965)
  ·
    refine ⟨8426072547515407689232403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89878107173497682018478965 8426072547515407689232403)
    ·
      refine ⟨12639108821273111533848605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8426072547515407689232403 12639108821273111533848605)
      ·
        refine ⟨4739665807977416825193227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12639108821273111533848605 4739665807977416825193227)
        ·
          refine ⟨7109498711966125237789841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4739665807977416825193227 7109498711966125237789841)
          ·
            refine ⟨5332124033974593928342381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7109498711966125237789841 5332124033974593928342381)
            ·
              refine ⟨1999546512740472723128393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5332124033974593928342381 1999546512740472723128393)
              ·
                refine ⟨1499659884555354542346295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999546512740472723128393 1499659884555354542346295)
                ·
                  refine ⟨2249489826833031813519443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499659884555354542346295 2249489826833031813519443)
                  ·
                    refine ⟨3374234740249547720279165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2249489826833031813519443 3374234740249547720279165)
                    ·
                      refine ⟨1265338027593580395104687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3374234740249547720279165 1265338027593580395104687)
                      ·
                        rfl

theorem cell23_2464237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_2464237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464237 prefixEnd_2464237 := by exact prefixLift 2464237
  have htrace : WordTrace (prefixWord ++ tailWord_2464237) baseStart_2464237 baseEnd_2464237 := by
    simpa [prefixWord, tailWord_2464237, baseEnd_2464237] using wordTrace_append hprefix tailTrace_2464237
  have hstable : (prefixWord ++ tailWord_2464237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464237).length < 2 ^ (prefixWord ++ tailWord_2464237).sum := by decide
  have hdescent : baseEnd_2464237 < baseStart_2464237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464246 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_2464246 : Nat := 118140960795 + 2464246 * 2 ^ 59
def prefixEnd_2464246 : Nat := 4983230072969 + 3 ^ 40 * 2464246 * 2
def baseEnd_2464246 : Nat := 1265342648919470859892145

theorem tailTrace_2464246 : CollatzResearch.WordTrace tailWord_2464246 prefixEnd_2464246 1265342648919470859892145 := by
  unfold tailWord_2464246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5617402214404067284722287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59918956953643384370371061 5617402214404067284722287)
  ·
    refine ⟨8426103321606100927083431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5617402214404067284722287 8426103321606100927083431)
    ·
      refine ⟨12639154982409151390625147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8426103321606100927083431 12639154982409151390625147)
      ·
        refine ⟨18958732473613727085937721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12639154982409151390625147 18958732473613727085937721)
        ·
          refine ⟨14219049355210295314453291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18958732473613727085937721 14219049355210295314453291)
          ·
            refine ⟨21328574032815442971679937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14219049355210295314453291 21328574032815442971679937)
            ·
              refine ⟨15996430524611582228759953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21328574032815442971679937 15996430524611582228759953)
              ·
                refine ⟨11997322893458686671569965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15996430524611582228759953 11997322893458686671569965)
                ·
                  refine ⟨4498996085047007501838737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11997322893458686671569965 4498996085047007501838737)
                  ·
                    refine ⟨3374247063785255626379053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4498996085047007501838737 3374247063785255626379053)
                    ·
                      refine ⟨1265342648919470859892145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3374247063785255626379053 1265342648919470859892145)
                      ·
                        rfl

theorem cell23_2464246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_2464246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464246 prefixEnd_2464246 := by exact prefixLift 2464246
  have htrace : WordTrace (prefixWord ++ tailWord_2464246) baseStart_2464246 baseEnd_2464246 := by
    simpa [prefixWord, tailWord_2464246, baseEnd_2464246] using wordTrace_append hprefix tailTrace_2464246
  have hstable : (prefixWord ++ tailWord_2464246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464246).length < 2 ^ (prefixWord ++ tailWord_2464246).sum := by decide
  have hdescent : baseEnd_2464246 < baseStart_2464246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464252 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_2464252 : Nat := 118140960795 + 2464252 * 2 ^ 59
def prefixEnd_2464252 : Nat := 4983230072969 + 3 ^ 40 * 2464252 * 2
def baseEnd_2464252 : Nat := 1265345729803397836417117

theorem tailTrace_2464252 : CollatzResearch.WordTrace tailWord_2464252 prefixEnd_2464252 1265345729803397836417117 := by
  unfold tailWord_2464252
  simp only [CollatzResearch.WordTrace]
  refine ⟨44939327134221669790137505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59919102845628893053516673 44939327134221669790137505)
  ·
    refine ⟨33704495350666252342603129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44939327134221669790137505 33704495350666252342603129)
    ·
      refine ⟨25278371512999689256952347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33704495350666252342603129 25278371512999689256952347)
      ·
        refine ⟨37917557269499533885428521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25278371512999689256952347 37917557269499533885428521)
        ·
          refine ⟨28438167952124650414071391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37917557269499533885428521 28438167952124650414071391)
          ·
            refine ⟨42657251928186975621107087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28438167952124650414071391 42657251928186975621107087)
            ·
              refine ⟨63985877892280463431660631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42657251928186975621107087 63985877892280463431660631)
              ·
                refine ⟨95978816838420695147490947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63985877892280463431660631 95978816838420695147490947)
                ·
                  refine ⟨143968225257631042721236421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95978816838420695147490947 143968225257631042721236421)
                  ·
                    refine ⟨26994042235805820510231829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 143968225257631042721236421 26994042235805820510231829)
                    ·
                      refine ⟨1265345729803397836417117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26994042235805820510231829 1265345729803397836417117)
                      ·
                        rfl

theorem cell23_2464252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_2464252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464252 prefixEnd_2464252 := by exact prefixLift 2464252
  have htrace : WordTrace (prefixWord ++ tailWord_2464252) baseStart_2464252 baseEnd_2464252 := by
    simpa [prefixWord, tailWord_2464252, baseEnd_2464252] using wordTrace_append hprefix tailTrace_2464252
  have hstable : (prefixWord ++ tailWord_2464252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464252).length < 2 ^ (prefixWord ++ tailWord_2464252).sum := by decide
  have hdescent : baseEnd_2464252 < baseStart_2464252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464259 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 3]
def baseStart_2464259 : Nat := 118140960795 + 2464259 * 2 ^ 59
def prefixEnd_2464259 : Nat := 4983230072969 + 3 ^ 40 * 2464259 * 2
def baseEnd_2464259 : Nat := 1265349324167979309029585

theorem tailTrace_2464259 : CollatzResearch.WordTrace tailWord_2464259 prefixEnd_2464259 1265349324167979309029585 := by
  unfold tailWord_2464259
  simp only [CollatzResearch.WordTrace]
  refine ⟨89878909579417979775779831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59919273052945319850519887 89878909579417979775779831)
  ·
    refine ⟨134818364369126969663669747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89878909579417979775779831 134818364369126969663669747)
    ·
      refine ⟨202227546553690454495504621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134818364369126969663669747 202227546553690454495504621)
      ·
        refine ⟨75835329957633920435814233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202227546553690454495504621 75835329957633920435814233)
        ·
          refine ⟨56876497468225440326860675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75835329957633920435814233 56876497468225440326860675)
          ·
            refine ⟨85314746202338160490291013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56876497468225440326860675 85314746202338160490291013)
            ·
              refine ⟨15996514912938405091929565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85314746202338160490291013 15996514912938405091929565)
              ·
                refine ⟨5998693092351901909473587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15996514912938405091929565 5998693092351901909473587)
                ·
                  refine ⟨8998039638527852864210381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5998693092351901909473587 8998039638527852864210381)
                  ·
                    refine ⟨3374264864447944824078893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8998039638527852864210381 3374264864447944824078893)
                    ·
                      refine ⟨1265349324167979309029585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3374264864447944824078893 1265349324167979309029585)
                      ·
                        rfl

theorem cell23_2464259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_2464259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464259 prefixEnd_2464259 := by exact prefixLift 2464259
  have htrace : WordTrace (prefixWord ++ tailWord_2464259) baseStart_2464259 baseEnd_2464259 := by
    simpa [prefixWord, tailWord_2464259, baseEnd_2464259] using wordTrace_append hprefix tailTrace_2464259
  have hstable : (prefixWord ++ tailWord_2464259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464259).length < 2 ^ (prefixWord ++ tailWord_2464259).sum := by decide
  have hdescent : baseEnd_2464259 < baseStart_2464259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464272 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 5]
def baseStart_2464272 : Nat := 118140960795 + 2464272 * 2 ^ 59
def prefixEnd_2464272 : Nat := 4983230072969 + 3 ^ 40 * 2464272 * 2
def baseEnd_2464272 : Nat := 1265355999416487758167025

theorem tailTrace_2464272 : CollatzResearch.WordTrace tailWord_2464272 prefixEnd_2464272 1265355999416487758167025 := by
  unfold tailWord_2464272
  simp only [CollatzResearch.WordTrace]
  refine ⟨44939691864185441498001535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59919589152247255330668713 44939691864185441498001535)
  ·
    refine ⟨67409537796278162247002303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44939691864185441498001535 67409537796278162247002303)
    ·
      refine ⟨101114306694417243370503455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67409537796278162247002303 101114306694417243370503455)
      ·
        refine ⟨151671460041625865055755183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101114306694417243370503455 151671460041625865055755183)
        ·
          refine ⟨227507190062438797583632775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151671460041625865055755183 227507190062438797583632775)
          ·
            refine ⟨341260785093658196375449163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227507190062438797583632775 341260785093658196375449163)
            ·
              refine ⟨511891177640487294563173745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341260785093658196375449163 511891177640487294563173745)
              ·
                refine ⟨383918383230365470922380309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511891177640487294563173745 383918383230365470922380309)
                ·
                  refine ⟨17996174213923381449486577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 383918383230365470922380309 17996174213923381449486577)
                  ·
                    refine ⟨13497130660442536087114933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17996174213923381449486577 13497130660442536087114933)
                    ·
                      refine ⟨1265355999416487758167025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13497130660442536087114933 1265355999416487758167025)
                      ·
                        rfl

theorem cell23_2464272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_2464272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464272 prefixEnd_2464272 := by exact prefixLift 2464272
  have htrace : WordTrace (prefixWord ++ tailWord_2464272) baseStart_2464272 baseEnd_2464272 := by
    simpa [prefixWord, tailWord_2464272, baseEnd_2464272] using wordTrace_append hprefix tailTrace_2464272
  have hstable : (prefixWord ++ tailWord_2464272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464272).length < 2 ^ (prefixWord ++ tailWord_2464272).sum := by decide
  have hdescent : baseEnd_2464272 < baseStart_2464272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464309 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 2, 6]
def baseStart_2464309 : Nat := 118140960795 + 2464309 * 2 ^ 59
def prefixEnd_2464309 : Nat := 4983230072969 + 3 ^ 40 * 2464309 * 2
def baseEnd_2464309 : Nat := 421791666066901371134785

theorem tailTrace_2464309 : CollatzResearch.WordTrace tailWord_2464309 prefixEnd_2464309 421791666066901371134785 := by
  unfold tailWord_2464309
  simp only [CollatzResearch.WordTrace]
  refine ⟨89880733229236838315099981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59920488819491225543399987 89880733229236838315099981)
  ·
    refine ⟨33705274960963814368162493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89880733229236838315099981 33705274960963814368162493)
    ·
      refine ⟨12639478110361430388060935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33705274960963814368162493 12639478110361430388060935)
      ·
        refine ⟨18959217165542145582091403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12639478110361430388060935 18959217165542145582091403)
        ·
          refine ⟨28438825748313218373137105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18959217165542145582091403 28438825748313218373137105)
          ·
            refine ⟨21329119311234913779852829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28438825748313218373137105 21329119311234913779852829)
            ·
              refine ⟨7998419741713092667444811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21329119311234913779852829 7998419741713092667444811)
              ·
                refine ⟨11997629612569639001167217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7998419741713092667444811 11997629612569639001167217)
                ·
                  refine ⟨8998222209427229250875413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11997629612569639001167217 8998222209427229250875413)
                  ·
                    refine ⟨421791666066901371134785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8998222209427229250875413 421791666066901371134785)
                    ·
                      rfl

theorem cell23_2464309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_2464309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464309 prefixEnd_2464309 := by exact prefixLift 2464309
  have htrace : WordTrace (prefixWord ++ tailWord_2464309) baseStart_2464309 baseEnd_2464309 := by
    simpa [prefixWord, tailWord_2464309, baseEnd_2464309] using wordTrace_append hprefix tailTrace_2464309
  have hstable : (prefixWord ++ tailWord_2464309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464309).length < 2 ^ (prefixWord ++ tailWord_2464309).sum := by decide
  have hdescent : baseEnd_2464309 < baseStart_2464309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464310 : List Nat := [5, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_2464310 : Nat := 118140960795 + 2464310 * 2 ^ 59
def prefixEnd_2464310 : Nat := 4983230072969 + 3 ^ 40 * 2464310 * 2
def baseEnd_2464310 : Nat := 1265375511681358609491851

theorem tailTrace_2464310 : CollatzResearch.WordTrace tailWord_2464310 prefixEnd_2464310 1265375511681358609491851 := by
  unfold tailWord_2464310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5617548106389575967867899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59920513134822143657257589 5617548106389575967867899)
  ·
    refine ⟨8426322159584363951801849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5617548106389575967867899 8426322159584363951801849)
    ·
      refine ⟨6319741619688272963851387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8426322159584363951801849 6319741619688272963851387)
      ·
        refine ⟨9479612429532409445777081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6319741619688272963851387 9479612429532409445777081)
        ·
          refine ⟨7109709322149307084332811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9479612429532409445777081 7109709322149307084332811)
          ·
            refine ⟨10664563983223960626499217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7109709322149307084332811 10664563983223960626499217)
            ·
              refine ⟨7998422987417970469874413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10664563983223960626499217 7998422987417970469874413)
              ·
                refine ⟨2999408620281738926202905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7998422987417970469874413 2999408620281738926202905)
                ·
                  refine ⟨2249556465211304194652179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2999408620281738926202905 2249556465211304194652179)
                  ·
                    refine ⟨3374334697816956291978269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2249556465211304194652179 3374334697816956291978269)
                    ·
                      refine ⟨1265375511681358609491851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3374334697816956291978269 1265375511681358609491851)
                      ·
                        rfl

theorem cell23_2464310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_2464310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464310 prefixEnd_2464310 := by exact prefixLift 2464310
  have htrace : WordTrace (prefixWord ++ tailWord_2464310) baseStart_2464310 baseEnd_2464310 := by
    simpa [prefixWord, tailWord_2464310, baseEnd_2464310] using wordTrace_append hprefix tailTrace_2464310
  have hstable : (prefixWord ++ tailWord_2464310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464310).length < 2 ^ (prefixWord ++ tailWord_2464310).sum := by decide
  have hdescent : baseEnd_2464310 < baseStart_2464310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464319 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 3]
def baseStart_2464319 : Nat := 118140960795 + 2464319 * 2 ^ 59
def prefixEnd_2464319 : Nat := 4983230072969 + 3 ^ 40 * 2464319 * 2
def baseEnd_2464319 : Nat := 1265380133007249074279309

theorem tailTrace_2464319 : CollatzResearch.WordTrace tailWord_2464319 prefixEnd_2464319 1265380133007249074279309 := by
  unfold tailWord_2464319
  simp only [CollatzResearch.WordTrace]
  refine ⟨89881097959200610022964011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59920731972800406681976007 89881097959200610022964011)
  ·
    refine ⟨134821646938800915034446017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89881097959200610022964011 134821646938800915034446017)
    ·
      refine ⟨101116235204100686275834513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134821646938800915034446017 101116235204100686275834513)
      ·
        refine ⟨75837176403075514706875885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101116235204100686275834513 75837176403075514706875885)
        ·
          refine ⟨28438941151153318015078457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75837176403075514706875885 28438941151153318015078457)
          ·
            refine ⟨21329205863364988511308843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28438941151153318015078457 21329205863364988511308843)
            ·
              refine ⟨31993808795047482766963265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21329205863364988511308843 31993808795047482766963265)
              ·
                refine ⟨23995356596285612075222449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31993808795047482766963265 23995356596285612075222449)
                ·
                  refine ⟨17996517447214209056416837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23995356596285612075222449 17996517447214209056416837)
                  ·
                    refine ⟨3374347021352664198078157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17996517447214209056416837 3374347021352664198078157)
                    ·
                      refine ⟨1265380133007249074279309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3374347021352664198078157 1265380133007249074279309)
                      ·
                        rfl

theorem cell23_2464319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_2464319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464319 prefixEnd_2464319 := by exact prefixLift 2464319
  have htrace : WordTrace (prefixWord ++ tailWord_2464319) baseStart_2464319 baseEnd_2464319 := by
    simpa [prefixWord, tailWord_2464319, baseEnd_2464319] using wordTrace_append hprefix tailTrace_2464319
  have hstable : (prefixWord ++ tailWord_2464319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464319).length < 2 ^ (prefixWord ++ tailWord_2464319).sum := by decide
  have hdescent : baseEnd_2464319 < baseStart_2464319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464356 : List Nat := [2, 3, 1, 1, 2, 2, 1, 6, 5]
def baseStart_2464356 : Nat := 118140960795 + 2464356 * 2 ^ 59
def prefixEnd_2464356 : Nat := 4983230072969 + 3 ^ 40 * 2464356 * 2
def baseEnd_2464356 : Nat := 140599903532385047724071

theorem tailTrace_2464356 : CollatzResearch.WordTrace tailWord_2464356 prefixEnd_2464356 140599903532385047724071 := by
  unfold tailWord_2464356
  simp only [CollatzResearch.WordTrace]
  refine ⟨44941223730033282671030461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59921631640044376894707281 44941223730033282671030461)
  ·
    refine ⟨16852958898762481001636423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44941223730033282671030461 16852958898762481001636423)
    ·
      refine ⟨25279438348143721502454635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16852958898762481001636423 25279438348143721502454635)
      ·
        refine ⟨37919157522215582253681953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25279438348143721502454635 37919157522215582253681953)
        ·
          refine ⟨28439368141661686690261465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37919157522215582253681953 28439368141661686690261465)
          ·
            refine ⟨21329526106246265017696099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28439368141661686690261465 21329526106246265017696099)
            ·
              refine ⟨31994289159369397526544149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21329526106246265017696099 31994289159369397526544149)
              ·
                refine ⟨1499732304345440509056757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31994289159369397526544149 1499732304345440509056757)
                ·
                  refine ⟨140599903532385047724071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1499732304345440509056757 140599903532385047724071)
                  ·
                    rfl

theorem cell23_2464356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_2464356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464356 prefixEnd_2464356 := by exact prefixLift 2464356
  have htrace : WordTrace (prefixWord ++ tailWord_2464356) baseStart_2464356 baseEnd_2464356 := by
    simpa [prefixWord, tailWord_2464356, baseEnd_2464356] using wordTrace_append hprefix tailTrace_2464356
  have hstable : (prefixWord ++ tailWord_2464356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464356).length < 2 ^ (prefixWord ++ tailWord_2464356).sum := by decide
  have hdescent : baseEnd_2464356 < baseStart_2464356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464419 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 4]
def baseStart_2464419 : Nat := 118140960795 + 2464419 * 2 ^ 59
def prefixEnd_2464419 : Nat := 4983230072969 + 3 ^ 40 * 2464419 * 2
def baseEnd_2464419 : Nat := 1265431481072698683028849

theorem tailTrace_2464419 : CollatzResearch.WordTrace tailWord_2464419 prefixEnd_2464419 1265431481072698683028849 := by
  unfold tailWord_2464419
  simp only [CollatzResearch.WordTrace]
  refine ⟨89884745258838327101604311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59923163505892218067736207 89884745258838327101604311)
  ·
    refine ⟨134827117888257490652406467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89884745258838327101604311 134827117888257490652406467)
    ·
      refine ⟨202240676832386235978609701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134827117888257490652406467 202240676832386235978609701)
      ·
        refine ⟨37920126906072419245989319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202240676832386235978609701 37920126906072419245989319)
        ·
          refine ⟨56880190359108628868983979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37920126906072419245989319 56880190359108628868983979)
          ·
            refine ⟨85320285538662943303475969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56880190359108628868983979 85320285538662943303475969)
            ·
              refine ⟨63990214153997207477606977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85320285538662943303475969 63990214153997207477606977)
              ·
                refine ⟨47992660615497905608205233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63990214153997207477606977 47992660615497905608205233)
                ·
                  refine ⟨35994495461623429206153925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47992660615497905608205233 35994495461623429206153925)
                  ·
                    refine ⟨6748967899054392976153861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35994495461623429206153925 6748967899054392976153861)
                    ·
                      refine ⟨1265431481072698683028849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6748967899054392976153861 1265431481072698683028849)
                      ·
                        rfl

theorem cell23_2464419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_2464419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464419 prefixEnd_2464419 := by exact prefixLift 2464419
  have htrace : WordTrace (prefixWord ++ tailWord_2464419) baseStart_2464419 baseEnd_2464419 := by
    simpa [prefixWord, tailWord_2464419, baseEnd_2464419] using wordTrace_append hprefix tailTrace_2464419
  have hstable : (prefixWord ++ tailWord_2464419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464419).length < 2 ^ (prefixWord ++ tailWord_2464419).sum := by decide
  have hdescent : baseEnd_2464419 < baseStart_2464419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464473 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 3, 1, 3]
def baseStart_2464473 : Nat := 118140960795 + 2464473 * 2 ^ 59
def prefixEnd_2464473 : Nat := 4983230072969 + 3 ^ 40 * 2464473 * 2
def baseEnd_2464473 : Nat := 1265459209028041471753601

theorem tailTrace_2464473 : CollatzResearch.WordTrace tailWord_2464473 prefixEnd_2464473 1265459209028041471753601 := by
  unfold tailWord_2464473
  simp only [CollatzResearch.WordTrace]
  refine ⟨89886714800642694324070073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59924476533761796216046715 89886714800642694324070073)
  ·
    refine ⟨67415036100482020743052555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89886714800642694324070073 67415036100482020743052555)
    ·
      refine ⟨101122554150723031114578833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67415036100482020743052555 101122554150723031114578833)
      ·
        refine ⟨75841915613042273335934125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101122554150723031114578833 75841915613042273335934125)
        ·
          refine ⟨28440718354890852500975297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75841915613042273335934125 28440718354890852500975297)
          ·
            refine ⟨21330538766168139375731473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28440718354890852500975297 21330538766168139375731473)
            ·
              refine ⟨15997904074626104531798605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21330538766168139375731473 15997904074626104531798605)
              ·
                refine ⟨5999214027984789199424477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15997904074626104531798605 5999214027984789199424477)
                ·
                  refine ⟨2249705260494295949784179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5999214027984789199424477 2249705260494295949784179)
                  ·
                    refine ⟨3374557890741443924676269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2249705260494295949784179 3374557890741443924676269)
                    ·
                      refine ⟨1265459209028041471753601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3374557890741443924676269 1265459209028041471753601)
                      ·
                        rfl

theorem cell23_2464473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_2464473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464473 prefixEnd_2464473 := by exact prefixLift 2464473
  have htrace : WordTrace (prefixWord ++ tailWord_2464473) baseStart_2464473 baseEnd_2464473 := by
    simpa [prefixWord, tailWord_2464473, baseEnd_2464473] using wordTrace_append hprefix tailTrace_2464473
  have hstable : (prefixWord ++ tailWord_2464473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464473).length < 2 ^ (prefixWord ++ tailWord_2464473).sum := by decide
  have hdescent : baseEnd_2464473 < baseStart_2464473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464493 : List Nat := [1, 5, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_2464493 : Nat := 118140960795 + 2464493 * 2 ^ 59
def prefixEnd_2464493 : Nat := 4983230072969 + 3 ^ 40 * 2464493 * 2
def baseEnd_2464493 : Nat := 421823159547043797834503

theorem tailTrace_2464493 : CollatzResearch.WordTrace tailWord_2464493 prefixEnd_2464493 421823159547043797834503 := by
  unfold tailWord_2464493
  simp only [CollatzResearch.WordTrace]
  refine ⟨89887444260570237739798133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59924962840380158493198755 89887444260570237739798133)
  ·
    refine ⟨8426947899428459788106075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89887444260570237739798133 8426947899428459788106075)
    ·
      refine ⟨12640421849142689682159113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8426947899428459788106075 12640421849142689682159113)
      ·
        refine ⟨9480316386857017261619335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12640421849142689682159113 9480316386857017261619335)
        ·
          refine ⟨14220474580285525892429003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9480316386857017261619335 14220474580285525892429003)
          ·
            refine ⟨21330711870428288838643505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14220474580285525892429003 21330711870428288838643505)
            ·
              refine ⟨15998033902821216628982629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21330711870428288838643505 15998033902821216628982629)
              ·
                refine ⟨2999631356778978117934243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15998033902821216628982629 2999631356778978117934243)
                ·
                  refine ⟨4499447035168467176901365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2999631356778978117934243 4499447035168467176901365)
                  ·
                    refine ⟨421823159547043797834503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4499447035168467176901365 421823159547043797834503)
                    ·
                      rfl

theorem cell23_2464493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_2464493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464493 prefixEnd_2464493 := by exact prefixLift 2464493
  have htrace : WordTrace (prefixWord ++ tailWord_2464493) baseStart_2464493 baseEnd_2464493 := by
    simpa [prefixWord, tailWord_2464493, baseEnd_2464493] using wordTrace_append hprefix tailTrace_2464493
  have hstable : (prefixWord ++ tailWord_2464493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464493).length < 2 ^ (prefixWord ++ tailWord_2464493).sum := by decide
  have hdescent : baseEnd_2464493 < baseStart_2464493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464496 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 4]
def baseStart_2464496 : Nat := 118140960795 + 2464496 * 2 ^ 59
def prefixEnd_2464496 : Nat := 4983230072969 + 3 ^ 40 * 2464496 * 2
def baseEnd_2464496 : Nat := 1265471019083094881765995

theorem tailTrace_2464496 : CollatzResearch.WordTrace tailWord_2464496 prefixEnd_2464496 1265471019083094881765995 := by
  unfold tailWord_2464496
  simp only [CollatzResearch.WordTrace]
  refine ⟨44943776839779684626078671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59925035786372912834771561 44943776839779684626078671)
  ·
    refine ⟨67415665259669526939118007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44943776839779684626078671 67415665259669526939118007)
    ·
      refine ⟨101123497889504290408677011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67415665259669526939118007 101123497889504290408677011)
      ·
        refine ⟨151685246834256435613015517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101123497889504290408677011 151685246834256435613015517)
        ·
          refine ⟨56881967562846163354880819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151685246834256435613015517 56881967562846163354880819)
          ·
            refine ⟨85322951344269245032321229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56881967562846163354880819 85322951344269245032321229)
            ·
              refine ⟨31996106754100966887120461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85322951344269245032321229 31996106754100966887120461)
              ·
                refine ⟨11998540032787862582670173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31996106754100966887120461 11998540032787862582670173)
                ·
                  refine ⟨4499452512295448468501315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11998540032787862582670173 4499452512295448468501315)
                  ·
                    refine ⟨6749178768443172702751973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4499452512295448468501315 6749178768443172702751973)
                    ·
                      refine ⟨1265471019083094881765995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6749178768443172702751973 1265471019083094881765995)
                      ·
                        rfl

theorem cell23_2464496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_2464496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464496 prefixEnd_2464496 := by exact prefixLift 2464496
  have htrace : WordTrace (prefixWord ++ tailWord_2464496) baseStart_2464496 baseEnd_2464496 := by
    simpa [prefixWord, tailWord_2464496, baseEnd_2464496] using wordTrace_append hprefix tailTrace_2464496
  have hstable : (prefixWord ++ tailWord_2464496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464496).length < 2 ^ (prefixWord ++ tailWord_2464496).sum := by decide
  have hdescent : baseEnd_2464496 < baseStart_2464496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464501 : List Nat := [1, 3, 6, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2464501 : Nat := 118140960795 + 2464501 * 2 ^ 59
def prefixEnd_2464501 : Nat := 4983230072969 + 3 ^ 40 * 2464501 * 2
def baseEnd_2464501 : Nat := 421824528828789120734491

theorem tailTrace_2464501 : CollatzResearch.WordTrace tailWord_2464501 prefixEnd_2464501 421824528828789120734491 := by
  unfold tailWord_2464501
  simp only [CollatzResearch.WordTrace]
  refine ⟨89887736044541255106089357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59925157363027503404059571 89887736044541255106089357)
  ·
    refine ⟨33707901016702970664783509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89887736044541255106089357 33707901016702970664783509)
    ·
      refine ⟨1580057860157951749911727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33707901016702970664783509 1580057860157951749911727)
      ·
        refine ⟨2370086790236927624867591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1580057860157951749911727 2370086790236927624867591)
        ·
          refine ⟨3555130185355391437301387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2370086790236927624867591 3555130185355391437301387)
          ·
            refine ⟨5332695278033087155952081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3555130185355391437301387 5332695278033087155952081)
            ·
              refine ⟨3999521458524815366964061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5332695278033087155952081 3999521458524815366964061)
              ·
                refine ⟨1499820546946805762611523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3999521458524815366964061 1499820546946805762611523)
                ·
                  refine ⟨2249730820420208643917285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499820546946805762611523 2249730820420208643917285)
                  ·
                    refine ⟨421824528828789120734491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2249730820420208643917285 421824528828789120734491)
                    ·
                      rfl

theorem cell23_2464501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2464501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464501 prefixEnd_2464501 := by exact prefixLift 2464501
  have htrace : WordTrace (prefixWord ++ tailWord_2464501) baseStart_2464501 baseEnd_2464501 := by
    simpa [prefixWord, tailWord_2464501, baseEnd_2464501] using wordTrace_append hprefix tailTrace_2464501
  have hstable : (prefixWord ++ tailWord_2464501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464501).length < 2 ^ (prefixWord ++ tailWord_2464501).sum := by decide
  have hdescent : baseEnd_2464501 < baseStart_2464501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464506 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 1, 6]
def baseStart_2464506 : Nat := 118140960795 + 2464506 * 2 ^ 59
def prefixEnd_2464506 : Nat := 4983230072969 + 3 ^ 40 * 2464506 * 2
def baseEnd_2464506 : Nat := 421825384629879947546983

theorem tailTrace_2464506 : CollatzResearch.WordTrace tailWord_2464506 prefixEnd_2464506 421825384629879947546983 := by
  unfold tailWord_2464506
  simp only [CollatzResearch.WordTrace]
  refine ⟨22471979602380785240005343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59925278939682093973347581 22471979602380785240005343)
  ·
    refine ⟨33707969403571177860008015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22471979602380785240005343 33707969403571177860008015)
    ·
      refine ⟨50561954105356766790012023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33707969403571177860008015 50561954105356766790012023)
      ·
        refine ⟨75842931158035150185018035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50561954105356766790012023 75842931158035150185018035)
        ·
          refine ⟨113764396737052725277527053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75842931158035150185018035 113764396737052725277527053)
          ·
            refine ⟨42661648776394771979072645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113764396737052725277527053 42661648776394771979072645)
            ·
              refine ⟨7999059145574019746076121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42661648776394771979072645 7999059145574019746076121)
              ·
                refine ⟨5999294359180514809557091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7999059145574019746076121 5999294359180514809557091)
                ·
                  refine ⟨8998941538770772214335637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5999294359180514809557091 8998941538770772214335637)
                  ·
                    refine ⟨421825384629879947546983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8998941538770772214335637 421825384629879947546983)
                    ·
                      rfl

theorem cell23_2464506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_2464506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464506 prefixEnd_2464506 := by exact prefixLift 2464506
  have htrace : WordTrace (prefixWord ++ tailWord_2464506) baseStart_2464506 baseEnd_2464506 := by
    simpa [prefixWord, tailWord_2464506, baseEnd_2464506] using wordTrace_append hprefix tailTrace_2464506
  have hstable : (prefixWord ++ tailWord_2464506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464506).length < 2 ^ (prefixWord ++ tailWord_2464506).sum := by decide
  have hdescent : baseEnd_2464506 < baseStart_2464506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464510 : List Nat := [4, 2, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2464510 : Nat := 118140960795 + 2464510 * 2 ^ 59
def prefixEnd_2464510 : Nat := 4983230072969 + 3 ^ 40 * 2464510 * 2
def baseEnd_2464510 : Nat := 421826069270752608996977

theorem tailTrace_2464510 : CollatzResearch.WordTrace tailWord_2464510 prefixEnd_2464510 421826069270752608996977 := by
  unfold tailWord_2464510
  simp only [CollatzResearch.WordTrace]
  refine ⟨11236008037688581205395873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59925376201005766428777989 11236008037688581205395873)
  ·
    refine ⟨8427006028266435904046905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11236008037688581205395873 8427006028266435904046905)
    ·
      refine ⟨6320254521199826928035179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8427006028266435904046905 6320254521199826928035179)
      ·
        refine ⟨9480381781799740392052769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6320254521199826928035179 9480381781799740392052769)
        ·
          refine ⟨7110286336349805294039577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9480381781799740392052769 7110286336349805294039577)
          ·
            refine ⟨5332714752262353970529683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7110286336349805294039577 5332714752262353970529683)
            ·
              refine ⟨7999072128393530955794525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5332714752262353970529683 7999072128393530955794525)
              ·
                refine ⟨2999652048147574108422947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7999072128393530955794525 2999652048147574108422947)
                ·
                  refine ⟨4499478072221361162634421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2999652048147574108422947 4499478072221361162634421)
                  ·
                    refine ⟨421826069270752608996977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4499478072221361162634421 421826069270752608996977)
                    ·
                      rfl

theorem cell23_2464510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2464510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464510 prefixEnd_2464510 := by exact prefixLift 2464510
  have htrace : WordTrace (prefixWord ++ tailWord_2464510) baseStart_2464510 baseEnd_2464510 := by
    simpa [prefixWord, tailWord_2464510, baseEnd_2464510] using wordTrace_append hprefix tailTrace_2464510
  have hstable : (prefixWord ++ tailWord_2464510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464510).length < 2 ^ (prefixWord ++ tailWord_2464510).sum := by decide
  have hdescent : baseEnd_2464510 < baseStart_2464510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464526 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2464526 : Nat := 118140960795 + 2464526 * 2 ^ 59
def prefixEnd_2464526 : Nat := 4983230072969 + 3 ^ 40 * 2464526 * 2
def baseEnd_2464526 : Nat := 1265486423502729764390857

theorem tailTrace_2464526 : CollatzResearch.WordTrace tailWord_2464526 prefixEnd_2464526 1265486423502729764390857 := by
  unfold tailWord_2464526
  simp only [CollatzResearch.WordTrace]
  refine ⟨11236080983681335546968679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59925765246300456250499621 11236080983681335546968679)
  ·
    refine ⟨16854121475522003320453019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11236080983681335546968679 16854121475522003320453019)
    ·
      refine ⟨25281182213283004980679529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16854121475522003320453019 25281182213283004980679529)
      ·
        refine ⟨18960886659962253735509647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25281182213283004980679529 18960886659962253735509647)
        ·
          refine ⟨28441329989943380603264471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18960886659962253735509647 28441329989943380603264471)
          ·
            refine ⟨42661994984915070904896707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28441329989943380603264471 42661994984915070904896707)
            ·
              refine ⟨63992992477372606357345061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42661994984915070904896707 63992992477372606357345061)
              ·
                refine ⟨11998686089507363692002199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63992992477372606357345061 11998686089507363692002199)
                ·
                  refine ⟨17998029134261045538003299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11998686089507363692002199 17998029134261045538003299)
                  ·
                    refine ⟨26997043701391568307004949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17998029134261045538003299 26997043701391568307004949)
                    ·
                      refine ⟨1265486423502729764390857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26997043701391568307004949 1265486423502729764390857)
                      ·
                        rfl

theorem cell23_2464526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2464526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464526 prefixEnd_2464526 := by exact prefixLift 2464526
  have htrace : WordTrace (prefixWord ++ tailWord_2464526) baseStart_2464526 baseEnd_2464526 := by
    simpa [prefixWord, tailWord_2464526, baseEnd_2464526] using wordTrace_append hprefix tailTrace_2464526
  have hstable : (prefixWord ++ tailWord_2464526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464526).length < 2 ^ (prefixWord ++ tailWord_2464526).sum := by decide
  have hdescent : baseEnd_2464526 < baseStart_2464526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464543 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 4]
def baseStart_2464543 : Nat := 118140960795 + 2464543 * 2 ^ 59
def prefixEnd_2464543 : Nat := 4983230072969 + 3 ^ 40 * 2464543 * 2
def baseEnd_2464543 : Nat := 1265495152673856197878279

theorem tailTrace_2464543 : CollatzResearch.WordTrace tailWord_2464543 prefixEnd_2464543 1265495152673856197878279 := by
  unfold tailWord_2464543
  simp only [CollatzResearch.WordTrace]
  refine ⟨89889267910389096279118283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59926178606926064186078855 89889267910389096279118283)
  ·
    refine ⟨134833901865583644418677425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89889267910389096279118283 134833901865583644418677425)
    ·
      refine ⟨101125426399187733314008069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134833901865583644418677425 101125426399187733314008069)
      ·
        refine ⟨18961017449847699996376513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101125426399187733314008069 18961017449847699996376513)
        ·
          refine ⟨14220763087385774997282385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18961017449847699996376513 14220763087385774997282385)
          ·
            refine ⟨10665572315539331247961789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14220763087385774997282385 10665572315539331247961789)
            ·
              refine ⟨3999589618327249217985671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10665572315539331247961789 3999589618327249217985671)
              ·
                refine ⟨5999384427490873826978507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3999589618327249217985671 5999384427490873826978507)
                ·
                  refine ⟨8999076641236310740467761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5999384427490873826978507 8999076641236310740467761)
                  ·
                    refine ⟨6749307480927233055350821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8999076641236310740467761 6749307480927233055350821)
                    ·
                      refine ⟨1265495152673856197878279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6749307480927233055350821 1265495152673856197878279)
                      ·
                        rfl

theorem cell23_2464543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_2464543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464543 prefixEnd_2464543 := by exact prefixLift 2464543
  have htrace : WordTrace (prefixWord ++ tailWord_2464543) baseStart_2464543 baseEnd_2464543 := by
    simpa [prefixWord, tailWord_2464543, baseEnd_2464543] using wordTrace_append hprefix tailTrace_2464543
  have hstable : (prefixWord ++ tailWord_2464543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464543).length < 2 ^ (prefixWord ++ tailWord_2464543).sum := by decide
  have hdescent : baseEnd_2464543 < baseStart_2464543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464620 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 1, 4, 2]
def baseStart_2464620 : Nat := 118140960795 + 2464620 * 2 ^ 59
def prefixEnd_2464620 : Nat := 4983230072969 + 3 ^ 40 * 2464620 * 2
def baseEnd_2464620 : Nat := 1265534690684252396615425

theorem tailTrace_2464620 : CollatzResearch.WordTrace tailWord_2464620 prefixEnd_2464620 1265534690684252396615425 := by
  unfold tailWord_2464620
  simp only [CollatzResearch.WordTrace]
  refine ⟨44946038165555069214835657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59928050887406758953114209 44946038165555069214835657)
  ·
    refine ⟨33709528624166301911126743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44946038165555069214835657 33709528624166301911126743)
    ·
      refine ⟨50564292936249452866690115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33709528624166301911126743 50564292936249452866690115)
      ·
        refine ⟨75846439404374179300035173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50564292936249452866690115 75846439404374179300035173)
        ·
          refine ⟨14221207388320158618756595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75846439404374179300035173 14221207388320158618756595)
          ·
            refine ⟨21331811082480237928134893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14221207388320158618756595 21331811082480237928134893)
            ·
              refine ⟨7999429155930089223050585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21331811082480237928134893 7999429155930089223050585)
              ·
                refine ⟨5999571866947566917287939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7999429155930089223050585 5999571866947566917287939)
                ·
                  refine ⟨8999357800421350375931909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5999571866947566917287939 8999357800421350375931909)
                  ·
                    refine ⟨1687379587579003195487233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8999357800421350375931909 1687379587579003195487233)
                    ·
                      refine ⟨1265534690684252396615425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1687379587579003195487233 1265534690684252396615425)
                      ·
                        rfl

theorem cell23_2464620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 4, 2].length) (baseStart_2464620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464620 prefixEnd_2464620 := by exact prefixLift 2464620
  have htrace : WordTrace (prefixWord ++ tailWord_2464620) baseStart_2464620 baseEnd_2464620 := by
    simpa [prefixWord, tailWord_2464620, baseEnd_2464620] using wordTrace_append hprefix tailTrace_2464620
  have hstable : (prefixWord ++ tailWord_2464620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464620).length < 2 ^ (prefixWord ++ tailWord_2464620).sum := by decide
  have hdescent : baseEnd_2464620 < baseStart_2464620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464636 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_2464636 : Nat := 118140960795 + 2464636 * 2 ^ 59
def prefixEnd_2464636 : Nat := 4983230072969 + 3 ^ 40 * 2464636 * 2
def baseEnd_2464636 : Nat := 1265542906374724334015351

theorem tailTrace_2464636 : CollatzResearch.WordTrace tailWord_2464636 prefixEnd_2464636 1265542906374724334015351 := by
  unfold tailWord_2464636
  simp only [CollatzResearch.WordTrace]
  refine ⟨44946329949526086581126881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59928439932701448774835841 44946329949526086581126881)
  ·
    refine ⟨33709747462144564935845161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44946329949526086581126881 33709747462144564935845161)
    ·
      refine ⟨25282310596608423701883871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33709747462144564935845161 25282310596608423701883871)
      ·
        refine ⟨37923465894912635552825807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25282310596608423701883871 37923465894912635552825807)
        ·
          refine ⟨56885198842368953329238711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37923465894912635552825807 56885198842368953329238711)
          ·
            refine ⟨85327798263553429993858067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56885198842368953329238711 85327798263553429993858067)
            ·
              refine ⟨127991697395330144990787101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85327798263553429993858067 127991697395330144990787101)
              ·
                refine ⟨47996886523248804371545163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127991697395330144990787101 47996886523248804371545163)
                ·
                  refine ⟨71995329784873206557317745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47996886523248804371545163 71995329784873206557317745)
                  ·
                    refine ⟨53996497338654904917988309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71995329784873206557317745 53996497338654904917988309)
                    ·
                      refine ⟨1265542906374724334015351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53996497338654904917988309 1265542906374724334015351)
                      ·
                        rfl

theorem cell23_2464636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_2464636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464636 prefixEnd_2464636 := by exact prefixLift 2464636
  have htrace : WordTrace (prefixWord ++ tailWord_2464636) baseStart_2464636 baseEnd_2464636 := by
    simpa [prefixWord, tailWord_2464636, baseEnd_2464636] using wordTrace_append hprefix tailTrace_2464636
  have hstable : (prefixWord ++ tailWord_2464636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464636).length < 2 ^ (prefixWord ++ tailWord_2464636).sum := by decide
  have hdescent : baseEnd_2464636 < baseStart_2464636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464637 : List Nat := [1, 4, 1, 1, 2, 1, 3, 4, 2, 2, 2]
def baseStart_2464637 : Nat := 118140960795 + 2464637 * 2 ^ 59
def prefixEnd_2464637 : Nat := 4983230072969 + 3 ^ 40 * 2464637 * 2
def baseEnd_2464637 : Nat := 1265543419855378830102847

theorem tailTrace_2464637 : CollatzResearch.WordTrace tailWord_2464637 prefixEnd_2464637 1265543419855378830102847 := by
  unfold tailWord_2464637
  simp only [CollatzResearch.WordTrace]
  refine ⟨89892696372048550333040165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59928464248032366888693443 89892696372048550333040165)
  ·
    refine ⟨16854880569759103187445031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89892696372048550333040165 16854880569759103187445031)
    ·
      refine ⟨25282320854638654781167547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16854880569759103187445031 25282320854638654781167547)
      ·
        refine ⟨37923481281957982171751321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25282320854638654781167547 37923481281957982171751321)
        ·
          refine ⟨28442610961468486628813491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37923481281957982171751321 28442610961468486628813491)
          ·
            refine ⟨42663916442202729943220237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28442610961468486628813491 42663916442202729943220237)
            ·
              refine ⟨15998968665826023728707589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42663916442202729943220237 15998968665826023728707589)
              ·
                refine ⟨2999806624842379449132673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15998968665826023728707589 2999806624842379449132673)
                ·
                  refine ⟨2249854968631784586849505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2999806624842379449132673 2249854968631784586849505)
                  ·
                    refine ⟨1687391226473838440137129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2249854968631784586849505 1687391226473838440137129)
                    ·
                      refine ⟨1265543419855378830102847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1687391226473838440137129 1265543419855378830102847)
                      ·
                        rfl

theorem cell23_2464637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_2464637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464637 prefixEnd_2464637 := by exact prefixLift 2464637
  have htrace : WordTrace (prefixWord ++ tailWord_2464637) baseStart_2464637 baseEnd_2464637 := by
    simpa [prefixWord, tailWord_2464637, baseEnd_2464637] using wordTrace_append hprefix tailTrace_2464637
  have hstable : (prefixWord ++ tailWord_2464637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464637).length < 2 ^ (prefixWord ++ tailWord_2464637).sum := by decide
  have hdescent : baseEnd_2464637 < baseStart_2464637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464650 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2464650 : Nat := 118140960795 + 2464650 * 2 ^ 59
def prefixEnd_2464650 : Nat := 4983230072969 + 3 ^ 40 * 2464650 * 2
def baseEnd_2464650 : Nat := 1265550095103887279240287

theorem tailTrace_2464650 : CollatzResearch.WordTrace tailWord_2464650 prefixEnd_2464650 1265550095103887279240287 := by
  unfold tailWord_2464650
  simp only [CollatzResearch.WordTrace]
  refine ⟨22473292630250363388315851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59928780347334302368842269 22473292630250363388315851)
  ·
    refine ⟨33709938945375545082473777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22473292630250363388315851 33709938945375545082473777)
    ·
      refine ⟨25282454209031658811855333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33709938945375545082473777 25282454209031658811855333)
      ·
        refine ⟨4740460164193436027222875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25282454209031658811855333 4740460164193436027222875)
        ·
          refine ⟨7110690246290154040834313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4740460164193436027222875 7110690246290154040834313)
          ·
            refine ⟨5333017684717615530625735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7110690246290154040834313 5333017684717615530625735)
            ·
              refine ⟨7999526527076423295938603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5333017684717615530625735 7999526527076423295938603)
              ·
                refine ⟨11999289790614634943907905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7999526527076423295938603 11999289790614634943907905)
                ·
                  refine ⟨8999467342960976207930929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11999289790614634943907905 8999467342960976207930929)
                  ·
                    refine ⟨6749600507220732155948197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8999467342960976207930929 6749600507220732155948197)
                    ·
                      refine ⟨1265550095103887279240287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6749600507220732155948197 1265550095103887279240287)
                      ·
                        rfl

theorem cell23_2464650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2464650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464650 prefixEnd_2464650 := by exact prefixLift 2464650
  have htrace : WordTrace (prefixWord ++ tailWord_2464650) baseStart_2464650 baseEnd_2464650 := by
    simpa [prefixWord, tailWord_2464650, baseEnd_2464650] using wordTrace_append hprefix tailTrace_2464650
  have hstable : (prefixWord ++ tailWord_2464650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464650).length < 2 ^ (prefixWord ++ tailWord_2464650).sum := by decide
  have hdescent : baseEnd_2464650 < baseStart_2464650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464730 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3]
def baseStart_2464730 : Nat := 118140960795 + 2464730 * 2 ^ 59
def prefixEnd_2464730 : Nat := 4983230072969 + 3 ^ 40 * 2464730 * 2
def baseEnd_2464730 : Nat := 1265591173556246966239919

theorem tailTrace_2464730 : CollatzResearch.WordTrace tailWord_2464730 prefixEnd_2464730 1265591173556246966239919 := by
  unfold tailWord_2464730
  simp only [CollatzResearch.WordTrace]
  refine ⟨22474022090177906804043911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59930725573807751477450429 22474022090177906804043911)
  ·
    refine ⟨33711033135266860206065867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22474022090177906804043911 33711033135266860206065867)
    ·
      refine ⟨50566549702900290309098801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33711033135266860206065867 50566549702900290309098801)
      ·
        refine ⟨37924912277175217731824101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50566549702900290309098801 37924912277175217731824101)
        ·
          refine ⟨7110921051970353324717019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37924912277175217731824101 7110921051970353324717019)
          ·
            refine ⟨10666381577955529987075529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7110921051970353324717019 10666381577955529987075529)
            ·
              refine ⟨7999786183466647490306647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10666381577955529987075529 7999786183466647490306647)
              ·
                refine ⟨11999679275199971235459971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7999786183466647490306647 11999679275199971235459971)
                ·
                  refine ⟨17999518912799956853189957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11999679275199971235459971 17999518912799956853189957)
                  ·
                    refine ⟨3374909796149991909973117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17999518912799956853189957 3374909796149991909973117)
                    ·
                      refine ⟨1265591173556246966239919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3374909796149991909973117 1265591173556246966239919)
                      ·
                        rfl

theorem cell23_2464730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_2464730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464730 prefixEnd_2464730 := by exact prefixLift 2464730
  have htrace : WordTrace (prefixWord ++ tailWord_2464730) baseStart_2464730 baseEnd_2464730 := by
    simpa [prefixWord, tailWord_2464730, baseEnd_2464730] using wordTrace_append hprefix tailTrace_2464730
  have hstable : (prefixWord ++ tailWord_2464730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464730).length < 2 ^ (prefixWord ++ tailWord_2464730).sum := by decide
  have hdescent : baseEnd_2464730 < baseStart_2464730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464763 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 3, 5]
def baseStart_2464763 : Nat := 118140960795 + 2464763 * 2 ^ 59
def prefixEnd_2464763 : Nat := 4983230072969 + 3 ^ 40 * 2464763 * 2
def baseEnd_2464763 : Nat := 421869372805948445709089

theorem tailTrace_2464763 : CollatzResearch.WordTrace tailWord_2464763 prefixEnd_2464763 421869372805948445709089 := by
  unfold tailWord_2464763
  simp only [CollatzResearch.WordTrace]
  refine ⟨89897291969592073852126943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59931527979728049234751295 89897291969592073852126943)
  ·
    refine ⟨134845937954388110778190415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89897291969592073852126943 134845937954388110778190415)
    ·
      refine ⟨202268906931582166167285623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134845937954388110778190415 202268906931582166167285623)
      ·
        refine ⟨303403360397373249250928435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202268906931582166167285623 303403360397373249250928435)
        ·
          refine ⟨455105040596059873876392653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303403360397373249250928435 455105040596059873876392653)
          ·
            refine ⟨170664390223522452703647245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 455105040596059873876392653 170664390223522452703647245)
            ·
              refine ⟨63999146333820919763867717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170664390223522452703647245 63999146333820919763867717)
              ·
                refine ⟨11999839937591422455725197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63999146333820919763867717 11999839937591422455725197)
                ·
                  refine ⟨4499939976596783420896949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11999839937591422455725197 4499939976596783420896949)
                  ·
                    refine ⟨421869372805948445709089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4499939976596783420896949 421869372805948445709089)
                    ·
                      rfl

theorem cell23_2464763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 5].length) (baseStart_2464763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464763 prefixEnd_2464763 := by exact prefixLift 2464763
  have htrace : WordTrace (prefixWord ++ tailWord_2464763) baseStart_2464763 baseEnd_2464763 := by
    simpa [prefixWord, tailWord_2464763, baseEnd_2464763] using wordTrace_append hprefix tailTrace_2464763
  have hstable : (prefixWord ++ tailWord_2464763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464763).length < 2 ^ (prefixWord ++ tailWord_2464763).sum := by decide
  have hdescent : baseEnd_2464763 < baseStart_2464763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464780 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 3, 5]
def baseStart_2464780 : Nat := 118140960795 + 2464780 * 2 ^ 59
def prefixEnd_2464780 : Nat := 4983230072969 + 3 ^ 40 * 2464780 * 2
def baseEnd_2464780 : Nat := 421872282529657256871563

theorem tailTrace_2464780 : CollatzResearch.WordTrace tailWord_2464780 prefixEnd_2464780 421872282529657256871563 := by
  unfold tailWord_2464780
  simp only [CollatzResearch.WordTrace]
  refine ⟨44948956005265242877747897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59931941340353657170330529 44948956005265242877747897)
  ·
    refine ⟨33711717003948932158310923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44948956005265242877747897 33711717003948932158310923)
    ·
      refine ⟨50567575505923398237466385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33711717003948932158310923 50567575505923398237466385)
      ·
        refine ⟨37925681629442548678099789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50567575505923398237466385 37925681629442548678099789)
        ·
          refine ⟨14222130611040955754287421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37925681629442548678099789 14222130611040955754287421)
          ·
            refine ⟨5333298979140358407857783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14222130611040955754287421 5333298979140358407857783)
            ·
              refine ⟨7999948468710537611786675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5333298979140358407857783 7999948468710537611786675)
              ·
                refine ⟨11999922703065806417680013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7999948468710537611786675 11999922703065806417680013)
                ·
                  refine ⟨4499971013649677406630005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11999922703065806417680013 4499971013649677406630005)
                  ·
                    refine ⟨421872282529657256871563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4499971013649677406630005 421872282529657256871563)
                    ·
                      rfl

theorem cell23_2464780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_2464780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464780 prefixEnd_2464780 := by exact prefixLift 2464780
  have htrace : WordTrace (prefixWord ++ tailWord_2464780) baseStart_2464780 baseEnd_2464780 := by
    simpa [prefixWord, tailWord_2464780, baseEnd_2464780] using wordTrace_append hprefix tailTrace_2464780
  have hstable : (prefixWord ++ tailWord_2464780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464780).length < 2 ^ (prefixWord ++ tailWord_2464780).sum := by decide
  have hdescent : baseEnd_2464780 < baseStart_2464780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464793 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 3, 6]
def baseStart_2464793 : Nat := 118140960795 + 2464793 * 2 ^ 59
def prefixEnd_2464793 : Nat := 4983230072969 + 3 ^ 40 * 2464793 * 2
def baseEnd_2464793 : Nat := 421874507612493406584043

theorem tailTrace_2464793 : CollatzResearch.WordTrace tailWord_2464793 prefixEnd_2464793 421874507612493406584043 := by
  unfold tailWord_2464793
  simp only [CollatzResearch.WordTrace]
  refine ⟨89898386159483388975719033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59932257439655592650479355 89898386159483388975719033)
  ·
    refine ⟨67423789619612541731789275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89898386159483388975719033 67423789619612541731789275)
    ·
      refine ⟨101135684429418812597683913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67423789619612541731789275 101135684429418812597683913)
      ·
        refine ⟨75851763322064109448262935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101135684429418812597683913 75851763322064109448262935)
        ·
          refine ⟨113777644983096164172394403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75851763322064109448262935 113777644983096164172394403)
          ·
            refine ⟨170666467474644246258591605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113777644983096164172394403 170666467474644246258591605)
            ·
              refine ⟨15999981325747898086742963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170666467474644246258591605 15999981325747898086742963)
              ·
                refine ⟨23999971988621847130114445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15999981325747898086742963 23999971988621847130114445)
                ·
                  refine ⟨8999989495733192673792917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23999971988621847130114445 8999989495733192673792917)
                  ·
                    refine ⟨421874507612493406584043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8999989495733192673792917 421874507612493406584043)
                    ·
                      rfl

theorem cell23_2464793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_2464793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464793 prefixEnd_2464793 := by exact prefixLift 2464793
  have htrace : WordTrace (prefixWord ++ tailWord_2464793) baseStart_2464793 baseEnd_2464793 := by
    simpa [prefixWord, tailWord_2464793, baseEnd_2464793] using wordTrace_append hprefix tailTrace_2464793
  have hstable : (prefixWord ++ tailWord_2464793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464793).length < 2 ^ (prefixWord ++ tailWord_2464793).sum := by decide
  have hdescent : baseEnd_2464793 < baseStart_2464793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464794 : List Nat := [3, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3]
def baseStart_2464794 : Nat := 118140960795 + 2464794 * 2 ^ 59
def prefixEnd_2464794 : Nat := 4983230072969 + 3 ^ 40 * 2464794 * 2
def baseEnd_2464794 : Nat := 1265624036318134715839625

theorem tailTrace_2464794 : CollatzResearch.WordTrace tailWord_2464794 prefixEnd_2464794 1265624036318134715839625 := by
  unfold tailWord_2464794
  simp only [CollatzResearch.WordTrace]
  refine ⟨22474605658119941536626359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59932281754986510764336957 22474605658119941536626359)
  ·
    refine ⟨33711908487179912304939539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22474605658119941536626359 33711908487179912304939539)
    ·
      refine ⟨50567862730769868457409309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33711908487179912304939539 50567862730769868457409309)
      ·
        refine ⟨18962948524038700671528491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50567862730769868457409309 18962948524038700671528491)
        ·
          refine ⟨28444422786058051007292737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18962948524038700671528491 28444422786058051007292737)
          ·
            refine ⟨21333317089543538255469553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28444422786058051007292737 21333317089543538255469553)
            ·
              refine ⟨15999987817157653691602165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21333317089543538255469553 15999987817157653691602165)
              ·
                refine ⟨1499998857858530033587703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15999987817157653691602165 1499998857858530033587703)
                ·
                  refine ⟨2249998286787795050381555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499998857858530033587703 2249998286787795050381555)
                  ·
                    refine ⟨3374997430181692575572333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2249998286787795050381555 3374997430181692575572333)
                    ·
                      refine ⟨1265624036318134715839625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3374997430181692575572333 1265624036318134715839625)
                      ·
                        rfl

theorem cell23_2464794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_2464794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464794 prefixEnd_2464794 := by exact prefixLift 2464794
  have htrace : WordTrace (prefixWord ++ tailWord_2464794) baseStart_2464794 baseEnd_2464794 := by
    simpa [prefixWord, tailWord_2464794, baseEnd_2464794] using wordTrace_append hprefix tailTrace_2464794
  have hstable : (prefixWord ++ tailWord_2464794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464794).length < 2 ^ (prefixWord ++ tailWord_2464794).sum := by decide
  have hdescent : baseEnd_2464794 < baseStart_2464794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464804 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 2, 3, 2]
def baseStart_2464804 : Nat := 118140960795 + 2464804 * 2 ^ 59
def prefixEnd_2464804 : Nat := 4983230072969 + 3 ^ 40 * 2464804 * 2
def baseEnd_2464804 : Nat := 1265629171124679676714579

theorem tailTrace_2464804 : CollatzResearch.WordTrace tailWord_2464804 prefixEnd_2464804 1265629171124679676714579 := by
  unfold tailWord_2464804
  simp only [CollatzResearch.WordTrace]
  refine ⟨44949393681221768927184733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59932524908295691902912977 44949393681221768927184733)
  ·
    refine ⟨16856022630458163347694275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44949393681221768927184733 16856022630458163347694275)
    ·
      refine ⟨25284033945687245021541413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16856022630458163347694275 25284033945687245021541413)
      ·
        refine ⟨4740756364816358441539015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25284033945687245021541413 4740756364816358441539015)
        ·
          refine ⟨7111134547224537662308523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4740756364816358441539015 7111134547224537662308523)
          ·
            refine ⟨10666701820836806493462785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7111134547224537662308523 10666701820836806493462785)
            ·
              refine ⟨8000026365627604870097089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10666701820836806493462785 8000026365627604870097089)
              ·
                refine ⟨6000019774220703652572817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8000026365627604870097089 6000019774220703652572817)
                ·
                  refine ⟨4500014830665527739429613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6000019774220703652572817 4500014830665527739429613)
                  ·
                    refine ⟨1687505561499572902286105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4500014830665527739429613 1687505561499572902286105)
                    ·
                      refine ⟨1265629171124679676714579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1687505561499572902286105 1265629171124679676714579)
                      ·
                        rfl

theorem cell23_2464804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_2464804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464804 prefixEnd_2464804 := by exact prefixLift 2464804
  have htrace : WordTrace (prefixWord ++ tailWord_2464804) baseStart_2464804 baseEnd_2464804 := by
    simpa [prefixWord, tailWord_2464804, baseEnd_2464804] using wordTrace_append hprefix tailTrace_2464804
  have hstable : (prefixWord ++ tailWord_2464804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464804).length < 2 ^ (prefixWord ++ tailWord_2464804).sum := by decide
  have hdescent : baseEnd_2464804 < baseStart_2464804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464838 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_2464838 : Nat := 118140960795 + 2464838 * 2 ^ 59
def prefixEnd_2464838 : Nat := 4983230072969 + 3 ^ 40 * 2464838 * 2
def baseEnd_2464838 : Nat := 1265646629466932543689423

theorem tailTrace_2464838 : CollatzResearch.WordTrace tailWord_2464838 prefixEnd_2464838 1265646629466932543689423 := by
  unfold tailWord_2464838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2809375857635011301909599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59933351629546907774071445 2809375857635011301909599)
  ·
    refine ⟨4214063786452516952864399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2809375857635011301909599 4214063786452516952864399)
    ·
      refine ⟨6321095679678775429296599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4214063786452516952864399 6321095679678775429296599)
      ·
        refine ⟨9481643519518163143944899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6321095679678775429296599 9481643519518163143944899)
        ·
          refine ⟨14222465279277244715917349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9481643519518163143944899 14222465279277244715917349)
          ·
            refine ⟨2666712239864483384234503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14222465279277244715917349 2666712239864483384234503)
            ·
              refine ⟨4000068359796725076351755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2666712239864483384234503 4000068359796725076351755)
              ·
                refine ⟨6000102539695087614527633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4000068359796725076351755 6000102539695087614527633)
                ·
                  refine ⟨4500076904771315710895725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6000102539695087614527633 4500076904771315710895725)
                  ·
                    refine ⟨1687528839289243391585897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4500076904771315710895725 1687528839289243391585897)
                    ·
                      refine ⟨1265646629466932543689423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1687528839289243391585897 1265646629466932543689423)
                      ·
                        rfl

theorem cell23_2464838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_2464838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464838 prefixEnd_2464838 := by exact prefixLift 2464838
  have htrace : WordTrace (prefixWord ++ tailWord_2464838) baseStart_2464838 baseEnd_2464838 := by
    simpa [prefixWord, tailWord_2464838, baseEnd_2464838] using wordTrace_append hprefix tailTrace_2464838
  have hstable : (prefixWord ++ tailWord_2464838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464838).length < 2 ^ (prefixWord ++ tailWord_2464838).sum := by decide
  have hdescent : baseEnd_2464838 < baseStart_2464838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464840 : List Nat := [2, 1, 3, 1, 1, 1, 7, 7]
def baseStart_2464840 : Nat := 118140960795 + 2464840 * 2 ^ 59
def prefixEnd_2464840 : Nat := 4983230072969 + 3 ^ 40 * 2464840 * 2
def baseEnd_2464840 : Nat := 46875839126971908735719

theorem tailTrace_2464840 : CollatzResearch.WordTrace tailWord_2464840 prefixEnd_2464840 46875839126971908735719 := by
  unfold tailWord_2464840
  simp only [CollatzResearch.WordTrace]
  refine ⟨44950050195156558001339987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59933400260208744001786649 44950050195156558001339987)
  ·
    refine ⟨67425075292734837002009981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44950050195156558001339987 67425075292734837002009981)
    ·
      refine ⟨25284403234775563875753743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67425075292734837002009981 25284403234775563875753743)
      ·
        refine ⟨37926604852163345813630615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25284403234775563875753743 37926604852163345813630615)
        ·
          refine ⟨56889907278245018720445923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37926604852163345813630615 56889907278245018720445923)
          ·
            refine ⟨85334860917367528080668885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56889907278245018720445923 85334860917367528080668885)
            ·
              refine ⟨2000035802750801439390677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 85334860917367528080668885 2000035802750801439390677)
              ·
                refine ⟨46875839126971908735719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2000035802750801439390677 46875839126971908735719)
                ·
                  rfl

theorem cell23_2464840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 7].length) (baseStart_2464840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2464840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2464840 prefixEnd_2464840 := by exact prefixLift 2464840
  have htrace : WordTrace (prefixWord ++ tailWord_2464840) baseStart_2464840 baseEnd_2464840 := by
    simpa [prefixWord, tailWord_2464840, baseEnd_2464840] using wordTrace_append hprefix tailTrace_2464840
  have hstable : (prefixWord ++ tailWord_2464840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464840).length < 2 ^ (prefixWord ++ tailWord_2464840).sum := by decide
  have hdescent : baseEnd_2464840 < baseStart_2464840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
