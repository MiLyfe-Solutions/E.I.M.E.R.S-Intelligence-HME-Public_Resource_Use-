import V185TrunkScan23Chunk0350

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2076553 : List Nat := [1, 2, 1, 1, 5, 1, 5, 1, 2, 2, 2]
def baseStart_2076553 : Nat := 118140960795 + 2076553 * 2 ^ 59
def prefixEnd_2076553 : Nat := 4983230072969 + 3 ^ 40 * 2076553 * 2
def baseEnd_2076553 : Nat := 1066269793535919210537613

theorem tailTrace_2076553 : CollatzResearch.WordTrace tailWord_2076553 prefixEnd_2076553 1066269793535919210537613 := by
  unfold tailWord_2076553
  simp only [CollatzResearch.WordTrace]
  refine ⟨75738110046010602862618313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50492073364007068575078875 75738110046010602862618313)
  ·
    refine ⟨56803582534507952146963735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75738110046010602862618313 56803582534507952146963735)
    ·
      refine ⟨85205373801761928220445603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56803582534507952146963735 85205373801761928220445603)
      ·
        refine ⟨127808060702642892330668405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85205373801761928220445603 127808060702642892330668405)
        ·
          refine ⟨11982005690872771156000163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127808060702642892330668405 11982005690872771156000163)
          ·
            refine ⟨17973008536309156734000245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11982005690872771156000163 17973008536309156734000245)
            ·
              refine ⟨1684969550278983443812523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17973008536309156734000245 1684969550278983443812523)
              ·
                refine ⟨2527454325418475165718785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684969550278983443812523 2527454325418475165718785)
                ·
                  refine ⟨1895590744063856374289089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2527454325418475165718785 1895590744063856374289089)
                  ·
                    refine ⟨1421693058047892280716817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1895590744063856374289089 1421693058047892280716817)
                    ·
                      refine ⟨1066269793535919210537613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421693058047892280716817 1066269793535919210537613)
                      ·
                        rfl

theorem cell23_2076553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 2, 2, 2].length) (baseStart_2076553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076553 prefixEnd_2076553 := by exact prefixLift 2076553
  have htrace : WordTrace (prefixWord ++ tailWord_2076553) baseStart_2076553 baseEnd_2076553 := by
    simpa [prefixWord, tailWord_2076553, baseEnd_2076553] using wordTrace_append hprefix tailTrace_2076553
  have hstable : (prefixWord ++ tailWord_2076553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076553).length < 2 ^ (prefixWord ++ tailWord_2076553).sum := by decide
  have hdescent : baseEnd_2076553 < baseStart_2076553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076604 : List Nat := [2, 2, 2, 5, 2, 1, 2, 1, 2, 2, 2]
def baseStart_2076604 : Nat := 118140960795 + 2076604 * 2 ^ 59
def prefixEnd_2076604 : Nat := 4983230072969 + 3 ^ 40 * 2076604 * 2
def baseEnd_2076604 : Nat := 1066295981049298510999879

theorem tailTrace_2076604 : CollatzResearch.WordTrace tailWord_2076604 prefixEnd_2076604 1066295981049298510999879 := by
  unfold tailWord_2076604
  simp only [CollatzResearch.WordTrace]
  refine ⟨37869985084412919286362433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50493313445883892381816577 37869985084412919286362433)
  ·
    refine ⟨28402488813309689464771825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37869985084412919286362433 28402488813309689464771825)
    ·
      refine ⟨21301866609982267098578869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28402488813309689464771825 21301866609982267098578869)
      ·
        refine ⟨1997049994685837540491769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21301866609982267098578869 1997049994685837540491769)
        ·
          refine ⟨1497787496014378155368827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1997049994685837540491769 1497787496014378155368827)
          ·
            refine ⟨2246681244021567233053241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497787496014378155368827 2246681244021567233053241)
            ·
              refine ⟨1685010933016175424789931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246681244021567233053241 1685010933016175424789931)
              ·
                refine ⟨2527516399524263137184897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685010933016175424789931 2527516399524263137184897)
                ·
                  refine ⟨1895637299643197352888673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2527516399524263137184897 1895637299643197352888673)
                  ·
                    refine ⟨1421727974732398014666505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1895637299643197352888673 1421727974732398014666505)
                    ·
                      refine ⟨1066295981049298510999879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421727974732398014666505 1066295981049298510999879)
                      ·
                        rfl

theorem cell23_2076604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_2076604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076604 prefixEnd_2076604 := by exact prefixLift 2076604
  have htrace : WordTrace (prefixWord ++ tailWord_2076604) baseStart_2076604 baseEnd_2076604 := by
    simpa [prefixWord, tailWord_2076604, baseEnd_2076604] using wordTrace_append hprefix tailTrace_2076604
  have hstable : (prefixWord ++ tailWord_2076604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076604).length < 2 ^ (prefixWord ++ tailWord_2076604).sum := by decide
  have hdescent : baseEnd_2076604 < baseStart_2076604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076659 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 7, 1, 3]
def baseStart_2076659 : Nat := 118140960795 + 2076659 * 2 ^ 59
def prefixEnd_2076659 : Nat := 4983230072969 + 3 ^ 40 * 2076659 * 2
def baseEnd_2076659 : Nat := 1066324222485295795812125

theorem tailTrace_2076659 : CollatzResearch.WordTrace tailWord_2076659 prefixEnd_2076659 1066324222485295795812125 := by
  unfold tailWord_2076659
  simp only [CollatzResearch.WordTrace]
  refine ⟨75741976183626582965977031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50494650789084388643984687 75741976183626582965977031)
  ·
    refine ⟨113612964275439874448965547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75741976183626582965977031 113612964275439874448965547)
    ·
      refine ⟨170419446413159811673448321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113612964275439874448965547 170419446413159811673448321)
      ·
        refine ⟨127814584809869858755086241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170419446413159811673448321 127814584809869858755086241)
        ·
          refine ⟨95860938607402394066314681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127814584809869858755086241 95860938607402394066314681)
          ·
            refine ⟨71895703955551795549736011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95860938607402394066314681 71895703955551795549736011)
            ·
              refine ⟨107843555933327693324604017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71895703955551795549736011 107843555933327693324604017)
              ·
                refine ⟨80882666949995769993453013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107843555933327693324604017 80882666949995769993453013)
                ·
                  refine ⟨1895687506640525859221555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 80882666949995769993453013 1895687506640525859221555)
                  ·
                    refine ⟨2843531259960788788832333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1895687506640525859221555 2843531259960788788832333)
                    ·
                      refine ⟨1066324222485295795812125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2843531259960788788832333 1066324222485295795812125)
                      ·
                        rfl

theorem cell23_2076659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 1, 3].length) (baseStart_2076659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076659 prefixEnd_2076659 := by exact prefixLift 2076659
  have htrace : WordTrace (prefixWord ++ tailWord_2076659) baseStart_2076659 baseEnd_2076659 := by
    simpa [prefixWord, tailWord_2076659, baseEnd_2076659] using wordTrace_append hprefix tailTrace_2076659
  have hstable : (prefixWord ++ tailWord_2076659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076659).length < 2 ^ (prefixWord ++ tailWord_2076659).sum := by decide
  have hdescent : baseEnd_2076659 < baseStart_2076659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076679 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 3, 5]
def baseStart_2076679 : Nat := 118140960795 + 2076679 * 2 ^ 59
def prefixEnd_2076679 : Nat := 4983230072969 + 3 ^ 40 * 2076679 * 2
def baseEnd_2076679 : Nat := 355444830699461905854011

theorem tailTrace_2076679 : CollatzResearch.WordTrace tailWord_2076679 prefixEnd_2076679 355444830699461905854011 := by
  unfold tailWord_2076679
  simp only [CollatzResearch.WordTrace]
  refine ⟨75742705643554126381705091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50495137095702750921136727 75742705643554126381705091)
  ·
    refine ⟨113614058465331189572557637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75742705643554126381705091 113614058465331189572557637)
    ·
      refine ⟨21302635962249598044854557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113614058465331189572557637 21302635962249598044854557)
      ·
        refine ⟨7988488485843599266820459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21302635962249598044854557 7988488485843599266820459)
        ·
          refine ⟨11982732728765398900230689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7988488485843599266820459 11982732728765398900230689)
          ·
            refine ⟨8987049546574049175173017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11982732728765398900230689 8987049546574049175173017)
            ·
              refine ⟨6740287159930536881379763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8987049546574049175173017 6740287159930536881379763)
              ·
                refine ⟨10110430739895805322069645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6740287159930536881379763 10110430739895805322069645)
                ·
                  refine ⟨3791411527460926995776117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10110430739895805322069645 3791411527460926995776117)
                  ·
                    refine ⟨355444830699461905854011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3791411527460926995776117 355444830699461905854011)
                    ·
                      rfl

theorem cell23_2076679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_2076679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076679 prefixEnd_2076679 := by exact prefixLift 2076679
  have htrace : WordTrace (prefixWord ++ tailWord_2076679) baseStart_2076679 baseEnd_2076679 := by
    simpa [prefixWord, tailWord_2076679, baseEnd_2076679] using wordTrace_append hprefix tailTrace_2076679
  have hstable : (prefixWord ++ tailWord_2076679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076679).length < 2 ^ (prefixWord ++ tailWord_2076679).sum := by decide
  have hdescent : baseEnd_2076679 < baseStart_2076679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076686 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2]
def baseStart_2076686 : Nat := 118140960795 + 2076686 * 2 ^ 59
def prefixEnd_2076686 : Nat := 4983230072969 + 3 ^ 40 * 2076686 * 2
def baseEnd_2076686 : Nat := 1066338086462967190174501

theorem tailTrace_2076686 : CollatzResearch.WordTrace tailWord_2076686 prefixEnd_2076686 1066338086462967190174501 := by
  unfold tailWord_2076686
  simp only [CollatzResearch.WordTrace]
  refine ⟨9467870119316095822151239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50495307303019177718139941 9467870119316095822151239)
  ·
    refine ⟨14201805178974143733226859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9467870119316095822151239 14201805178974143733226859)
    ·
      refine ⟨21302707768461215599840289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14201805178974143733226859 21302707768461215599840289)
      ·
        refine ⟨15977030826345911699880217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21302707768461215599840289 15977030826345911699880217)
        ·
          refine ⟨11982773119759433774910163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15977030826345911699880217 11982773119759433774910163)
          ·
            refine ⟨17974159679639150662365245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11982773119759433774910163 17974159679639150662365245)
            ·
              refine ⟨6740309879864681498386967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17974159679639150662365245 6740309879864681498386967)
              ·
                refine ⟨10110464819797022247580451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6740309879864681498386967 10110464819797022247580451)
                ·
                  refine ⟨15165697229695533371370677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10110464819797022247580451 15165697229695533371370677)
                  ·
                    refine ⟨1421784115283956253566001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15165697229695533371370677 1421784115283956253566001)
                    ·
                      refine ⟨1066338086462967190174501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421784115283956253566001 1066338086462967190174501)
                      ·
                        rfl

theorem cell23_2076686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_2076686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076686 prefixEnd_2076686 := by exact prefixLift 2076686
  have htrace : WordTrace (prefixWord ++ tailWord_2076686) baseStart_2076686 baseEnd_2076686 := by
    simpa [prefixWord, tailWord_2076686, baseEnd_2076686] using wordTrace_append hprefix tailTrace_2076686
  have hstable : (prefixWord ++ tailWord_2076686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076686).length < 2 ^ (prefixWord ++ tailWord_2076686).sum := by decide
  have hdescent : baseEnd_2076686 < baseStart_2076686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076719 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 3]
def baseStart_2076719 : Nat := 118140960795 + 2076719 * 2 ^ 59
def prefixEnd_2076719 : Nat := 4983230072969 + 3 ^ 40 * 2076719 * 2
def baseEnd_2076719 : Nat := 1066355031324565561061849

theorem tailTrace_2076719 : CollatzResearch.WordTrace tailWord_2076719 prefixEnd_2076719 1066355031324565561061849 := by
  unfold tailWord_2076719
  simp only [CollatzResearch.WordTrace]
  refine ⟨75744164563409213213161211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50496109708939475475440807 75744164563409213213161211)
  ·
    refine ⟨113616246845113819819741817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75744164563409213213161211 113616246845113819819741817)
    ·
      refine ⟨85212185133835364864806363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113616246845113819819741817 85212185133835364864806363)
      ·
        refine ⟨127818277700753047297209545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85212185133835364864806363 127818277700753047297209545)
        ·
          refine ⟨95863708275564785472907159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127818277700753047297209545 95863708275564785472907159)
          ·
            refine ⟨143795562413347178209360739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95863708275564785472907159 143795562413347178209360739)
            ·
              refine ⟨215693343620020767314041109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143795562413347178209360739 215693343620020767314041109)
              ·
                refine ⟨10110625482188473467845677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 215693343620020767314041109 10110625482188473467845677)
                ·
                  refine ⟨3791484555820677550442129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10110625482188473467845677 3791484555820677550442129)
                  ·
                    refine ⟨2843613416865508162831597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3791484555820677550442129 2843613416865508162831597)
                    ·
                      refine ⟨1066355031324565561061849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2843613416865508162831597 1066355031324565561061849)
                      ·
                        rfl

theorem cell23_2076719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 3].length) (baseStart_2076719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076719 prefixEnd_2076719 := by exact prefixLift 2076719
  have htrace : WordTrace (prefixWord ++ tailWord_2076719) baseStart_2076719 baseEnd_2076719 := by
    simpa [prefixWord, tailWord_2076719, baseEnd_2076719] using wordTrace_append hprefix tailTrace_2076719
  have hstable : (prefixWord ++ tailWord_2076719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076719).length < 2 ^ (prefixWord ++ tailWord_2076719).sum := by decide
  have hdescent : baseEnd_2076719 < baseStart_2076719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076733 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 3, 2, 2]
def baseStart_2076733 : Nat := 118140960795 + 2076733 * 2 ^ 59
def prefixEnd_2076733 : Nat := 4983230072969 + 3 ^ 40 * 2076733 * 2
def baseEnd_2076733 : Nat := 1066362220053728506286785

theorem tailTrace_2076733 : CollatzResearch.WordTrace tailWord_2076733 prefixEnd_2076733 1066362220053728506286785 := by
  unfold tailWord_2076733
  simp only [CollatzResearch.WordTrace]
  refine ⟨75744675185358493604170853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50496450123572329069447235 75744675185358493604170853)
  ·
    refine ⟨14202126597254717550782035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75744675185358493604170853 14202126597254717550782035)
    ·
      refine ⟨21303189895882076326173053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14202126597254717550782035 21303189895882076326173053)
      ·
        refine ⟨7988696210955778622314895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21303189895882076326173053 7988696210955778622314895)
        ·
          refine ⟨11983044316433667933472343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7988696210955778622314895 11983044316433667933472343)
          ·
            refine ⟨17974566474650501900208515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11983044316433667933472343 17974566474650501900208515)
            ·
              refine ⟨26961849711975752850312773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17974566474650501900208515 26961849711975752850312773)
              ·
                refine ⟨5055346820995453659433645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26961849711975752850312773 5055346820995453659433645)
                ·
                  refine ⟨1895755057873295122287617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5055346820995453659433645 1895755057873295122287617)
                  ·
                    refine ⟨1421816293404971341715713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1895755057873295122287617 1421816293404971341715713)
                    ·
                      refine ⟨1066362220053728506286785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421816293404971341715713 1066362220053728506286785)
                      ·
                        rfl

theorem cell23_2076733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_2076733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076733 prefixEnd_2076733 := by exact prefixLift 2076733
  have htrace : WordTrace (prefixWord ++ tailWord_2076733) baseStart_2076733 baseEnd_2076733 := by
    simpa [prefixWord, tailWord_2076733, baseEnd_2076733] using wordTrace_append hprefix tailTrace_2076733
  have hstable : (prefixWord ++ tailWord_2076733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076733).length < 2 ^ (prefixWord ++ tailWord_2076733).sum := by decide
  have hdescent : baseEnd_2076733 < baseStart_2076733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076736 : List Nat := [2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 3]
def baseStart_2076736 : Nat := 118140960795 + 2076736 * 2 ^ 59
def prefixEnd_2076736 : Nat := 4983230072969 + 3 ^ 40 * 2076736 * 2
def baseEnd_2076736 : Nat := 1066363760495691994549271

theorem tailTrace_2076736 : CollatzResearch.WordTrace tailWord_2076736 prefixEnd_2076736 1066363760495691994549271 := by
  unfold tailWord_2076736
  simp only [CollatzResearch.WordTrace]
  refine ⟨37872392302173812558265031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50496523069565083411020041 37872392302173812558265031)
  ·
    refine ⟨56808588453260718837397547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37872392302173812558265031 56808588453260718837397547)
    ·
      refine ⟨85212882679891078256096321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56808588453260718837397547 85212882679891078256096321)
      ·
        refine ⟨63909662009918308692072241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85212882679891078256096321 63909662009918308692072241)
        ·
          refine ⟨47932246507438731519054181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63909662009918308692072241 47932246507438731519054181)
          ·
            refine ⟨8987296220144762159822659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47932246507438731519054181 8987296220144762159822659)
            ·
              refine ⟨13480944330217143239733989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8987296220144762159822659 13480944330217143239733989)
              ·
                refine ⟨2527677061915714357450123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13480944330217143239733989 2527677061915714357450123)
                ·
                  refine ⟨3791515592873571536175185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527677061915714357450123 3791515592873571536175185)
                  ·
                    refine ⟨2843636694655178652131389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3791515592873571536175185 2843636694655178652131389)
                    ·
                      refine ⟨1066363760495691994549271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2843636694655178652131389 1066363760495691994549271)
                      ·
                        rfl

theorem cell23_2076736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_2076736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076736 prefixEnd_2076736 := by exact prefixLift 2076736
  have htrace : WordTrace (prefixWord ++ tailWord_2076736) baseStart_2076736 baseEnd_2076736 := by
    simpa [prefixWord, tailWord_2076736, baseEnd_2076736] using wordTrace_append hprefix tailTrace_2076736
  have hstable : (prefixWord ++ tailWord_2076736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076736).length < 2 ^ (prefixWord ++ tailWord_2076736).sum := by decide
  have hdescent : baseEnd_2076736 < baseStart_2076736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076752 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 3, 9]
def baseStart_2076752 : Nat := 118140960795 + 2076752 * 2 ^ 59
def prefixEnd_2076752 : Nat := 4983230072969 + 3 ^ 40 * 2076752 * 2
def baseEnd_2076752 : Nat := 355457325395387977316399

theorem tailTrace_2076752 : CollatzResearch.WordTrace tailWord_2076752 prefixEnd_2076752 355457325395387977316399 := by
  unfold tailWord_2076752
  simp only [CollatzResearch.WordTrace]
  refine ⟨37872684086144829924556255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50496912114859773232741673 37872684086144829924556255)
  ·
    refine ⟨56809026129217244886834383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37872684086144829924556255 56809026129217244886834383)
    ·
      refine ⟨85213539193825867330251575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56809026129217244886834383 85213539193825867330251575)
      ·
        refine ⟨127820308790738800995377363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85213539193825867330251575 127820308790738800995377363)
        ·
          refine ⟨191730463186108201493066045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127820308790738800995377363 191730463186108201493066045)
          ·
            refine ⟨71898923694790575559899767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191730463186108201493066045 71898923694790575559899767)
            ·
              refine ⟨107848385542185863339849651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71898923694790575559899767 107848385542185863339849651)
              ·
                refine ⟨161772578313278795009774477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107848385542185863339849651 161772578313278795009774477)
                ·
                  refine ⟨60664716867479548128665429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161772578313278795009774477 60664716867479548128665429)
                  ·
                    refine ⟨355457325395387977316399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 60664716867479548128665429 355457325395387977316399)
                    ·
                      rfl

theorem cell23_2076752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_2076752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076752 prefixEnd_2076752 := by exact prefixLift 2076752
  have htrace : WordTrace (prefixWord ++ tailWord_2076752) baseStart_2076752 baseEnd_2076752 := by
    simpa [prefixWord, tailWord_2076752, baseEnd_2076752] using wordTrace_append hprefix tailTrace_2076752
  have hstable : (prefixWord ++ tailWord_2076752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076752).length < 2 ^ (prefixWord ++ tailWord_2076752).sum := by decide
  have hdescent : baseEnd_2076752 < baseStart_2076752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076783 : List Nat := [1, 1, 2, 1, 3, 5, 1, 3, 2, 1, 3]
def baseStart_2076783 : Nat := 118140960795 + 2076783 * 2 ^ 59
def prefixEnd_2076783 : Nat := 4983230072969 + 3 ^ 40 * 2076783 * 2
def baseEnd_2076783 : Nat := 1066387894086453310661555

theorem tailTrace_2076783 : CollatzResearch.WordTrace tailWord_2076783 prefixEnd_2076783 1066387894086453310661555 := by
  unfold tailWord_2076783
  simp only [CollatzResearch.WordTrace]
  refine ⟨75746498835177352143491003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50497665890118234762327335 75746498835177352143491003)
  ·
    refine ⟨113619748252766028215236505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75746498835177352143491003 113619748252766028215236505)
    ·
      refine ⟨85214811189574521161427379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113619748252766028215236505 85214811189574521161427379)
      ·
        refine ⟨127822216784361781742141069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85214811189574521161427379 127822216784361781742141069)
        ·
          refine ⟨47933331294135668153302901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127822216784361781742141069 47933331294135668153302901)
          ·
            refine ⟨4493749808825218889372147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47933331294135668153302901 4493749808825218889372147)
            ·
              refine ⟨6740624713237828334058221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4493749808825218889372147 6740624713237828334058221)
              ·
                refine ⟨2527734267464185625271833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6740624713237828334058221 2527734267464185625271833)
                ·
                  refine ⟨1895800700598139218953875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2527734267464185625271833 1895800700598139218953875)
                  ·
                    refine ⟨2843701050897208828430813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1895800700598139218953875 2843701050897208828430813)
                    ·
                      refine ⟨1066387894086453310661555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2843701050897208828430813 1066387894086453310661555)
                      ·
                        rfl

theorem cell23_2076783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 1, 3].length) (baseStart_2076783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076783 prefixEnd_2076783 := by exact prefixLift 2076783
  have htrace : WordTrace (prefixWord ++ tailWord_2076783) baseStart_2076783 baseEnd_2076783 := by
    simpa [prefixWord, tailWord_2076783, baseEnd_2076783] using wordTrace_append hprefix tailTrace_2076783
  have hstable : (prefixWord ++ tailWord_2076783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076783).length < 2 ^ (prefixWord ++ tailWord_2076783).sum := by decide
  have hdescent : baseEnd_2076783 < baseStart_2076783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076793 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 3, 3, 2]
def baseStart_2076793 : Nat := 118140960795 + 2076793 * 2 ^ 59
def prefixEnd_2076793 : Nat := 4983230072969 + 3 ^ 40 * 2076793 * 2
def baseEnd_2076793 : Nat := 1066393028892998271536509

theorem tailTrace_2076793 : CollatzResearch.WordTrace tailWord_2076793 prefixEnd_2076793 1066393028892998271536509 := by
  unfold tailWord_2076793
  simp only [CollatzResearch.WordTrace]
  refine ⟨75746863565141123851355033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50497909043427415900903355 75746863565141123851355033)
  ·
    refine ⟨56810147673855842888516275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75746863565141123851355033 56810147673855842888516275)
    ·
      refine ⟨85215221510783764332774413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56810147673855842888516275 85215221510783764332774413)
      ·
        refine ⟨31955708066543911624790405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85215221510783764332774413 31955708066543911624790405)
        ·
          refine ⟨5991695262476983429648201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31955708066543911624790405 5991695262476983429648201)
          ·
            refine ⟨4493771446857737572236151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5991695262476983429648201 4493771446857737572236151)
            ·
              refine ⟨6740657170286606358354227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4493771446857737572236151 6740657170286606358354227)
              ·
                refine ⟨10110985755429909537531341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6740657170286606358354227 10110985755429909537531341)
                ·
                  refine ⟨3791619658286216076574253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10110985755429909537531341 3791619658286216076574253)
                  ·
                    refine ⟨1421857371857331028715345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3791619658286216076574253 1421857371857331028715345)
                    ·
                      refine ⟨1066393028892998271536509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421857371857331028715345 1066393028892998271536509)
                      ·
                        rfl

theorem cell23_2076793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_2076793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076793 prefixEnd_2076793 := by exact prefixLift 2076793
  have htrace : WordTrace (prefixWord ++ tailWord_2076793) baseStart_2076793 baseEnd_2076793 := by
    simpa [prefixWord, tailWord_2076793, baseEnd_2076793] using wordTrace_append hprefix tailTrace_2076793
  have hstable : (prefixWord ++ tailWord_2076793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076793).length < 2 ^ (prefixWord ++ tailWord_2076793).sum := by decide
  have hdescent : baseEnd_2076793 < baseStart_2076793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076809 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 5]
def baseStart_2076809 : Nat := 118140960795 + 2076809 * 2 ^ 59
def prefixEnd_2076809 : Nat := 4983230072969 + 3 ^ 40 * 2076809 * 2
def baseEnd_2076809 : Nat := 1066401244583470208936435

theorem tailTrace_2076809 : CollatzResearch.WordTrace tailWord_2076809 prefixEnd_2076809 1066401244583470208936435 := by
  unfold tailWord_2076809
  simp only [CollatzResearch.WordTrace]
  refine ⟨75747447133083158583937481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50498298088722105722624987 75747447133083158583937481)
  ·
    refine ⟨56810585349812368937953111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75747447133083158583937481 56810585349812368937953111)
    ·
      refine ⟨85215878024718553406929667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56810585349812368937953111 85215878024718553406929667)
      ·
        refine ⟨127823817037077830110394501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85215878024718553406929667 127823817037077830110394501)
        ·
          refine ⟨23966965694452093145698969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127823817037077830110394501 23966965694452093145698969)
          ·
            refine ⟨17975224270839069859274227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23966965694452093145698969 17975224270839069859274227)
            ·
              refine ⟨26962836406258604788911341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17975224270839069859274227 26962836406258604788911341)
              ·
                refine ⟨10111063652346976795841753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26962836406258604788911341 10111063652346976795841753)
                ·
                  refine ⟨7583297739260232596881315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10111063652346976795841753 7583297739260232596881315)
                  ·
                    refine ⟨11374946608890348895321973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7583297739260232596881315 11374946608890348895321973)
                    ·
                      refine ⟨1066401244583470208936435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11374946608890348895321973 1066401244583470208936435)
                      ·
                        rfl

theorem cell23_2076809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_2076809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076809 prefixEnd_2076809 := by exact prefixLift 2076809
  have htrace : WordTrace (prefixWord ++ tailWord_2076809) baseStart_2076809 baseEnd_2076809 := by
    simpa [prefixWord, tailWord_2076809, baseEnd_2076809] using wordTrace_append hprefix tailTrace_2076809
  have hstable : (prefixWord ++ tailWord_2076809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076809).length < 2 ^ (prefixWord ++ tailWord_2076809).sum := by decide
  have hdescent : baseEnd_2076809 < baseStart_2076809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076819 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 4]
def baseStart_2076819 : Nat := 118140960795 + 2076819 * 2 ^ 59
def prefixEnd_2076819 : Nat := 4983230072969 + 3 ^ 40 * 2076819 * 2
def baseEnd_2076819 : Nat := 1066406379390015169811389

theorem tailTrace_2076819 : CollatzResearch.WordTrace tailWord_2076819 prefixEnd_2076819 1066406379390015169811389 := by
  unfold tailWord_2076819
  simp only [CollatzResearch.WordTrace]
  refine ⟨75747811863046930291801511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50498541242031286861201007 75747811863046930291801511)
  ·
    refine ⟨113621717794570395437702267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75747811863046930291801511 113621717794570395437702267)
    ·
      refine ⟨170432576691855593156553401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113621717794570395437702267 170432576691855593156553401)
      ·
        refine ⟨127824432518891694867415051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170432576691855593156553401 127824432518891694867415051)
        ·
          refine ⟨191736648778337542301122577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127824432518891694867415051 191736648778337542301122577)
          ·
            refine ⟨143802486583753156725841933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191736648778337542301122577 143802486583753156725841933)
            ·
              refine ⟨53925932468907433772190725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143802486583753156725841933 53925932468907433772190725)
              ·
                refine ⟨10111112337920143832285761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53925932468907433772190725 10111112337920143832285761)
                ·
                  refine ⟨7583334253440107874214321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10111112337920143832285761 7583334253440107874214321)
                  ·
                    refine ⟨5687500690080080905660741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7583334253440107874214321 5687500690080080905660741)
                    ·
                      refine ⟨1066406379390015169811389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5687500690080080905660741 1066406379390015169811389)
                      ·
                        rfl

theorem cell23_2076819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_2076819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076819 prefixEnd_2076819 := by exact prefixLift 2076819
  have htrace : WordTrace (prefixWord ++ tailWord_2076819) baseStart_2076819 baseEnd_2076819 := by
    simpa [prefixWord, tailWord_2076819, baseEnd_2076819] using wordTrace_append hprefix tailTrace_2076819
  have hstable : (prefixWord ++ tailWord_2076819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076819).length < 2 ^ (prefixWord ++ tailWord_2076819).sum := by decide
  have hdescent : baseEnd_2076819 < baseStart_2076819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076859 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 1, 7]
def baseStart_2076859 : Nat := 118140960795 + 2076859 * 2 ^ 59
def prefixEnd_2076859 : Nat := 4983230072969 + 3 ^ 40 * 2076859 * 2
def baseEnd_2076859 : Nat := 355475639538731671103735

theorem tailTrace_2076859 : CollatzResearch.WordTrace tailWord_2076859 prefixEnd_2076859 355475639538731671103735 := by
  unfold tailWord_2076859
  simp only [CollatzResearch.WordTrace]
  refine ⟨75749270782902017123257631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50499513855268011415505087 75749270782902017123257631)
  ·
    refine ⟨113623906174353025684886447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75749270782902017123257631 113623906174353025684886447)
    ·
      refine ⟨170435859261529538527329671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113623906174353025684886447 170435859261529538527329671)
      ·
        refine ⟨255653788892294307790994507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170435859261529538527329671 255653788892294307790994507)
        ·
          refine ⟨383480683338441461686491761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255653788892294307790994507 383480683338441461686491761)
          ·
            refine ⟨287610512503831096264868821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383480683338441461686491761 287610512503831096264868821)
            ·
              refine ⟨6740871386808541318707863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 287610512503831096264868821 6740871386808541318707863)
              ·
                refine ⟨10111307080212811978061795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6740871386808541318707863 10111307080212811978061795)
                ·
                  refine ⟨15166960620319217967092693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10111307080212811978061795 15166960620319217967092693)
                  ·
                    refine ⟨355475639538731671103735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15166960620319217967092693 355475639538731671103735)
                    ·
                      rfl

theorem cell23_2076859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 7].length) (baseStart_2076859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076859 prefixEnd_2076859 := by exact prefixLift 2076859
  have htrace : WordTrace (prefixWord ++ tailWord_2076859) baseStart_2076859 baseEnd_2076859 := by
    simpa [prefixWord, tailWord_2076859, baseEnd_2076859] using wordTrace_append hprefix tailTrace_2076859
  have hstable : (prefixWord ++ tailWord_2076859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076859).length < 2 ^ (prefixWord ++ tailWord_2076859).sum := by decide
  have hdescent : baseEnd_2076859 < baseStart_2076859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076869 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_2076869 : Nat := 118140960795 + 2076869 * 2 ^ 59
def prefixEnd_2076869 : Nat := 4983230072969 + 3 ^ 40 * 2076869 * 2
def baseEnd_2076869 : Nat := 1066432053422739974186159

theorem tailTrace_2076869 : CollatzResearch.WordTrace tailWord_2076869 prefixEnd_2076869 1066432053422739974186159 := by
  unfold tailWord_2076869
  simp only [CollatzResearch.WordTrace]
  refine ⟨75749635512865788831121661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50499757008577192554081107 75749635512865788831121661)
  ·
    refine ⟨28406113317324670811670623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75749635512865788831121661 28406113317324670811670623)
    ·
      refine ⟨42609169975987006217505935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28406113317324670811670623 42609169975987006217505935)
      ·
        refine ⟨63913754963980509326258903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42609169975987006217505935 63913754963980509326258903)
        ·
          refine ⟨95870632445970763989388355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63913754963980509326258903 95870632445970763989388355)
          ·
            refine ⟨143805948668956145984082533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95870632445970763989388355 143805948668956145984082533)
            ·
              refine ⟨26963615375429277372015475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143805948668956145984082533 26963615375429277372015475)
              ·
                refine ⟨40445423063143916058023213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26963615375429277372015475 40445423063143916058023213)
                ·
                  refine ⟨15167033648678968521758705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40445423063143916058023213 15167033648678968521758705)
                  ·
                    refine ⟨11375275236509226391319029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15167033648678968521758705 11375275236509226391319029)
                    ·
                      refine ⟨1066432053422739974186159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11375275236509226391319029 1066432053422739974186159)
                      ·
                        rfl

theorem cell23_2076869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_2076869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076869 prefixEnd_2076869 := by exact prefixLift 2076869
  have htrace : WordTrace (prefixWord ++ tailWord_2076869) baseStart_2076869 baseEnd_2076869 := by
    simpa [prefixWord, tailWord_2076869, baseEnd_2076869] using wordTrace_append hprefix tailTrace_2076869
  have hstable : (prefixWord ++ tailWord_2076869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076869).length < 2 ^ (prefixWord ++ tailWord_2076869).sum := by decide
  have hdescent : baseEnd_2076869 < baseStart_2076869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076930 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2076930 : Nat := 118140960795 + 2076930 * 2 ^ 59
def prefixEnd_2076930 : Nat := 4983230072969 + 3 ^ 40 * 2076930 * 2
def baseEnd_2076930 : Nat := 1066463375742664235523379

theorem tailTrace_2076930 : CollatzResearch.WordTrace tailWord_2076930 prefixEnd_2076930 1066463375742664235523379 := by
  unfold tailWord_2076930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18937965091411199062273061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50501240243763197499394829 18937965091411199062273061)
  ·
    refine ⟨3550868454639599824176199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18937965091411199062273061 3550868454639599824176199)
    ·
      refine ⟨5326302681959399736264299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3550868454639599824176199 5326302681959399736264299)
      ·
        refine ⟨7989454022939099604396449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5326302681959399736264299 7989454022939099604396449)
        ·
          refine ⟨5992090517204324703297337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7989454022939099604396449 5992090517204324703297337)
          ·
            refine ⟨4494067887903243527473003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5992090517204324703297337 4494067887903243527473003)
            ·
              refine ⟨6741101831854865291209505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4494067887903243527473003 6741101831854865291209505)
              ·
                refine ⟨5055826373891148968407129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6741101831854865291209505 5055826373891148968407129)
                ·
                  refine ⟨3791869780418361726305347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5055826373891148968407129 3791869780418361726305347)
                  ·
                    refine ⟨5687804670627542589458021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3791869780418361726305347 5687804670627542589458021)
                    ·
                      refine ⟨1066463375742664235523379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5687804670627542589458021 1066463375742664235523379)
                      ·
                        rfl

theorem cell23_2076930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2076930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076930 prefixEnd_2076930 := by exact prefixLift 2076930
  have htrace : WordTrace (prefixWord ++ tailWord_2076930) baseStart_2076930 baseEnd_2076930 := by
    simpa [prefixWord, tailWord_2076930, baseEnd_2076930] using wordTrace_append hprefix tailTrace_2076930
  have hstable : (prefixWord ++ tailWord_2076930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076930).length < 2 ^ (prefixWord ++ tailWord_2076930).sum := by decide
  have hdescent : baseEnd_2076930 < baseStart_2076930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076936 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 8]
def baseStart_2076936 : Nat := 118140960795 + 2076936 * 2 ^ 59
def prefixEnd_2076936 : Nat := 4983230072969 + 3 ^ 40 * 2076936 * 2
def baseEnd_2076936 : Nat := 118496272958510134672039

theorem tailTrace_2076936 : CollatzResearch.WordTrace tailWord_2076936 prefixEnd_2076936 118496272958510134672039 := by
  unfold tailWord_2076936
  simp only [CollatzResearch.WordTrace]
  refine ⟨37876039601811529636905331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50501386135748706182540441 37876039601811529636905331)
  ·
    refine ⟨56814059402717294455357997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37876039601811529636905331 56814059402717294455357997)
    ·
      refine ⟨21305272276018985420759249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56814059402717294455357997 21305272276018985420759249)
      ·
        refine ⟨15978954207014239065569437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21305272276018985420759249 15978954207014239065569437)
        ·
          refine ⟨5992107827630339649588539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15978954207014239065569437 5992107827630339649588539)
          ·
            refine ⟨8988161741445509474382809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5992107827630339649588539 8988161741445509474382809)
            ·
              refine ⟨6741121306084132105787107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8988161741445509474382809 6741121306084132105787107)
              ·
                refine ⟨10111681959126198158680661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741121306084132105787107 10111681959126198158680661)
                ·
                  refine ⟨118496272958510134672039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10111681959126198158680661 118496272958510134672039)
                  ·
                    rfl

theorem cell23_2076936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 8].length) (baseStart_2076936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076936 prefixEnd_2076936 := by exact prefixLift 2076936
  have htrace : WordTrace (prefixWord ++ tailWord_2076936) baseStart_2076936 baseEnd_2076936 := by
    simpa [prefixWord, tailWord_2076936, baseEnd_2076936] using wordTrace_append hprefix tailTrace_2076936
  have hstable : (prefixWord ++ tailWord_2076936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076936).length < 2 ^ (prefixWord ++ tailWord_2076936).sum := by decide
  have hdescent : baseEnd_2076936 < baseStart_2076936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076963 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 5, 1, 3]
def baseStart_2076963 : Nat := 118140960795 + 2076963 * 2 ^ 59
def prefixEnd_2076963 : Nat := 4983230072969 + 3 ^ 40 * 2076963 * 2
def baseEnd_2076963 : Nat := 1066480320604262606410727

theorem tailTrace_2076963 : CollatzResearch.WordTrace tailWord_2076963 prefixEnd_2076963 1066480320604262606410727 := by
  unfold tailWord_2076963
  simp only [CollatzResearch.WordTrace]
  refine ⟨75753063974525242885043543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50502042649683495256695695 75753063974525242885043543)
  ·
    refine ⟨113629595961787864327565315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75753063974525242885043543 113629595961787864327565315)
    ·
      refine ⟨170444393942681796491347973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113629595961787864327565315 170444393942681796491347973)
      ·
        refine ⟨31958323864252836842127745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170444393942681796491347973 31958323864252836842127745)
        ·
          refine ⟨23968742898189627631595809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31958323864252836842127745 23968742898189627631595809)
          ·
            refine ⟨17976557173642220723696857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23968742898189627631595809 17976557173642220723696857)
            ·
              refine ⟨13482417880231665542772643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17976557173642220723696857 13482417880231665542772643)
              ·
                refine ⟨20223626820347498314158965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13482417880231665542772643 20223626820347498314158965)
                ·
                  refine ⟨1895965014407577966952403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20223626820347498314158965 1895965014407577966952403)
                  ·
                    refine ⟨2843947521611366950428605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1895965014407577966952403 2843947521611366950428605)
                    ·
                      refine ⟨1066480320604262606410727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2843947521611366950428605 1066480320604262606410727)
                      ·
                        rfl

theorem cell23_2076963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_2076963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076963 prefixEnd_2076963 := by exact prefixLift 2076963
  have htrace : WordTrace (prefixWord ++ tailWord_2076963) baseStart_2076963 baseEnd_2076963 := by
    simpa [prefixWord, tailWord_2076963, baseEnd_2076963] using wordTrace_append hprefix tailTrace_2076963
  have hstable : (prefixWord ++ tailWord_2076963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076963).length < 2 ^ (prefixWord ++ tailWord_2076963).sum := by decide
  have hdescent : baseEnd_2076963 < baseStart_2076963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077023 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 3]
def baseStart_2077023 : Nat := 118140960795 + 2077023 * 2 ^ 59
def prefixEnd_2077023 : Nat := 4983230072969 + 3 ^ 40 * 2077023 * 2
def baseEnd_2077023 : Nat := 1066511129443532371660451

theorem tailTrace_2077023 : CollatzResearch.WordTrace tailWord_2077023 prefixEnd_2077023 1066511129443532371660451 := by
  unfold tailWord_2077023
  simp only [CollatzResearch.WordTrace]
  refine ⟨75755252354307873132227723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50503501569538582088151815 75755252354307873132227723)
  ·
    refine ⟨113632878531461809698341585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75755252354307873132227723 113632878531461809698341585)
    ·
      refine ⟨85224658898596357273756189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113632878531461809698341585 85224658898596357273756189)
      ·
        refine ⟨31959247086973633977658571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85224658898596357273756189 31959247086973633977658571)
        ·
          refine ⟨47938870630460450966487857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31959247086973633977658571 47938870630460450966487857)
          ·
            refine ⟨35954152972845338224865893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47938870630460450966487857 35954152972845338224865893)
            ·
              refine ⟨6741403682408500917162355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35954152972845338224865893 6741403682408500917162355)
              ·
                refine ⟨10112105523612751375743533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741403682408500917162355 10112105523612751375743533)
                ·
                  refine ⟨3792039571354781765903825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10112105523612751375743533 3792039571354781765903825)
                  ·
                    refine ⟨2844029678516086324427869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3792039571354781765903825 2844029678516086324427869)
                    ·
                      refine ⟨1066511129443532371660451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2844029678516086324427869 1066511129443532371660451)
                      ·
                        rfl

theorem cell23_2077023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_2077023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077023 prefixEnd_2077023 := by exact prefixLift 2077023
  have htrace : WordTrace (prefixWord ++ tailWord_2077023) baseStart_2077023 baseEnd_2077023 := by
    simpa [prefixWord, tailWord_2077023, baseEnd_2077023] using wordTrace_append hprefix tailTrace_2077023
  have hstable : (prefixWord ++ tailWord_2077023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077023).length < 2 ^ (prefixWord ++ tailWord_2077023).sum := by decide
  have hdescent : baseEnd_2077023 < baseStart_2077023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077024 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 2, 3, 2]
def baseStart_2077024 : Nat := 118140960795 + 2077024 * 2 ^ 59
def prefixEnd_2077024 : Nat := 4983230072969 + 3 ^ 40 * 2077024 * 2
def baseEnd_2077024 : Nat := 1066511642924186867747947

theorem tailTrace_2077024 : CollatzResearch.WordTrace tailWord_2077024 prefixEnd_2077024 1066511642924186867747947 := by
  unfold tailWord_2077024
  simp only [CollatzResearch.WordTrace]
  refine ⟨37877644413652125151507063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50503525884869500202009417 37877644413652125151507063)
  ·
    refine ⟨56816466620478187727260595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37877644413652125151507063 56816466620478187727260595)
    ·
      refine ⟨85224699930717281590890893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56816466620478187727260595 85224699930717281590890893)
      ·
        refine ⟨31959262474018980596584085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85224699930717281590890893 31959262474018980596584085)
        ·
          refine ⟨1498090428469639715464879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31959262474018980596584085 1498090428469639715464879)
          ·
            refine ⟨2247135642704459573197319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498090428469639715464879 2247135642704459573197319)
            ·
              refine ⟨3370703464056689359795979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2247135642704459573197319 3370703464056689359795979)
              ·
                refine ⟨5056055196085034039693969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3370703464056689359795979 5056055196085034039693969)
                ·
                  refine ⟨3792041397063775529770477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5056055196085034039693969 3792041397063775529770477)
                  ·
                    refine ⟨1422015523898915823663929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3792041397063775529770477 1422015523898915823663929)
                    ·
                      refine ⟨1066511642924186867747947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1422015523898915823663929 1066511642924186867747947)
                      ·
                        rfl

theorem cell23_2077024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_2077024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077024 prefixEnd_2077024 := by exact prefixLift 2077024
  have htrace : WordTrace (prefixWord ++ tailWord_2077024) baseStart_2077024 baseEnd_2077024 := by
    simpa [prefixWord, tailWord_2077024, baseEnd_2077024] using wordTrace_append hprefix tailTrace_2077024
  have hstable : (prefixWord ++ tailWord_2077024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077024).length < 2 ^ (prefixWord ++ tailWord_2077024).sum := by decide
  have hdescent : baseEnd_2077024 < baseStart_2077024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077040 : List Nat := [2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 3]
def baseStart_2077040 : Nat := 118140960795 + 2077040 * 2 ^ 59
def prefixEnd_2077040 : Nat := 4983230072969 + 3 ^ 40 * 2077040 * 2
def baseEnd_2077040 : Nat := 1066519858614658805147873

theorem tailTrace_2077040 : CollatzResearch.WordTrace tailWord_2077040 prefixEnd_2077040 1066519858614658805147873 := by
  unfold tailWord_2077040
  simp only [CollatzResearch.WordTrace]
  refine ⟨37877936197623142517798287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50503914930164190023731049 37877936197623142517798287)
  ·
    refine ⟨56816904296434713776697431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37877936197623142517798287 56816904296434713776697431)
    ·
      refine ⟨85225356444652070665046147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56816904296434713776697431 85225356444652070665046147)
      ·
        refine ⟨127838034666978105997569221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85225356444652070665046147 127838034666978105997569221)
        ·
          refine ⟨23969631500058394874544229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127838034666978105997569221 23969631500058394874544229)
          ·
            refine ⟨4494305906260949038977043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23969631500058394874544229 4494305906260949038977043)
            ·
              refine ⟨6741458859391423558465565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4494305906260949038977043 6741458859391423558465565)
              ·
                refine ⟨2528047072271783834424587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6741458859391423558465565 2528047072271783834424587)
                ·
                  refine ⟨3792070608407675751636881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528047072271783834424587 3792070608407675751636881)
                  ·
                    refine ⟨2844052956305756813727661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3792070608407675751636881 2844052956305756813727661)
                    ·
                      refine ⟨1066519858614658805147873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2844052956305756813727661 1066519858614658805147873)
                      ·
                        rfl

theorem cell23_2077040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 3].length) (baseStart_2077040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077040 prefixEnd_2077040 := by exact prefixLift 2077040
  have htrace : WordTrace (prefixWord ++ tailWord_2077040) baseStart_2077040 baseEnd_2077040 := by
    simpa [prefixWord, tailWord_2077040, baseEnd_2077040] using wordTrace_append hprefix tailTrace_2077040
  have hstable : (prefixWord ++ tailWord_2077040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077040).length < 2 ^ (prefixWord ++ tailWord_2077040).sum := by decide
  have hdescent : baseEnd_2077040 < baseStart_2077040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077143 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 3]
def baseStart_2077143 : Nat := 118140960795 + 2077143 * 2 ^ 59
def prefixEnd_2077143 : Nat := 4983230072969 + 3 ^ 40 * 2077143 * 2
def baseEnd_2077143 : Nat := 1066572747122071902159899

theorem tailTrace_2077143 : CollatzResearch.WordTrace tailWord_2077143 prefixEnd_2077143 1066572747122071902159899 := by
  unfold tailWord_2077143
  simp only [CollatzResearch.WordTrace]
  refine ⟨75759629113873133626596083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50506419409248755751064055 75759629113873133626596083)
  ·
    refine ⟨113639443670809700439894125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75759629113873133626596083 113639443670809700439894125)
    ·
      refine ⟨42614791376553637664960297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113639443670809700439894125 42614791376553637664960297)
      ·
        refine ⟨31961093532415228248720223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42614791376553637664960297 31961093532415228248720223)
        ·
          refine ⟨47941640298622842373080335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31961093532415228248720223 47941640298622842373080335)
          ·
            refine ⟨71912460447934263559620503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47941640298622842373080335 71912460447934263559620503)
            ·
              refine ⟨107868690671901395339430755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71912460447934263559620503 107868690671901395339430755)
              ·
                refine ⟨161803036007852093009146133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107868690671901395339430755 161803036007852093009146133)
                ·
                  refine ⟨7584517312868066859803725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161803036007852093009146133 7584517312868066859803725)
                  ·
                    refine ⟨2844193992325525072426397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7584517312868066859803725 2844193992325525072426397)
                    ·
                      refine ⟨1066572747122071902159899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2844193992325525072426397 1066572747122071902159899)
                      ·
                        rfl

theorem cell23_2077143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_2077143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077143 prefixEnd_2077143 := by exact prefixLift 2077143
  have htrace : WordTrace (prefixWord ++ tailWord_2077143) baseStart_2077143 baseEnd_2077143 := by
    simpa [prefixWord, tailWord_2077143, baseEnd_2077143] using wordTrace_append hprefix tailTrace_2077143
  have hstable : (prefixWord ++ tailWord_2077143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077143).length < 2 ^ (prefixWord ++ tailWord_2077143).sum := by decide
  have hdescent : baseEnd_2077143 < baseStart_2077143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077163 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 2, 5]
def baseStart_2077163 : Nat := 118140960795 + 2077163 * 2 ^ 59
def prefixEnd_2077163 : Nat := 4983230072969 + 3 ^ 40 * 2077163 * 2
def baseEnd_2077163 : Nat := 355527672245053941303269

theorem tailTrace_2077163 : CollatzResearch.WordTrace tailWord_2077163 prefixEnd_2077163 355527672245053941303269 := by
  unfold tailWord_2077163
  simp only [CollatzResearch.WordTrace]
  refine ⟨75760358573800677042324143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50506905715867118028216095 75760358573800677042324143)
  ·
    refine ⟨113640537860701015563486215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75760358573800677042324143 113640537860701015563486215)
    ·
      refine ⟨170460806791051523345229323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113640537860701015563486215 170460806791051523345229323)
      ·
        refine ⟨255691210186577285017843985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170460806791051523345229323 255691210186577285017843985)
        ·
          refine ⟨191768407639932963763382989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255691210186577285017843985 191768407639932963763382989)
          ·
            refine ⟨71913152864974861411268621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191768407639932963763382989 71913152864974861411268621)
            ·
              refine ⟨26967432324365573029225733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71913152864974861411268621 26967432324365573029225733)
              ·
                refine ⟨5056393560818544942979825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26967432324365573029225733 5056393560818544942979825)
                ·
                  refine ⟨3792295170613908707234869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5056393560818544942979825 3792295170613908707234869)
                  ·
                    refine ⟨355527672245053941303269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3792295170613908707234869 355527672245053941303269)
                    ·
                      rfl

theorem cell23_2077163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 5].length) (baseStart_2077163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077163 prefixEnd_2077163 := by exact prefixLift 2077163
  have htrace : WordTrace (prefixWord ++ tailWord_2077163) baseStart_2077163 baseEnd_2077163 := by
    simpa [prefixWord, tailWord_2077163, baseEnd_2077163] using wordTrace_append hprefix tailTrace_2077163
  have hstable : (prefixWord ++ tailWord_2077163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077163).length < 2 ^ (prefixWord ++ tailWord_2077163).sum := by decide
  have hdescent : baseEnd_2077163 < baseStart_2077163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077183 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 4]
def baseStart_2077183 : Nat := 118140960795 + 2077183 * 2 ^ 59
def prefixEnd_2077183 : Nat := 4983230072969 + 3 ^ 40 * 2077183 * 2
def baseEnd_2077183 : Nat := 1066593286348251745659715

theorem tailTrace_2077183 : CollatzResearch.WordTrace tailWord_2077183 prefixEnd_2077183 1066593286348251745659715 := by
  unfold tailWord_2077183
  simp only [CollatzResearch.WordTrace]
  refine ⟨75761088033728220458052203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50507392022485480305368135 75761088033728220458052203)
  ·
    refine ⟨113641632050592330687078305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75761088033728220458052203 113641632050592330687078305)
    ·
      refine ⟨85231224037944248015308729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113641632050592330687078305 85231224037944248015308729)
      ·
        refine ⟨63923418028458186011481547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85231224037944248015308729 63923418028458186011481547)
        ·
          refine ⟨95885127042687279017222321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63923418028458186011481547 95885127042687279017222321)
          ·
            refine ⟨71913845282015459262916741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95885127042687279017222321 71913845282015459262916741)
            ·
              refine ⟨13483845990377898611796889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71913845282015459262916741 13483845990377898611796889)
              ·
                refine ⟨10112884492783423958847667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13483845990377898611796889 10112884492783423958847667)
                ·
                  refine ⟨15169326739175135938271501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10112884492783423958847667 15169326739175135938271501)
                  ·
                    refine ⟨5688497527190675976851813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15169326739175135938271501 5688497527190675976851813)
                    ·
                      refine ⟨1066593286348251745659715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5688497527190675976851813 1066593286348251745659715)
                      ·
                        rfl

theorem cell23_2077183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_2077183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077183 prefixEnd_2077183 := by exact prefixLift 2077183
  have htrace : WordTrace (prefixWord ++ tailWord_2077183) baseStart_2077183 baseEnd_2077183 := by
    simpa [prefixWord, tailWord_2077183, baseEnd_2077183] using wordTrace_append hprefix tailTrace_2077183
  have hstable : (prefixWord ++ tailWord_2077183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077183).length < 2 ^ (prefixWord ++ tailWord_2077183).sum := by decide
  have hdescent : baseEnd_2077183 < baseStart_2077183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077254 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_2077254 : Nat := 118140960795 + 2077254 * 2 ^ 59
def prefixEnd_2077254 : Nat := 4983230072969 + 3 ^ 40 * 2077254 * 2
def baseEnd_2077254 : Nat := 1066629743474720967871889

theorem tailTrace_2077254 : CollatzResearch.WordTrace tailWord_2077254 prefixEnd_2077254 1066629743474720967871889 := by
  unfold tailWord_2077254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2367614925514718736996463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50509118410980666389257877 2367614925514718736996463)
  ·
    refine ⟨3551422388272078105494695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2367614925514718736996463 3551422388272078105494695)
    ·
      refine ⟨5327133582408117158242043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3551422388272078105494695 5327133582408117158242043)
      ·
        refine ⟨7990700373612175737363065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327133582408117158242043 7990700373612175737363065)
        ·
          refine ⟨5993025280209131803022299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7990700373612175737363065 5993025280209131803022299)
          ·
            refine ⟨8989537920313697704533449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5993025280209131803022299 8989537920313697704533449)
            ·
              refine ⟨6742153440235273278400087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8989537920313697704533449 6742153440235273278400087)
              ·
                refine ⟨10113230160352909917600131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6742153440235273278400087 10113230160352909917600131)
                ·
                  refine ⟨15169845240529364876400197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10113230160352909917600131 15169845240529364876400197)
                  ·
                    refine ⟨2844345982599255914325037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15169845240529364876400197 2844345982599255914325037)
                    ·
                      refine ⟨1066629743474720967871889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2844345982599255914325037 1066629743474720967871889)
                      ·
                        rfl

theorem cell23_2077254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_2077254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077254 prefixEnd_2077254 := by exact prefixLift 2077254
  have htrace : WordTrace (prefixWord ++ tailWord_2077254) baseStart_2077254 baseEnd_2077254 := by
    simpa [prefixWord, tailWord_2077254, baseEnd_2077254] using wordTrace_append hprefix tailTrace_2077254
  have hstable : (prefixWord ++ tailWord_2077254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077254).length < 2 ^ (prefixWord ++ tailWord_2077254).sum := by decide
  have hdescent : baseEnd_2077254 < baseStart_2077254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077261 : List Nat := [1, 6, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_2077261 : Nat := 118140960795 + 2077261 * 2 ^ 59
def prefixEnd_2077261 : Nat := 4983230072969 + 3 ^ 40 * 2077261 * 2
def baseEnd_2077261 : Nat := 355544445946434146828119

theorem tailTrace_2077261 : CollatzResearch.WordTrace tailWord_2077261 prefixEnd_2077261 355544445946434146828119 := by
  unfold tailWord_2077261
  simp only [CollatzResearch.WordTrace]
  refine ⟨75763932927445639779391637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50509288618297093186261091 75763932927445639779391637)
  ·
    refine ⟨3551434355974014364658983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75763932927445639779391637 3551434355974014364658983)
    ·
      refine ⟨5327151533961021546988475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3551434355974014364658983 5327151533961021546988475)
      ·
        refine ⟨7990727300941532320482713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327151533961021546988475 7990727300941532320482713)
        ·
          refine ⟨5993045475706149240362035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7990727300941532320482713 5993045475706149240362035)
          ·
            refine ⟨8989568213559223860543053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5993045475706149240362035 8989568213559223860543053)
            ·
              refine ⟨3371088080084708947703645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8989568213559223860543053 3371088080084708947703645)
              ·
                refine ⟨1264158030031765855388867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3371088080084708947703645 1264158030031765855388867)
                ·
                  refine ⟨1896237045047648783083301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264158030031765855388867 1896237045047648783083301)
                  ·
                    refine ⟨355544445946434146828119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1896237045047648783083301 355544445946434146828119)
                    ·
                      rfl

theorem cell23_2077261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_2077261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077261 prefixEnd_2077261 := by exact prefixLift 2077261
  have htrace : WordTrace (prefixWord ++ tailWord_2077261) baseStart_2077261 baseEnd_2077261 := by
    simpa [prefixWord, tailWord_2077261, baseEnd_2077261] using wordTrace_append hprefix tailTrace_2077261
  have hstable : (prefixWord ++ tailWord_2077261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077261).length < 2 ^ (prefixWord ++ tailWord_2077261).sum := by decide
  have hdescent : baseEnd_2077261 < baseStart_2077261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077330 : List Nat := [3, 2, 3, 1, 2, 12]
def baseStart_2077330 : Nat := 118140960795 + 2077330 * 2 ^ 59
def prefixEnd_2077330 : Nat := 4983230072969 + 3 ^ 40 * 2077330 * 2
def baseEnd_2077330 : Nat := 4389583407425772306673

theorem tailTrace_2077330 : CollatzResearch.WordTrace tailWord_2077330 prefixEnd_2077330 4389583407425772306673 := by
  unfold tailWord_2077330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18941612391048916140913361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50510966376130443042435629 18941612391048916140913361)
  ·
    refine ⟨14206209293286687105685021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18941612391048916140913361 14206209293286687105685021)
    ·
      refine ⟨5327328484982507664631883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14206209293286687105685021 5327328484982507664631883)
      ·
        refine ⟨7990992727473761496947825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327328484982507664631883 7990992727473761496947825)
        ·
          refine ⟨5993244545605321122710869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7990992727473761496947825 5993244545605321122710869)
          ·
            refine ⟨4389583407425772306673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5993244545605321122710869 4389583407425772306673)
            ·
              rfl

theorem cell23_2077330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 12].length) (baseStart_2077330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077330 prefixEnd_2077330 := by exact prefixLift 2077330
  have htrace : WordTrace (prefixWord ++ tailWord_2077330) baseStart_2077330 baseEnd_2077330 := by
    simpa [prefixWord, tailWord_2077330, baseEnd_2077330] using wordTrace_append hprefix tailTrace_2077330
  have hstable : (prefixWord ++ tailWord_2077330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077330).length < 2 ^ (prefixWord ++ tailWord_2077330).sum := by decide
  have hdescent : baseEnd_2077330 < baseStart_2077330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077358 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_2077358 : Nat := 118140960795 + 2077358 * 2 ^ 59
def prefixEnd_2077358 : Nat := 4983230072969 + 3 ^ 40 * 2077358 * 2
def baseEnd_2077358 : Nat := 1066683145462788560971411

theorem tailTrace_2077358 : CollatzResearch.WordTrace tailWord_2077358 prefixEnd_2077358 1066683145462788560971411 := by
  unfold tailWord_2077358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9470933851011778168209091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50511647205396150230448485 9470933851011778168209091)
  ·
    refine ⟨14206400776517667252313637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9470933851011778168209091 14206400776517667252313637)
    ·
      refine ⟨2663700145597062609808807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14206400776517667252313637 2663700145597062609808807)
      ·
        refine ⟨3995550218395593914713211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663700145597062609808807 3995550218395593914713211)
        ·
          refine ⟨5993325327593390872069817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3995550218395593914713211 5993325327593390872069817)
          ·
            refine ⟨4494993995695043154052363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5993325327593390872069817 4494993995695043154052363)
            ·
              refine ⟨6742490993542564731078545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4494993995695043154052363 6742490993542564731078545)
              ·
                refine ⟨5056868245156923548308909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6742490993542564731078545 5056868245156923548308909)
                ·
                  refine ⟨1896325591933846330615841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5056868245156923548308909 1896325591933846330615841)
                  ·
                    refine ⟨1422244193950384747961881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1896325591933846330615841 1422244193950384747961881)
                    ·
                      refine ⟨1066683145462788560971411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1422244193950384747961881 1066683145462788560971411)
                      ·
                        rfl

theorem cell23_2077358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_2077358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077358 prefixEnd_2077358 := by exact prefixLift 2077358
  have htrace : WordTrace (prefixWord ++ tailWord_2077358) baseStart_2077358 baseEnd_2077358 := by
    simpa [prefixWord, tailWord_2077358, baseEnd_2077358] using wordTrace_append hprefix tailTrace_2077358
  have hstable : (prefixWord ++ tailWord_2077358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077358).length < 2 ^ (prefixWord ++ tailWord_2077358).sum := by decide
  have hdescent : baseEnd_2077358 < baseStart_2077358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077370 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_2077370 : Nat := 118140960795 + 2077370 * 2 ^ 59
def prefixEnd_2077370 : Nat := 4983230072969 + 3 ^ 40 * 2077370 * 2
def baseEnd_2077370 : Nat := 1066689307230642514021355

theorem tailTrace_2077370 : CollatzResearch.WordTrace tailWord_2077370 prefixEnd_2077370 1066689307230642514021355 := by
  unfold tailWord_2077370
  simp only [CollatzResearch.WordTrace]
  refine ⟨18941977121012687848777391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50511938989367167596739709 18941977121012687848777391)
  ·
    refine ⟨28412965681519031773166087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18941977121012687848777391 28412965681519031773166087)
    ·
      refine ⟨42619448522278547659749131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28412965681519031773166087 42619448522278547659749131)
      ·
        refine ⟨63929172783417821489623697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42619448522278547659749131 63929172783417821489623697)
        ·
          refine ⟨47946879587563366117217773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63929172783417821489623697 47946879587563366117217773)
          ·
            refine ⟨17980079845336262293956665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47946879587563366117217773 17980079845336262293956665)
            ·
              refine ⟨13485059884002196720467499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17980079845336262293956665 13485059884002196720467499)
              ·
                refine ⟨20227589826003295080701249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13485059884002196720467499 20227589826003295080701249)
                ·
                  refine ⟨15170692369502471310525937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20227589826003295080701249 15170692369502471310525937)
                  ·
                    refine ⟨11378019277126853482894453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15170692369502471310525937 11378019277126853482894453)
                    ·
                      refine ⟨1066689307230642514021355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11378019277126853482894453 1066689307230642514021355)
                      ·
                        rfl

theorem cell23_2077370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_2077370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077370 prefixEnd_2077370 := by exact prefixLift 2077370
  have htrace : WordTrace (prefixWord ++ tailWord_2077370) baseStart_2077370 baseEnd_2077370 := by
    simpa [prefixWord, tailWord_2077370, baseEnd_2077370] using wordTrace_append hprefix tailTrace_2077370
  have hstable : (prefixWord ++ tailWord_2077370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077370).length < 2 ^ (prefixWord ++ tailWord_2077370).sum := by decide
  have hdescent : baseEnd_2077370 < baseStart_2077370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077374 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_2077374 : Nat := 118140960795 + 2077374 * 2 ^ 59
def prefixEnd_2077374 : Nat := 4983230072969 + 3 ^ 40 * 2077374 * 2
def baseEnd_2077374 : Nat := 1066691361153260498371337

theorem tailTrace_2077374 : CollatzResearch.WordTrace tailWord_2077374 prefixEnd_2077374 1066691361153260498371337 := by
  unfold tailWord_2077374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9471006797004532509781897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50512036250690840052170117 9471006797004532509781897)
  ·
    refine ⟨7103255097753399382336423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9471006797004532509781897 7103255097753399382336423)
    ·
      refine ⟨10654882646630099073504635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7103255097753399382336423 10654882646630099073504635)
      ·
        refine ⟨15982323969945148610256953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10654882646630099073504635 15982323969945148610256953)
        ·
          refine ⟨11986742977458861457692715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15982323969945148610256953 11986742977458861457692715)
          ·
            refine ⟨17980114466188292186539073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11986742977458861457692715 17980114466188292186539073)
            ·
              refine ⟨13485085849641219139904305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17980114466188292186539073 13485085849641219139904305)
              ·
                refine ⟨10113814387230914354928229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13485085849641219139904305 10113814387230914354928229)
                ·
                  refine ⟨1896340197605796441549043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10113814387230914354928229 1896340197605796441549043)
                  ·
                    refine ⟨2844510296408694662323565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1896340197605796441549043 2844510296408694662323565)
                    ·
                      refine ⟨1066691361153260498371337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2844510296408694662323565 1066691361153260498371337)
                      ·
                        rfl

theorem cell23_2077374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_2077374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077374 prefixEnd_2077374 := by exact prefixLift 2077374
  have htrace : WordTrace (prefixWord ++ tailWord_2077374) baseStart_2077374 baseEnd_2077374 := by
    simpa [prefixWord, tailWord_2077374, baseEnd_2077374] using wordTrace_append hprefix tailTrace_2077374
  have hstable : (prefixWord ++ tailWord_2077374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077374).length < 2 ^ (prefixWord ++ tailWord_2077374).sum := by decide
  have hdescent : baseEnd_2077374 < baseStart_2077374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077505 : List Nat := [1, 2, 5, 3, 1, 2, 2, 2, 5]
def baseStart_2077505 : Nat := 118140960795 + 2077505 * 2 ^ 59
def prefixEnd_2077505 : Nat := 4983230072969 + 3 ^ 40 * 2077505 * 2
def baseEnd_2077505 : Nat := 118528736346555498425915

theorem tailTrace_2077505 : CollatzResearch.WordTrace tailWord_2077505 prefixEnd_2077505 118528736346555498425915 := by
  unfold tailWord_2077505
  simp only [CollatzResearch.WordTrace]
  refine ⟨75772832338561669451273969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50515221559041112967515979 75772832338561669451273969)
  ·
    refine ⟨56829624253921252088455477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75772832338561669451273969 56829624253921252088455477)
    ·
      refine ⟨5327777273805117383292701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56829624253921252088455477 5327777273805117383292701)
      ·
        refine ⟨1997916477676919018734763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5327777273805117383292701 1997916477676919018734763)
        ·
          refine ⟨2996874716515378528102145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997916477676919018734763 2996874716515378528102145)
          ·
            refine ⟨2247656037386533896076609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2996874716515378528102145 2247656037386533896076609)
            ·
              refine ⟨1685742028039900422057457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2247656037386533896076609 1685742028039900422057457)
              ·
                refine ⟨1264306521029925316543093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1685742028039900422057457 1264306521029925316543093)
                ·
                  refine ⟨118528736346555498425915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1264306521029925316543093 118528736346555498425915)
                  ·
                    rfl

theorem cell23_2077505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 5].length) (baseStart_2077505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077505 prefixEnd_2077505 := by exact prefixLift 2077505
  have htrace : WordTrace (prefixWord ++ tailWord_2077505) baseStart_2077505 baseEnd_2077505 := by
    simpa [prefixWord, tailWord_2077505, baseEnd_2077505] using wordTrace_append hprefix tailTrace_2077505
  have hstable : (prefixWord ++ tailWord_2077505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077505).length < 2 ^ (prefixWord ++ tailWord_2077505).sum := by decide
  have hdescent : baseEnd_2077505 < baseStart_2077505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077521 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 2, 4, 2]
def baseStart_2077521 : Nat := 118140960795 + 2077521 * 2 ^ 59
def prefixEnd_2077521 : Nat := 4983230072969 + 3 ^ 40 * 2077521 * 2
def baseEnd_2077521 : Nat := 1066766842809471423233161

theorem tailTrace_2077521 : CollatzResearch.WordTrace tailWord_2077521 prefixEnd_2077521 1066766842809471423233161 := by
  unfold tailWord_2077521
  simp only [CollatzResearch.WordTrace]
  refine ⟨75773415906503704183856417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50515610604335802789237611 75773415906503704183856417)
  ·
    refine ⟨56830061929877778137892313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75773415906503704183856417 56830061929877778137892313)
    ·
      refine ⟨42622546447408333603419235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56830061929877778137892313 42622546447408333603419235)
      ·
        refine ⟨63933819671112500405128853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42622546447408333603419235 63933819671112500405128853)
        ·
          refine ⟨2996897797083398456490415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63933819671112500405128853 2996897797083398456490415)
          ·
            refine ⟨4495346695625097684735623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996897797083398456490415 4495346695625097684735623)
            ·
              refine ⟨6743020043437646527103435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4495346695625097684735623 6743020043437646527103435)
              ·
                refine ⟨10114530065156469790655153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6743020043437646527103435 10114530065156469790655153)
                ·
                  refine ⟨7585897548867352342991365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10114530065156469790655153 7585897548867352342991365)
                  ·
                    refine ⟨1422355790412628564310881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7585897548867352342991365 1422355790412628564310881)
                    ·
                      refine ⟨1066766842809471423233161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1422355790412628564310881 1066766842809471423233161)
                      ·
                        rfl

theorem cell23_2077521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 4, 2].length) (baseStart_2077521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077521 prefixEnd_2077521 := by exact prefixLift 2077521
  have htrace : WordTrace (prefixWord ++ tailWord_2077521) baseStart_2077521 baseEnd_2077521 := by
    simpa [prefixWord, tailWord_2077521, baseEnd_2077521] using wordTrace_append hprefix tailTrace_2077521
  have hstable : (prefixWord ++ tailWord_2077521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077521).length < 2 ^ (prefixWord ++ tailWord_2077521).sum := by decide
  have hdescent : baseEnd_2077521 < baseStart_2077521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077537 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_2077537 : Nat := 118140960795 + 2077537 * 2 ^ 59
def prefixEnd_2077537 : Nat := 4983230072969 + 3 ^ 40 * 2077537 * 2
def baseEnd_2077537 : Nat := 1066775058499943360633087

theorem tailTrace_2077537 : CollatzResearch.WordTrace tailWord_2077537 prefixEnd_2077537 1066775058499943360633087 := by
  unfold tailWord_2077537
  simp only [CollatzResearch.WordTrace]
  refine ⟨75773999474445738916438865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50515999649630492610959243 75773999474445738916438865)
  ·
    refine ⟨56830499605834304187329149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75773999474445738916438865 56830499605834304187329149)
    ·
      refine ⟨21311437352187864070248431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56830499605834304187329149 21311437352187864070248431)
      ·
        refine ⟨31967156028281796105372647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21311437352187864070248431 31967156028281796105372647)
        ·
          refine ⟨47950734042422694158058971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31967156028281796105372647 47950734042422694158058971)
          ·
            refine ⟨71926101063634041237088457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47950734042422694158058971 71926101063634041237088457)
            ·
              refine ⟨53944575797725530927816343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71926101063634041237088457 53944575797725530927816343)
              ·
                refine ⟨80916863696588296391724515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53944575797725530927816343 80916863696588296391724515)
                ·
                  refine ⟨121375295544882444587586773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80916863696588296391724515 121375295544882444587586773)
                  ·
                    refine ⟨2844733489333182295021565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 121375295544882444587586773 2844733489333182295021565)
                    ·
                      refine ⟨1066775058499943360633087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2844733489333182295021565 1066775058499943360633087)
                      ·
                        rfl

theorem cell23_2077537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_2077537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077537 prefixEnd_2077537 := by exact prefixLift 2077537
  have htrace : WordTrace (prefixWord ++ tailWord_2077537) baseStart_2077537 baseEnd_2077537 := by
    simpa [prefixWord, tailWord_2077537, baseEnd_2077537] using wordTrace_append hprefix tailTrace_2077537
  have hstable : (prefixWord ++ tailWord_2077537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077537).length < 2 ^ (prefixWord ++ tailWord_2077537).sum := by decide
  have hdescent : baseEnd_2077537 < baseStart_2077537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077538 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2077538 : Nat := 118140960795 + 2077538 * 2 ^ 59
def prefixEnd_2077538 : Nat := 4983230072969 + 3 ^ 40 * 2077538 * 2
def baseEnd_2077538 : Nat := 1066775571980597856720583

theorem tailTrace_2077538 : CollatzResearch.WordTrace tailWord_2077538 prefixEnd_2077538 1066775571980597856720583 := by
  unfold tailWord_2077538
  simp only [CollatzResearch.WordTrace]
  refine ⟨18943508986860529021806317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50516023964961410724816845 18943508986860529021806317)
  ·
    refine ⟨7103815870072698383177369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18943508986860529021806317 7103815870072698383177369)
    ·
      refine ⟨5327861902554523787383027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7103815870072698383177369 5327861902554523787383027)
      ·
        refine ⟨7991792853831785681074541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327861902554523787383027 7991792853831785681074541)
        ·
          refine ⟨2996922320186919630402953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7991792853831785681074541 2996922320186919630402953)
          ·
            refine ⟨2247691740140189722802215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2996922320186919630402953 2247691740140189722802215)
            ·
              refine ⟨3371537610210284584203323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2247691740140189722802215 3371537610210284584203323)
              ·
                refine ⟨5057306415315426876304985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3371537610210284584203323 5057306415315426876304985)
                ·
                  refine ⟨3792979811486570157228739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5057306415315426876304985 3792979811486570157228739)
                  ·
                    refine ⟨5689469717229855235843109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3792979811486570157228739 5689469717229855235843109)
                    ·
                      refine ⟨1066775571980597856720583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5689469717229855235843109 1066775571980597856720583)
                      ·
                        rfl

theorem cell23_2077538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2077538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077538 prefixEnd_2077538 := by exact prefixLift 2077538
  have htrace : WordTrace (prefixWord ++ tailWord_2077538) baseStart_2077538 baseEnd_2077538 := by
    simpa [prefixWord, tailWord_2077538, baseEnd_2077538] using wordTrace_append hprefix tailTrace_2077538
  have hstable : (prefixWord ++ tailWord_2077538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077538).length < 2 ^ (prefixWord ++ tailWord_2077538).sum := by decide
  have hdescent : baseEnd_2077538 < baseStart_2077538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077571 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 3, 1, 3]
def baseStart_2077571 : Nat := 118140960795 + 2077571 * 2 ^ 59
def prefixEnd_2077571 : Nat := 4983230072969 + 3 ^ 40 * 2077571 * 2
def baseEnd_2077571 : Nat := 1066792516842196227607931

theorem tailTrace_2077571 : CollatzResearch.WordTrace tailWord_2077571 prefixEnd_2077571 1066792516842196227607931 := by
  unfold tailWord_2077571
  simp only [CollatzResearch.WordTrace]
  refine ⟨75775239556322562723176567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50516826370881708482117711 75775239556322562723176567)
  ·
    refine ⟨113662859334483844084764851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75775239556322562723176567 113662859334483844084764851)
    ·
      refine ⟨170494289001725766127147277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113662859334483844084764851 170494289001725766127147277)
      ·
        refine ⟨63935358375647162297680229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170494289001725766127147277 63935358375647162297680229)
        ·
          refine ⟨11987879695433842930815043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63935358375647162297680229 11987879695433842930815043)
          ·
            refine ⟨17981819543150764396222565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11987879695433842930815043 17981819543150764396222565)
            ·
              refine ⟨3371591164340768324291731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17981819543150764396222565 3371591164340768324291731)
              ·
                refine ⟨5057386746511152486437597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3371591164340768324291731 5057386746511152486437597)
                ·
                  refine ⟨1896520029941682182414099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5057386746511152486437597 1896520029941682182414099)
                  ·
                    refine ⟨2844780044912523273621149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1896520029941682182414099 2844780044912523273621149)
                    ·
                      refine ⟨1066792516842196227607931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2844780044912523273621149 1066792516842196227607931)
                      ·
                        rfl

theorem cell23_2077571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_2077571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077571 prefixEnd_2077571 := by exact prefixLift 2077571
  have htrace : WordTrace (prefixWord ++ tailWord_2077571) baseStart_2077571 baseEnd_2077571 := by
    simpa [prefixWord, tailWord_2077571, baseEnd_2077571] using wordTrace_append hprefix tailTrace_2077571
  have hstable : (prefixWord ++ tailWord_2077571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077571).length < 2 ^ (prefixWord ++ tailWord_2077571).sum := by decide
  have hdescent : baseEnd_2077571 < baseStart_2077571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077587 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 1, 6]
def baseStart_2077587 : Nat := 118140960795 + 2077587 * 2 ^ 59
def prefixEnd_2077587 : Nat := 4983230072969 + 3 ^ 40 * 2077587 * 2
def baseEnd_2077587 : Nat := 355600244177556055002619

theorem tailTrace_2077587 : CollatzResearch.WordTrace tailWord_2077587 prefixEnd_2077587 355600244177556055002619 := by
  unfold tailWord_2077587
  simp only [CollatzResearch.WordTrace]
  refine ⟨75775823124264597455759015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50517215416176398303839343 75775823124264597455759015)
  ·
    refine ⟨113663734686396896183638523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75775823124264597455759015 113663734686396896183638523)
    ·
      refine ⟨170495602029595344275457785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113663734686396896183638523 170495602029595344275457785)
      ·
        refine ⟨127871701522196508206593339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170495602029595344275457785 127871701522196508206593339)
        ·
          refine ⟨191807552283294762309890009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127871701522196508206593339 191807552283294762309890009)
          ·
            refine ⟨143855664212471071732417507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191807552283294762309890009 143855664212471071732417507)
            ·
              refine ⟨215783496318706607598626261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143855664212471071732417507 215783496318706607598626261)
              ·
                refine ⟨5057425694969686115592803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 215783496318706607598626261 5057425694969686115592803)
                ·
                  refine ⟨7586138542454529173389205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5057425694969686115592803 7586138542454529173389205)
                  ·
                    refine ⟨355600244177556055002619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7586138542454529173389205 355600244177556055002619)
                    ·
                      rfl

theorem cell23_2077587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 6].length) (baseStart_2077587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077587 prefixEnd_2077587 := by exact prefixLift 2077587
  have htrace : WordTrace (prefixWord ++ tailWord_2077587) baseStart_2077587 baseEnd_2077587 := by
    simpa [prefixWord, tailWord_2077587, baseEnd_2077587] using wordTrace_append hprefix tailTrace_2077587
  have hstable : (prefixWord ++ tailWord_2077587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077587).length < 2 ^ (prefixWord ++ tailWord_2077587).sum := by decide
  have hdescent : baseEnd_2077587 < baseStart_2077587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077604 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_2077604 : Nat := 118140960795 + 2077604 * 2 ^ 59
def prefixEnd_2077604 : Nat := 4983230072969 + 3 ^ 40 * 2077604 * 2
def baseEnd_2077604 : Nat := 355603153901264866165093

theorem tailTrace_2077604 : CollatzResearch.WordTrace tailWord_2077604 prefixEnd_2077604 355603153901264866165093 := by
  unfold tailWord_2077604
  simp only [CollatzResearch.WordTrace]
  refine ⟨37888221582601504679563933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50517628776802006239418577 37888221582601504679563933)
  ·
    refine ⟨14208083093475564254836475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37888221582601504679563933 14208083093475564254836475)
    ·
      refine ⟨21312124640213346382254713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14208083093475564254836475 21312124640213346382254713)
      ·
        refine ⟨15984093480160009786691035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21312124640213346382254713 15984093480160009786691035)
        ·
          refine ⟨23976140220240014680036553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15984093480160009786691035 23976140220240014680036553)
          ·
            refine ⟨17982105165180011010027415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23976140220240014680036553 17982105165180011010027415)
            ·
              refine ⟨26973157747770016515041123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17982105165180011010027415 26973157747770016515041123)
              ·
                refine ⟨40459736621655024772561685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26973157747770016515041123 40459736621655024772561685)
                ·
                  refine ⟨1896550154140079286213829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40459736621655024772561685 1896550154140079286213829)
                  ·
                    refine ⟨355603153901264866165093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1896550154140079286213829 355603153901264866165093)
                    ·
                      rfl

theorem cell23_2077604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_2077604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077604 prefixEnd_2077604 := by exact prefixLift 2077604
  have htrace : WordTrace (prefixWord ++ tailWord_2077604) baseStart_2077604 baseEnd_2077604 := by
    simpa [prefixWord, tailWord_2077604, baseEnd_2077604] using wordTrace_append hprefix tailTrace_2077604
  have hstable : (prefixWord ++ tailWord_2077604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077604).length < 2 ^ (prefixWord ++ tailWord_2077604).sum := by decide
  have hdescent : baseEnd_2077604 < baseStart_2077604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077621 : List Nat := [1, 3, 3, 2, 1, 1, 2, 4, 2, 4]
def baseStart_2077621 : Nat := 118140960795 + 2077621 * 2 ^ 59
def prefixEnd_2077621 : Nat := 4983230072969 + 3 ^ 40 * 2077621 * 2
def baseEnd_2077621 : Nat := 355606063624973677327567

theorem tailTrace_2077621 : CollatzResearch.WordTrace tailWord_2077621 prefixEnd_2077621 355606063624973677327567 := by
  unfold tailWord_2077621
  simp only [CollatzResearch.WordTrace]
  refine ⟨75777063206141421262496717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50518042137427614174997811 75777063206141421262496717)
  ·
    refine ⟨28416398702303032973436269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75777063206141421262496717 28416398702303032973436269)
    ·
      refine ⟨10656149513363637365038601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28416398702303032973436269 10656149513363637365038601)
      ·
        refine ⟨7992112135022728023778951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10656149513363637365038601 7992112135022728023778951)
        ·
          refine ⟨11988168202534092035668427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7992112135022728023778951 11988168202534092035668427)
          ·
            refine ⟨17982252303801138053502641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11988168202534092035668427 17982252303801138053502641)
            ·
              refine ⟨13486689227850853540126981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17982252303801138053502641 13486689227850853540126981)
              ·
                refine ⟨2528754230222035038773809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13486689227850853540126981 2528754230222035038773809)
                ·
                  refine ⟨1896565672666526279080357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2528754230222035038773809 1896565672666526279080357)
                  ·
                    refine ⟨355606063624973677327567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1896565672666526279080357 355606063624973677327567)
                    ·
                      rfl

theorem cell23_2077621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_2077621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077621 prefixEnd_2077621 := by exact prefixLift 2077621
  have htrace : WordTrace (prefixWord ++ tailWord_2077621) baseStart_2077621 baseEnd_2077621 := by
    simpa [prefixWord, tailWord_2077621, baseEnd_2077621] using wordTrace_append hprefix tailTrace_2077621
  have hstable : (prefixWord ++ tailWord_2077621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077621).length < 2 ^ (prefixWord ++ tailWord_2077621).sum := by decide
  have hdescent : baseEnd_2077621 < baseStart_2077621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077661 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_2077661 : Nat := 118140960795 + 2077661 * 2 ^ 59
def prefixEnd_2077661 : Nat := 4983230072969 + 3 ^ 40 * 2077661 * 2
def baseEnd_2077661 : Nat := 1066838730101100875482517

theorem tailTrace_2077661 : CollatzResearch.WordTrace tailWord_2077661 prefixEnd_2077661 1066838730101100875482517 := by
  unfold tailWord_2077661
  simp only [CollatzResearch.WordTrace]
  refine ⟨75778522125996508093952837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50519014750664338729301891 75778522125996508093952837)
  ·
    refine ⟨14208472898624345267616157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75778522125996508093952837 14208472898624345267616157)
    ·
      refine ⟨5328177336984129475356059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14208472898624345267616157 5328177336984129475356059)
      ·
        refine ⟨7992266005476194213034089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328177336984129475356059 7992266005476194213034089)
        ·
          refine ⟨5994199504107145659775567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7992266005476194213034089 5994199504107145659775567)
          ·
            refine ⟨8991299256160718489663351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994199504107145659775567 8991299256160718489663351)
            ·
              refine ⟨13486948884241077734495027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8991299256160718489663351 13486948884241077734495027)
              ·
                refine ⟨20230423326361616601742541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13486948884241077734495027 20230423326361616601742541)
                ·
                  refine ⟨7586408747385606225653453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20230423326361616601742541 7586408747385606225653453)
                  ·
                    refine ⟨2844903280269602334620045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7586408747385606225653453 2844903280269602334620045)
                    ·
                      refine ⟨1066838730101100875482517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2844903280269602334620045 1066838730101100875482517)
                      ·
                        rfl

theorem cell23_2077661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_2077661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077661 prefixEnd_2077661 := by exact prefixLift 2077661
  have htrace : WordTrace (prefixWord ++ tailWord_2077661) baseStart_2077661 baseEnd_2077661 := by
    simpa [prefixWord, tailWord_2077661, baseEnd_2077661] using wordTrace_append hprefix tailTrace_2077661
  have hstable : (prefixWord ++ tailWord_2077661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077661).length < 2 ^ (prefixWord ++ tailWord_2077661).sum := by decide
  have hdescent : baseEnd_2077661 < baseStart_2077661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077685 : List Nat := [1, 3, 5, 2, 2, 1, 1, 8]
def baseStart_2077685 : Nat := 118140960795 + 2077685 * 2 ^ 59
def prefixEnd_2077685 : Nat := 4983230072969 + 3 ^ 40 * 2077685 * 2
def baseEnd_2077685 : Nat := 39513001986548473391941

theorem tailTrace_2077685 : CollatzResearch.WordTrace tailWord_2077685 prefixEnd_2077685 39513001986548473391941 := by
  unfold tailWord_2077685
  simp only [CollatzResearch.WordTrace]
  refine ⟨75779397477909560192826509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50519598318606373461884339 75779397477909560192826509)
  ·
    refine ⟨28417274054216085072309941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75779397477909560192826509 28417274054216085072309941)
    ·
      refine ⟨2664119442582757975529057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28417274054216085072309941 2664119442582757975529057)
      ·
        refine ⟨1998089581937068481646793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2664119442582757975529057 1998089581937068481646793)
        ·
          refine ⟨1498567186452801361235095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1998089581937068481646793 1498567186452801361235095)
          ·
            refine ⟨2247850779679202041852643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498567186452801361235095 2247850779679202041852643)
            ·
              refine ⟨3371776169518803062778965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2247850779679202041852643 3371776169518803062778965)
              ·
                refine ⟨39513001986548473391941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3371776169518803062778965 39513001986548473391941)
                ·
                  rfl

theorem cell23_2077685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 8].length) (baseStart_2077685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077685 prefixEnd_2077685 := by exact prefixLift 2077685
  have htrace : WordTrace (prefixWord ++ tailWord_2077685) baseStart_2077685 baseEnd_2077685 := by
    simpa [prefixWord, tailWord_2077685, baseEnd_2077685] using wordTrace_append hprefix tailTrace_2077685
  have hstable : (prefixWord ++ tailWord_2077685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077685).length < 2 ^ (prefixWord ++ tailWord_2077685).sum := by decide
  have hdescent : baseEnd_2077685 < baseStart_2077685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077748 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2077748 : Nat := 118140960795 + 2077748 * 2 ^ 59
def prefixEnd_2077748 : Nat := 4983230072969 + 3 ^ 40 * 2077748 * 2
def baseEnd_2077748 : Nat := 1066883402918042035094617

theorem tailTrace_2077748 : CollatzResearch.WordTrace tailWord_2077748 prefixEnd_2077748 1066883402918042035094617 := by
  unfold tailWord_2077748
  simp only [CollatzResearch.WordTrace]
  refine ⟨37890847638340660976184949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50521130184454214634913265 37890847638340660976184949)
  ·
    refine ⟨3552266966094436966517339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37890847638340660976184949 3552266966094436966517339)
    ·
      refine ⟨5328400449141655449776009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552266966094436966517339 5328400449141655449776009)
      ·
        refine ⟨3996300336856241587332007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5328400449141655449776009 3996300336856241587332007)
        ·
          refine ⟨5994450505284362380998011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3996300336856241587332007 5994450505284362380998011)
          ·
            refine ⟨8991675757926543571497017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994450505284362380998011 8991675757926543571497017)
            ·
              refine ⟨6743756818444907678622763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8991675757926543571497017 6743756818444907678622763)
              ·
                refine ⟨10115635227667361517934145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6743756818444907678622763 10115635227667361517934145)
                ·
                  refine ⟨7586726420750521138450609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10115635227667361517934145 7586726420750521138450609)
                  ·
                    refine ⟨5690044815562890853837957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7586726420750521138450609 5690044815562890853837957)
                    ·
                      refine ⟨1066883402918042035094617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5690044815562890853837957 1066883402918042035094617)
                      ·
                        rfl

theorem cell23_2077748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2077748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077748 prefixEnd_2077748 := by exact prefixLift 2077748
  have htrace : WordTrace (prefixWord ++ tailWord_2077748) baseStart_2077748 baseEnd_2077748 := by
    simpa [prefixWord, tailWord_2077748, baseEnd_2077748] using wordTrace_append hprefix tailTrace_2077748
  have hstable : (prefixWord ++ tailWord_2077748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077748).length < 2 ^ (prefixWord ++ tailWord_2077748).sum := by decide
  have hdescent : baseEnd_2077748 < baseStart_2077748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077752 : List Nat := [2, 1, 2, 1, 5, 2, 3, 1, 2, 2, 2]
def baseStart_2077752 : Nat := 118140960795 + 2077752 * 2 ^ 59
def prefixEnd_2077752 : Nat := 4983230072969 + 3 ^ 40 * 2077752 * 2
def baseEnd_2077752 : Nat := 1066885456840660019444599

theorem tailTrace_2077752 : CollatzResearch.WordTrace tailWord_2077752 prefixEnd_2077752 1066885456840660019444599 := by
  unfold tailWord_2077752
  simp only [CollatzResearch.WordTrace]
  refine ⟨37890920584333415317757755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50521227445777887090343673 37890920584333415317757755)
  ·
    refine ⟨56836380876500122976636633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37890920584333415317757755 56836380876500122976636633)
    ·
      refine ⟨42627285657375092232477475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56836380876500122976636633 42627285657375092232477475)
      ·
        refine ⟨63940928486062638348716213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42627285657375092232477475 63940928486062638348716213)
        ·
          refine ⟨5994462045568372345192145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63940928486062638348716213 5994462045568372345192145)
          ·
            refine ⟨4495846534176279258894109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5994462045568372345192145 4495846534176279258894109)
            ·
              refine ⟨1685942450316104722085291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4495846534176279258894109 1685942450316104722085291)
              ·
                refine ⟨2528913675474157083127937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685942450316104722085291 2528913675474157083127937)
                ·
                  refine ⟨1896685256605617812345953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2528913675474157083127937 1896685256605617812345953)
                  ·
                    refine ⟨1422513942454213359259465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1896685256605617812345953 1422513942454213359259465)
                    ·
                      refine ⟨1066885456840660019444599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1422513942454213359259465 1066885456840660019444599)
                      ·
                        rfl

theorem cell23_2077752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 2, 2, 2].length) (baseStart_2077752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077752 prefixEnd_2077752 := by exact prefixLift 2077752
  have htrace : WordTrace (prefixWord ++ tailWord_2077752) baseStart_2077752 baseEnd_2077752 := by
    simpa [prefixWord, tailWord_2077752, baseEnd_2077752] using wordTrace_append hprefix tailTrace_2077752
  have hstable : (prefixWord ++ tailWord_2077752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077752).length < 2 ^ (prefixWord ++ tailWord_2077752).sum := by decide
  have hdescent : baseEnd_2077752 < baseStart_2077752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077754 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 1, 7]
def baseStart_2077754 : Nat := 118140960795 + 2077754 * 2 ^ 59
def prefixEnd_2077754 : Nat := 4983230072969 + 3 ^ 40 * 2077754 * 2
def baseEnd_2077754 : Nat := 355628827933989670539863

theorem tailTrace_2077754 : CollatzResearch.WordTrace tailWord_2077754 prefixEnd_2077754 355628827933989670539863 := by
  unfold tailWord_2077754
  simp only [CollatzResearch.WordTrace]
  refine ⟨18945478528664896244272079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50521276076439723318058877 18945478528664896244272079)
  ·
    refine ⟨28418217792997344366408119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18945478528664896244272079 28418217792997344366408119)
    ·
      refine ⟨42627326689496016549612179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28418217792997344366408119 42627326689496016549612179)
      ·
        refine ⟨63940990034244024824418269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42627326689496016549612179 63940990034244024824418269)
        ·
          refine ⟨23977871262841509309156851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63940990034244024824418269 23977871262841509309156851)
          ·
            refine ⟨35966806894262263963735277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23977871262841509309156851 35966806894262263963735277)
            ·
              refine ⟨13487552585348348986400729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35966806894262263963735277 13487552585348348986400729)
              ·
                refine ⟨10115664439011261739800547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13487552585348348986400729 10115664439011261739800547)
                ·
                  refine ⟨15173496658516892609700821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10115664439011261739800547 15173496658516892609700821)
                  ·
                    refine ⟨355628827933989670539863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15173496658516892609700821 355628827933989670539863)
                    ·
                      rfl

theorem cell23_2077754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_2077754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077754 prefixEnd_2077754 := by exact prefixLift 2077754
  have htrace : WordTrace (prefixWord ++ tailWord_2077754) baseStart_2077754 baseEnd_2077754 := by
    simpa [prefixWord, tailWord_2077754, baseEnd_2077754] using wordTrace_append hprefix tailTrace_2077754
  have hstable : (prefixWord ++ tailWord_2077754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077754).length < 2 ^ (prefixWord ++ tailWord_2077754).sum := by decide
  have hdescent : baseEnd_2077754 < baseStart_2077754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077791 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 4]
def baseStart_2077791 : Nat := 118140960795 + 2077791 * 2 ^ 59
def prefixEnd_2077791 : Nat := 4983230072969 + 3 ^ 40 * 2077791 * 2
def baseEnd_2077791 : Nat := 1066905482586185366856919

theorem tailTrace_2077791 : CollatzResearch.WordTrace tailWord_2077791 prefixEnd_2077791 1066905482586185366856919 := by
  unfold tailWord_2077791
  simp only [CollatzResearch.WordTrace]
  refine ⟨75783263615525540296185227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50522175743683693530790151 75783263615525540296185227)
  ·
    refine ⟨113674895423288310444277841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75783263615525540296185227 113674895423288310444277841)
    ·
      refine ⟨85256171567466232833208381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113674895423288310444277841 85256171567466232833208381)
      ·
        refine ⟨31971064337799837312453143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85256171567466232833208381 31971064337799837312453143)
        ·
          refine ⟨47956596506699755968679715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31971064337799837312453143 47956596506699755968679715)
          ·
            refine ⟨71934894760049633953019573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47956596506699755968679715 71934894760049633953019573)
            ·
              refine ⟨6743896383754653183095585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71934894760049633953019573 6743896383754653183095585)
              ·
                refine ⟨5057922287815989887321689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6743896383754653183095585 5057922287815989887321689)
                ·
                  refine ⟨3793441715861992415491267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5057922287815989887321689 3793441715861992415491267)
                  ·
                    refine ⟨5690162573792988623236901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3793441715861992415491267 5690162573792988623236901)
                    ·
                      refine ⟨1066905482586185366856919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5690162573792988623236901 1066905482586185366856919)
                      ·
                        rfl

theorem cell23_2077791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_2077791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077791 prefixEnd_2077791 := by exact prefixLift 2077791
  have htrace : WordTrace (prefixWord ++ tailWord_2077791) baseStart_2077791 baseEnd_2077791 := by
    simpa [prefixWord, tailWord_2077791, baseEnd_2077791] using wordTrace_append hprefix tailTrace_2077791
  have hstable : (prefixWord ++ tailWord_2077791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077791).length < 2 ^ (prefixWord ++ tailWord_2077791).sum := by decide
  have hdescent : baseEnd_2077791 < baseStart_2077791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077828 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_2077828 : Nat := 118140960795 + 2077828 * 2 ^ 59
def prefixEnd_2077828 : Nat := 4983230072969 + 3 ^ 40 * 2077828 * 2
def baseEnd_2077828 : Nat := 1066924481370401722094249

theorem tailTrace_2077828 : CollatzResearch.WordTrace tailWord_2077828 prefixEnd_2077828 1066924481370401722094249 := by
  unfold tailWord_2077828
  simp only [CollatzResearch.WordTrace]
  refine ⟨37892306558195747807641069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50523075410927663743521425 37892306558195747807641069)
  ·
    refine ⟨14209614959323405427865401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37892306558195747807641069 14209614959323405427865401)
    ·
      refine ⟨10657211219492554070899051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14209614959323405427865401 10657211219492554070899051)
      ·
        refine ⟨15985816829238831106348577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10657211219492554070899051 15985816829238831106348577)
        ·
          refine ⟨11989362621929123329761433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15985816829238831106348577 11989362621929123329761433)
          ·
            refine ⟨8992021966446842497321075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11989362621929123329761433 8992021966446842497321075)
            ·
              refine ⟨13488032949670263745981613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992021966446842497321075 13488032949670263745981613)
              ·
                refine ⟨5058012356126348904743105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13488032949670263745981613 5058012356126348904743105)
                ·
                  refine ⟨3793509267094761678557329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5058012356126348904743105 3793509267094761678557329)
                  ·
                    refine ⟨2845131950321071258917997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3793509267094761678557329 2845131950321071258917997)
                    ·
                      refine ⟨1066924481370401722094249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2845131950321071258917997 1066924481370401722094249)
                      ·
                        rfl

theorem cell23_2077828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_2077828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077828 prefixEnd_2077828 := by exact prefixLift 2077828
  have htrace : WordTrace (prefixWord ++ tailWord_2077828) baseStart_2077828 baseEnd_2077828 := by
    simpa [prefixWord, tailWord_2077828, baseEnd_2077828] using wordTrace_append hprefix tailTrace_2077828
  have hstable : (prefixWord ++ tailWord_2077828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077828).length < 2 ^ (prefixWord ++ tailWord_2077828).sum := by decide
  have hdescent : baseEnd_2077828 < baseStart_2077828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077848 : List Nat := [2, 1, 2, 4, 2, 2, 2, 2, 6]
def baseStart_2077848 : Nat := 118140960795 + 2077848 * 2 ^ 59
def prefixEnd_2077848 : Nat := 4983230072969 + 3 ^ 40 * 2077848 * 2
def baseEnd_2077848 : Nat := 118548305664832404871573

theorem tailTrace_2077848 : CollatzResearch.WordTrace tailWord_2077848 prefixEnd_2077848 118548305664832404871573 := by
  unfold tailWord_2077848
  simp only [CollatzResearch.WordTrace]
  refine ⟨37892671288159519515505099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50523561717546026020673465 37892671288159519515505099)
  ·
    refine ⟨56839006932239279273257649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37892671288159519515505099 56839006932239279273257649)
    ·
      refine ⟨42629255199179459454943237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56839006932239279273257649 42629255199179459454943237)
      ·
        refine ⟨7992985349846148647801857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42629255199179459454943237 7992985349846148647801857)
        ·
          refine ⟨5994739012384611485851393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7992985349846148647801857 5994739012384611485851393)
          ·
            refine ⟨4496054259288458614388545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5994739012384611485851393 4496054259288458614388545)
            ·
              refine ⟨3372040694466343960791409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4496054259288458614388545 3372040694466343960791409)
              ·
                refine ⟨2529030520849757970593557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3372040694466343960791409 2529030520849757970593557)
                ·
                  refine ⟨118548305664832404871573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2529030520849757970593557 118548305664832404871573)
                  ·
                    rfl

theorem cell23_2077848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 6].length) (baseStart_2077848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077848 prefixEnd_2077848 := by exact prefixLift 2077848
  have htrace : WordTrace (prefixWord ++ tailWord_2077848) baseStart_2077848 baseEnd_2077848 := by
    simpa [prefixWord, tailWord_2077848, baseEnd_2077848] using wordTrace_append hprefix tailTrace_2077848
  have hstable : (prefixWord ++ tailWord_2077848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077848).length < 2 ^ (prefixWord ++ tailWord_2077848).sum := by decide
  have hdescent : baseEnd_2077848 < baseStart_2077848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077852 : List Nat := [2, 2, 3, 2, 1, 2, 4, 2, 1, 4]
def baseStart_2077852 : Nat := 118140960795 + 2077852 * 2 ^ 59
def prefixEnd_2077852 : Nat := 4983230072969 + 3 ^ 40 * 2077852 * 2
def baseEnd_2077852 : Nat := 355645601635369876064713

theorem tailTrace_2077852 : CollatzResearch.WordTrace tailWord_2077852 prefixEnd_2077852 355645601635369876064713 := by
  unfold tailWord_2077852
  simp only [CollatzResearch.WordTrace]
  refine ⟨37892744234152273857077905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50523658978869698476103873 37892744234152273857077905)
  ·
    refine ⟨28419558175614205392808429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37892744234152273857077905 28419558175614205392808429)
    ·
      refine ⟨10657334315855327022303161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28419558175614205392808429 10657334315855327022303161)
      ·
        refine ⟨7993000736891495266727371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10657334315855327022303161 7993000736891495266727371)
        ·
          refine ⟨11989501105337242900091057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993000736891495266727371 11989501105337242900091057)
          ·
            refine ⟨8992125829002932175068293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11989501105337242900091057 8992125829002932175068293)
            ·
              refine ⟨1686023592938049782825305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8992125829002932175068293 1686023592938049782825305)
              ·
                refine ⟨1264517694703537337118979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1686023592938049782825305 1264517694703537337118979)
                ·
                  refine ⟨1896776542055306005678469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264517694703537337118979 1896776542055306005678469)
                  ·
                    refine ⟨355645601635369876064713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1896776542055306005678469 355645601635369876064713)
                    ·
                      rfl

theorem cell23_2077852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_2077852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077852 prefixEnd_2077852 := by exact prefixLift 2077852
  have htrace : WordTrace (prefixWord ++ tailWord_2077852) baseStart_2077852 baseEnd_2077852 := by
    simpa [prefixWord, tailWord_2077852, baseEnd_2077852] using wordTrace_append hprefix tailTrace_2077852
  have hstable : (prefixWord ++ tailWord_2077852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077852).length < 2 ^ (prefixWord ++ tailWord_2077852).sum := by decide
  have hdescent : baseEnd_2077852 < baseStart_2077852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077861 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 3, 5]
def baseStart_2077861 : Nat := 118140960795 + 2077861 * 2 ^ 59
def prefixEnd_2077861 : Nat := 4983230072969 + 3 ^ 40 * 2077861 * 2
def baseEnd_2077861 : Nat := 355647142077333364327199

theorem tailTrace_2077861 : CollatzResearch.WordTrace tailWord_2077861 prefixEnd_2077861 355647142077333364327199 := by
  unfold tailWord_2077861
  simp only [CollatzResearch.WordTrace]
  refine ⟨75785816725271942251233437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50523877816847961500822291 75785816725271942251233437)
  ·
    refine ⟨28419681271976978344212539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75785816725271942251233437 28419681271976978344212539)
    ·
      refine ⟨42629521907965467516318809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28419681271976978344212539 42629521907965467516318809)
      ·
        refine ⟨31972141430974100637239107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42629521907965467516318809 31972141430974100637239107)
        ·
          refine ⟨47958212146461150955858661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31972141430974100637239107 47958212146461150955858661)
          ·
            refine ⟨8992164777461465804223499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47958212146461150955858661 8992164777461465804223499)
            ·
              refine ⟨13488247166192198706335249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992164777461465804223499 13488247166192198706335249)
              ·
                refine ⟨10116185374644149029751437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13488247166192198706335249 10116185374644149029751437)
                ·
                  refine ⟨3793569515491555886156789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10116185374644149029751437 3793569515491555886156789)
                  ·
                    refine ⟨355647142077333364327199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3793569515491555886156789 355647142077333364327199)
                    ·
                      rfl

theorem cell23_2077861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_2077861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077861 prefixEnd_2077861 := by exact prefixLift 2077861
  have htrace : WordTrace (prefixWord ++ tailWord_2077861) baseStart_2077861 baseEnd_2077861 := by
    simpa [prefixWord, tailWord_2077861, baseEnd_2077861] using wordTrace_append hprefix tailTrace_2077861
  have hstable : (prefixWord ++ tailWord_2077861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077861).length < 2 ^ (prefixWord ++ tailWord_2077861).sum := by decide
  have hdescent : baseEnd_2077861 < baseStart_2077861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077885 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 2, 3, 2]
def baseStart_2077885 : Nat := 118140960795 + 2077885 * 2 ^ 59
def prefixEnd_2077885 : Nat := 4983230072969 + 3 ^ 40 * 2077885 * 2
def baseEnd_2077885 : Nat := 1066953749767707999081487

theorem tailTrace_2077885 : CollatzResearch.WordTrace tailWord_2077885 prefixEnd_2077885 1066953749767707999081487 := by
  unfold tailWord_2077885
  simp only [CollatzResearch.WordTrace]
  refine ⟨75786692077184994350107109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50524461384789996233404739 75786692077184994350107109)
  ·
    refine ⟨14210004764472186440645083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75786692077184994350107109 14210004764472186440645083)
    ·
      refine ⟨21315007146708279660967625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14210004764472186440645083 21315007146708279660967625)
      ·
        refine ⟨15986255360031209745725719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21315007146708279660967625 15986255360031209745725719)
        ·
          refine ⟨23979383040046814618588579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15986255360031209745725719 23979383040046814618588579)
          ·
            refine ⟨35969074560070221927882869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23979383040046814618588579 35969074560070221927882869)
            ·
              refine ⟨3372100740006583305739019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35969074560070221927882869 3372100740006583305739019)
              ·
                refine ⟨5058151110009874958608529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3372100740006583305739019 5058151110009874958608529)
                ·
                  refine ⟨3793613332507406218956397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5058151110009874958608529 3793613332507406218956397)
                  ·
                    refine ⟨1422604999690277332108649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3793613332507406218956397 1422604999690277332108649)
                    ·
                      refine ⟨1066953749767707999081487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1422604999690277332108649 1066953749767707999081487)
                      ·
                        rfl

theorem cell23_2077885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_2077885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077885 prefixEnd_2077885 := by exact prefixLift 2077885
  have htrace : WordTrace (prefixWord ++ tailWord_2077885) baseStart_2077885 baseEnd_2077885 := by
    simpa [prefixWord, tailWord_2077885, baseEnd_2077885] using wordTrace_append hprefix tailTrace_2077885
  have hstable : (prefixWord ++ tailWord_2077885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077885).length < 2 ^ (prefixWord ++ tailWord_2077885).sum := by decide
  have hdescent : baseEnd_2077885 < baseStart_2077885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077911 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_2077911 : Nat := 118140960795 + 2077911 * 2 ^ 59
def prefixEnd_2077911 : Nat := 4983230072969 + 3 ^ 40 * 2077911 * 2
def baseEnd_2077911 : Nat := 1066967100264724897356367

theorem tailTrace_2077911 : CollatzResearch.WordTrace tailWord_2077911 prefixEnd_2077911 1066967100264724897356367 := by
  unfold tailWord_2077911
  simp only [CollatzResearch.WordTrace]
  refine ⟨75787640375090800790553587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50525093583393867193702391 75787640375090800790553587)
  ·
    refine ⟨113681460562636201185830381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75787640375090800790553587 113681460562636201185830381)
    ·
      refine ⟨42630547710988575444686393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113681460562636201185830381 42630547710988575444686393)
      ·
        refine ⟨31972910783241431583514795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42630547710988575444686393 31972910783241431583514795)
        ·
          refine ⟨47959366174862147375272193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31972910783241431583514795 47959366174862147375272193)
          ·
            refine ⟨35969524631146610531454145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47959366174862147375272193 35969524631146610531454145)
            ·
              refine ⟨26977143473359957898590609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35969524631146610531454145 26977143473359957898590609)
              ·
                refine ⟨20232857605019968423942957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26977143473359957898590609 20232857605019968423942957)
                ·
                  refine ⟨7587321601882488158978609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20232857605019968423942957 7587321601882488158978609)
                  ·
                    refine ⟨5690491201411866119233957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7587321601882488158978609 5690491201411866119233957)
                    ·
                      refine ⟨1066967100264724897356367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5690491201411866119233957 1066967100264724897356367)
                      ·
                        rfl

theorem cell23_2077911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_2077911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077911 prefixEnd_2077911 := by exact prefixLift 2077911
  have htrace : WordTrace (prefixWord ++ tailWord_2077911) baseStart_2077911 baseEnd_2077911 := by
    simpa [prefixWord, tailWord_2077911, baseEnd_2077911] using wordTrace_append hprefix tailTrace_2077911
  have hstable : (prefixWord ++ tailWord_2077911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077911).length < 2 ^ (prefixWord ++ tailWord_2077911).sum := by decide
  have hdescent : baseEnd_2077911 < baseStart_2077911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077925 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 1, 6]
def baseStart_2077925 : Nat := 118140960795 + 2077925 * 2 ^ 59
def prefixEnd_2077925 : Nat := 4983230072969 + 3 ^ 40 * 2077925 * 2
def baseEnd_2077925 : Nat := 355658096331295947527101

theorem tailTrace_2077925 : CollatzResearch.WordTrace tailWord_2077925 prefixEnd_2077925 355658096331295947527101 := by
  unfold tailWord_2077925
  simp only [CollatzResearch.WordTrace]
  refine ⟨75788150997040081181563229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50525433998026720787708819 75788150997040081181563229)
  ·
    refine ⟨28420556623890030443086211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75788150997040081181563229 28420556623890030443086211)
    ·
      refine ⟨42630834935835045664629317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28420556623890030443086211 42630834935835045664629317)
      ·
        refine ⟨7993281550469071062117997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42630834935835045664629317 7993281550469071062117997)
        ·
          refine ⟨2997480581425901648294249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7993281550469071062117997 2997480581425901648294249)
          ·
            refine ⟨2248110436069426236220687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2997480581425901648294249 2248110436069426236220687)
            ·
              refine ⟨3372165654104139354331031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248110436069426236220687 3372165654104139354331031)
              ·
                refine ⟨5058248481156209031496547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3372165654104139354331031 5058248481156209031496547)
                ·
                  refine ⟨7587372721734313547244821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5058248481156209031496547 7587372721734313547244821)
                  ·
                    refine ⟨355658096331295947527101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7587372721734313547244821 355658096331295947527101)
                    ·
                      rfl

theorem cell23_2077925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_2077925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077925 prefixEnd_2077925 := by exact prefixLift 2077925
  have htrace : WordTrace (prefixWord ++ tailWord_2077925) baseStart_2077925 baseEnd_2077925 := by
    simpa [prefixWord, tailWord_2077925, baseEnd_2077925] using wordTrace_append hprefix tailTrace_2077925
  have hstable : (prefixWord ++ tailWord_2077925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077925).length < 2 ^ (prefixWord ++ tailWord_2077925).sum := by decide
  have hdescent : baseEnd_2077925 < baseStart_2077925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077938 : List Nat := [3, 2, 1, 3, 3, 1, 1, 9]
def baseStart_2077938 : Nat := 118140960795 + 2077938 * 2 ^ 59
def prefixEnd_2077938 : Nat := 4983230072969 + 3 ^ 40 * 2077938 * 2
def baseEnd_2077938 : Nat := 39517813490459121915509

theorem tailTrace_2077938 : CollatzResearch.WordTrace tailWord_2077938 prefixEnd_2077938 39517813490459121915509 := by
  unfold tailWord_2077938
  simp only [CollatzResearch.WordTrace]
  refine ⟨18947156286498246100446617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50525750097328656267857645 18947156286498246100446617)
  ·
    refine ⟨14210367214873684575334963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18947156286498246100446617 14210367214873684575334963)
    ·
      refine ⟨21315550822310526863002445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14210367214873684575334963 21315550822310526863002445)
      ·
        refine ⟨7993331558366447573625917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21315550822310526863002445 7993331558366447573625917)
        ·
          refine ⟨2997499334387417840109719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7993331558366447573625917 2997499334387417840109719)
          ·
            refine ⟨4496249001581126760164579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997499334387417840109719 4496249001581126760164579)
            ·
              refine ⟨6744373502371690140246869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496249001581126760164579 6744373502371690140246869)
              ·
                refine ⟨39517813490459121915509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6744373502371690140246869 39517813490459121915509)
                ·
                  rfl

theorem cell23_2077938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 9].length) (baseStart_2077938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077938 prefixEnd_2077938 := by exact prefixLift 2077938
  have htrace : WordTrace (prefixWord ++ tailWord_2077938) baseStart_2077938 baseEnd_2077938 := by
    simpa [prefixWord, tailWord_2077938, baseEnd_2077938] using wordTrace_append hprefix tailTrace_2077938
  have hstable : (prefixWord ++ tailWord_2077938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077938).length < 2 ^ (prefixWord ++ tailWord_2077938).sum := by decide
  have hdescent : baseEnd_2077938 < baseStart_2077938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077961 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 5]
def baseStart_2077961 : Nat := 118140960795 + 2077961 * 2 ^ 59
def prefixEnd_2077961 : Nat := 4983230072969 + 3 ^ 40 * 2077961 * 2
def baseEnd_2077961 : Nat := 1066992774297449701731137

theorem tailTrace_2077961 : CollatzResearch.WordTrace tailWord_2077961 prefixEnd_2077961 1066992774297449701731137 := by
  unfold tailWord_2077961
  simp only [CollatzResearch.WordTrace]
  refine ⟨75789464024909659329873737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50526309349939772886582491 75789464024909659329873737)
  ·
    refine ⟨56842098018682244497405303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75789464024909659329873737 56842098018682244497405303)
    ·
      refine ⟨85263147028023366746107955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56842098018682244497405303 85263147028023366746107955)
      ·
        refine ⟨127894720542035050119161933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85263147028023366746107955 127894720542035050119161933)
        ·
          refine ⟨47960520203263143794685725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127894720542035050119161933 47960520203263143794685725)
          ·
            refine ⟨17985195076223678923007147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47960520203263143794685725 17985195076223678923007147)
            ·
              refine ⟨26977792614335518384510721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17985195076223678923007147 26977792614335518384510721)
              ·
                refine ⟨20233344460751638788383041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26977792614335518384510721 20233344460751638788383041)
                ·
                  refine ⟨15175008345563729091287281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20233344460751638788383041 15175008345563729091287281)
                  ·
                    refine ⟨11381256259172796818465461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15175008345563729091287281 11381256259172796818465461)
                    ·
                      refine ⟨1066992774297449701731137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11381256259172796818465461 1066992774297449701731137)
                      ·
                        rfl

theorem cell23_2077961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_2077961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077961 prefixEnd_2077961 := by exact prefixLift 2077961
  have htrace : WordTrace (prefixWord ++ tailWord_2077961) baseStart_2077961 baseEnd_2077961 := by
    simpa [prefixWord, tailWord_2077961, baseEnd_2077961] using wordTrace_append hprefix tailTrace_2077961
  have hstable : (prefixWord ++ tailWord_2077961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077961).length < 2 ^ (prefixWord ++ tailWord_2077961).sum := by decide
  have hdescent : baseEnd_2077961 < baseStart_2077961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077966 : List Nat := [4, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2]
def baseStart_2077966 : Nat := 118140960795 + 2077966 * 2 ^ 59
def prefixEnd_2077966 : Nat := 4983230072969 + 3 ^ 40 * 2077966 * 2
def baseEnd_2077966 : Nat := 1066995341700722182168615

theorem tailTrace_2077966 : CollatzResearch.WordTrace tailWord_2077966 prefixEnd_2077966 1066995341700722182168615 := by
  unfold tailWord_2077966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9473705798736443147975719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50526430926594363455870501 9473705798736443147975719)
  ·
    refine ⟨14210558698104664721963579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9473705798736443147975719 14210558698104664721963579)
    ·
      refine ⟨21315838047156997082945369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14210558698104664721963579 21315838047156997082945369)
      ·
        refine ⟨15986878535367747812209027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21315838047156997082945369 15986878535367747812209027)
        ·
          refine ⟨23980317803051621718313541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15986878535367747812209027 23980317803051621718313541)
          ·
            refine ⟨4496309588072179072183789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23980317803051621718313541 4496309588072179072183789)
            ·
              refine ⟨1686116095527067152068921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4496309588072179072183789 1686116095527067152068921)
              ·
                refine ⟨1264587071645300364051691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1686116095527067152068921 1264587071645300364051691)
                ·
                  refine ⟨1896880607467950546077537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264587071645300364051691 1896880607467950546077537)
                  ·
                    refine ⟨1422660455600962909558153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1896880607467950546077537 1422660455600962909558153)
                    ·
                      refine ⟨1066995341700722182168615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1422660455600962909558153 1066995341700722182168615)
                      ·
                        rfl

theorem cell23_2077966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_2077966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077966 prefixEnd_2077966 := by exact prefixLift 2077966
  have htrace : WordTrace (prefixWord ++ tailWord_2077966) baseStart_2077966 baseEnd_2077966 := by
    simpa [prefixWord, tailWord_2077966, baseEnd_2077966] using wordTrace_append hprefix tailTrace_2077966
  have hstable : (prefixWord ++ tailWord_2077966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077966).length < 2 ^ (prefixWord ++ tailWord_2077966).sum := by decide
  have hdescent : baseEnd_2077966 < baseStart_2077966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077975 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 3, 3, 2]
def baseStart_2077975 : Nat := 118140960795 + 2077975 * 2 ^ 59
def prefixEnd_2077975 : Nat := 4983230072969 + 3 ^ 40 * 2077975 * 2
def baseEnd_2077975 : Nat := 1066999963026612646956073

theorem tailTrace_2077975 : CollatzResearch.WordTrace tailWord_2077975 prefixEnd_2077975 1066999963026612646956073 := by
  unfold tailWord_2077975
  simp only [CollatzResearch.WordTrace]
  refine ⟨75789974646858939720883379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50526649764572626480588919 75789974646858939720883379)
  ·
    refine ⟨113684961970288409581325069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75789974646858939720883379 113684961970288409581325069)
    ·
      refine ⟨42631860738858153592996901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113684961970288409581325069 42631860738858153592996901)
      ·
        refine ⟨7993473888535903798686919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42631860738858153592996901 7993473888535903798686919)
        ·
          refine ⟨11990210832803855698030379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993473888535903798686919 11990210832803855698030379)
          ·
            refine ⟨17985316249205783547045569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11990210832803855698030379 17985316249205783547045569)
            ·
              refine ⟨13488987186904337660284177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17985316249205783547045569 13488987186904337660284177)
              ·
                refine ⟨10116740390178253245213133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13488987186904337660284177 10116740390178253245213133)
                ·
                  refine ⟨3793777646316844966954925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10116740390178253245213133 3793777646316844966954925)
                  ·
                    refine ⟨1422666617368816862608097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3793777646316844966954925 1422666617368816862608097)
                    ·
                      refine ⟨1066999963026612646956073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1422666617368816862608097 1066999963026612646956073)
                      ·
                        rfl

theorem cell23_2077975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_2077975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077975 prefixEnd_2077975 := by exact prefixLift 2077975
  have htrace : WordTrace (prefixWord ++ tailWord_2077975) baseStart_2077975 baseEnd_2077975 := by
    simpa [prefixWord, tailWord_2077975, baseEnd_2077975] using wordTrace_append hprefix tailTrace_2077975
  have hstable : (prefixWord ++ tailWord_2077975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077975).length < 2 ^ (prefixWord ++ tailWord_2077975).sum := by decide
  have hdescent : baseEnd_2077975 < baseStart_2077975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077992 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_2077992 : Nat := 118140960795 + 2077992 * 2 ^ 59
def prefixEnd_2077992 : Nat := 4983230072969 + 3 ^ 40 * 2077992 * 2
def baseEnd_2077992 : Nat := 1067008692197739080443495

theorem tailTrace_2077992 : CollatzResearch.WordTrace tailWord_2077992 prefixEnd_2077992 1067008692197739080443495 := by
  unfold tailWord_2077992
  simp only [CollatzResearch.WordTrace]
  refine ⟨37895297343898675812126115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50527063125198234416168153 37895297343898675812126115)
  ·
    refine ⟨56842946015848013718189173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37895297343898675812126115 56842946015848013718189173)
    ·
      refine ⟨5329026188985751286080235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56842946015848013718189173 5329026188985751286080235)
      ·
        refine ⟨7993539283478626929120353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329026188985751286080235 7993539283478626929120353)
        ·
          refine ⟨5995154462608970196840265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7993539283478626929120353 5995154462608970196840265)
          ·
            refine ⟨4496365846956727647630199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5995154462608970196840265 4496365846956727647630199)
            ·
              refine ⟨6744548770435091471445299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496365846956727647630199 6744548770435091471445299)
              ·
                refine ⟨10116823155652637207167949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6744548770435091471445299 10116823155652637207167949)
                ·
                  refine ⟨3793808683369738952687981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10116823155652637207167949 3793808683369738952687981)
                  ·
                    refine ⟨1422678256263652107257993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3793808683369738952687981 1422678256263652107257993)
                    ·
                      refine ⟨1067008692197739080443495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1422678256263652107257993 1067008692197739080443495)
                      ·
                        rfl

theorem cell23_2077992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_2077992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2077992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2077992 prefixEnd_2077992 := by exact prefixLift 2077992
  have htrace : WordTrace (prefixWord ++ tailWord_2077992) baseStart_2077992 baseEnd_2077992 := by
    simpa [prefixWord, tailWord_2077992, baseEnd_2077992] using wordTrace_append hprefix tailTrace_2077992
  have hstable : (prefixWord ++ tailWord_2077992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077992).length < 2 ^ (prefixWord ++ tailWord_2077992).sum := by decide
  have hdescent : baseEnd_2077992 < baseStart_2077992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078005 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_2078005 : Nat := 118140960795 + 2078005 * 2 ^ 59
def prefixEnd_2078005 : Nat := 4983230072969 + 3 ^ 40 * 2078005 * 2
def baseEnd_2078005 : Nat := 1067015367446247529580935

theorem tailTrace_2078005 : CollatzResearch.WordTrace tailWord_2078005 prefixEnd_2078005 1067015367446247529580935 := by
  unfold tailWord_2078005
  simp only [CollatzResearch.WordTrace]
  refine ⟨75791068836750254844475469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50527379224500169896316979 75791068836750254844475469)
  ·
    refine ⟨28421650813781345566678301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75791068836750254844475469 28421650813781345566678301)
    ·
      refine ⟨10658119055168004587504363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28421650813781345566678301 10658119055168004587504363)
      ·
        refine ⟨15987178582752006881256545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10658119055168004587504363 15987178582752006881256545)
        ·
          refine ⟨11990383937064005160942409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15987178582752006881256545 11990383937064005160942409)
          ·
            refine ⟨8992787952798003870706807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11990383937064005160942409 8992787952798003870706807)
            ·
              refine ⟨13489181929197005806060211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992787952798003870706807 13489181929197005806060211)
              ·
                refine ⟨20233772893795508709090317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13489181929197005806060211 20233772893795508709090317)
                ·
                  refine ⟨7587664835173315765908869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20233772893795508709090317 7587664835173315765908869)
                  ·
                    refine ⟨1422687156594996706107913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7587664835173315765908869 1422687156594996706107913)
                    ·
                      refine ⟨1067015367446247529580935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1422687156594996706107913 1067015367446247529580935)
                      ·
                        rfl

theorem cell23_2078005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_2078005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078005 prefixEnd_2078005 := by exact prefixLift 2078005
  have htrace : WordTrace (prefixWord ++ tailWord_2078005) baseStart_2078005 baseEnd_2078005 := by
    simpa [prefixWord, tailWord_2078005, baseEnd_2078005] using wordTrace_append hprefix tailTrace_2078005
  have hstable : (prefixWord ++ tailWord_2078005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078005).length < 2 ^ (prefixWord ++ tailWord_2078005).sum := by decide
  have hdescent : baseEnd_2078005 < baseStart_2078005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078021 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_2078021 : Nat := 118140960795 + 2078021 * 2 ^ 59
def prefixEnd_2078021 : Nat := 4983230072969 + 3 ^ 40 * 2078021 * 2
def baseEnd_2078021 : Nat := 1067023583136719466980861

theorem tailTrace_2078021 : CollatzResearch.WordTrace tailWord_2078021 prefixEnd_2078021 1067023583136719466980861 := by
  unfold tailWord_2078021
  simp only [CollatzResearch.WordTrace]
  refine ⟨75791652404692289577057917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50527768269794859718038611 75791652404692289577057917)
  ·
    refine ⟨28421869651759608591396719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75791652404692289577057917 28421869651759608591396719)
    ·
      refine ⟨42632804477639412887095079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28421869651759608591396719 42632804477639412887095079)
      ·
        refine ⟨63949206716459119330642619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42632804477639412887095079 63949206716459119330642619)
        ·
          refine ⟨95923810074688678995963929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63949206716459119330642619 95923810074688678995963929)
          ·
            refine ⟨71942857556016509246972947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95923810074688678995963929 71942857556016509246972947)
            ·
              refine ⟨107914286334024763870459421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71942857556016509246972947 107914286334024763870459421)
              ·
                refine ⟨40467857375259286451422283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107914286334024763870459421 40467857375259286451422283)
                ·
                  refine ⟨60701786062888929677133425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40467857375259286451422283 60701786062888929677133425)
                  ·
                    refine ⟨45526339547166697257850069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60701786062888929677133425 45526339547166697257850069)
                    ·
                      refine ⟨1067023583136719466980861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45526339547166697257850069 1067023583136719466980861)
                      ·
                        rfl

theorem cell23_2078021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_2078021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078021 prefixEnd_2078021 := by exact prefixLift 2078021
  have htrace : WordTrace (prefixWord ++ tailWord_2078021) baseStart_2078021 baseEnd_2078021 := by
    simpa [prefixWord, tailWord_2078021, baseEnd_2078021] using wordTrace_append hprefix tailTrace_2078021
  have hstable : (prefixWord ++ tailWord_2078021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078021).length < 2 ^ (prefixWord ++ tailWord_2078021).sum := by decide
  have hdescent : baseEnd_2078021 < baseStart_2078021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078105 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 3, 4]
def baseStart_2078105 : Nat := 118140960795 + 2078105 * 2 ^ 59
def prefixEnd_2078105 : Nat := 4983230072969 + 3 ^ 40 * 2078105 * 2
def baseEnd_2078105 : Nat := 355688905170565712776825

theorem tailTrace_2078105 : CollatzResearch.WordTrace tailWord_2078105 prefixEnd_2078105 355688905170565712776825 := by
  unfold tailWord_2078105
  simp only [CollatzResearch.WordTrace]
  refine ⟨75794716136387971923115769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50529810757591981282077179 75794716136387971923115769)
  ·
    refine ⟨56846037102290978942336827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75794716136387971923115769 56846037102290978942336827)
    ·
      refine ⟨85269055653436468413505241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56846037102290978942336827 85269055653436468413505241)
      ·
        refine ⟨63951791740077351310128931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85269055653436468413505241 63951791740077351310128931)
        ·
          refine ⟨95927687610116026965193397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63951791740077351310128931 95927687610116026965193397)
          ·
            refine ⟨8993220713448377527986881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95927687610116026965193397 8993220713448377527986881)
            ·
              refine ⟨6744915535086283145990161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8993220713448377527986881 6744915535086283145990161)
              ·
                refine ⟨5058686651314712359492621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6744915535086283145990161 5058686651314712359492621)
                ·
                  refine ⟨1897007494243017134809733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5058686651314712359492621 1897007494243017134809733)
                  ·
                    refine ⟨355688905170565712776825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1897007494243017134809733 355688905170565712776825)
                    ·
                      rfl

theorem cell23_2078105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 4].length) (baseStart_2078105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078105 prefixEnd_2078105 := by exact prefixLift 2078105
  have htrace : WordTrace (prefixWord ++ tailWord_2078105) baseStart_2078105 baseEnd_2078105 := by
    simpa [prefixWord, tailWord_2078105, baseEnd_2078105] using wordTrace_append hprefix tailTrace_2078105
  have hstable : (prefixWord ++ tailWord_2078105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078105).length < 2 ^ (prefixWord ++ tailWord_2078105).sum := by decide
  have hdescent : baseEnd_2078105 < baseStart_2078105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078115 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 3]
def baseStart_2078115 : Nat := 118140960795 + 2078115 * 2 ^ 59
def prefixEnd_2078115 : Nat := 4983230072969 + 3 ^ 40 * 2078115 * 2
def baseEnd_2078115 : Nat := 1067071850318242099205429

theorem tailTrace_2078115 : CollatzResearch.WordTrace tailWord_2078115 prefixEnd_2078115 1067071850318242099205429 := by
  unfold tailWord_2078115
  simp only [CollatzResearch.WordTrace]
  refine ⟨75795080866351743630979799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50530053910901162420653199 75795080866351743630979799)
  ·
    refine ⟨113692621299527615446469699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75795080866351743630979799 113692621299527615446469699)
    ·
      refine ⟨170538931949291423169704549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113692621299527615446469699 170538931949291423169704549)
      ·
        refine ⟨31976049740492141844319603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170538931949291423169704549 31976049740492141844319603)
        ·
          refine ⟨47964074610738212766479405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31976049740492141844319603 47964074610738212766479405)
          ·
            refine ⟨17986527979026829787429777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47964074610738212766479405 17986527979026829787429777)
            ·
              refine ⟨13489895984270122340572333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17986527979026829787429777 13489895984270122340572333)
              ·
                refine ⟨5058710994101295877714625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13489895984270122340572333 5058710994101295877714625)
                ·
                  refine ⟨3794033245575971908285969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5058710994101295877714625 3794033245575971908285969)
                  ·
                    refine ⟨2845524934181978931214477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3794033245575971908285969 2845524934181978931214477)
                    ·
                      refine ⟨1067071850318242099205429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2845524934181978931214477 1067071850318242099205429)
                      ·
                        rfl

theorem cell23_2078115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_2078115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078115 prefixEnd_2078115 := by exact prefixLift 2078115
  have htrace : WordTrace (prefixWord ++ tailWord_2078115) baseStart_2078115 baseEnd_2078115 := by
    simpa [prefixWord, tailWord_2078115, baseEnd_2078115] using wordTrace_append hprefix tailTrace_2078115
  have hstable : (prefixWord ++ tailWord_2078115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078115).length < 2 ^ (prefixWord ++ tailWord_2078115).sum := by decide
  have hdescent : baseEnd_2078115 < baseStart_2078115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078155 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 3, 5, 2]
def baseStart_2078155 : Nat := 118140960795 + 2078155 * 2 ^ 59
def prefixEnd_2078155 : Nat := 4983230072969 + 3 ^ 40 * 2078155 * 2
def baseEnd_2078155 : Nat := 1067092389544421942705245

theorem tailTrace_2078155 : CollatzResearch.WordTrace tailWord_2078155 prefixEnd_2078155 1067092389544421942705245 := by
  unfold tailWord_2078155
  simp only [CollatzResearch.WordTrace]
  refine ⟨75796539786206830462435919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50531026524137886974957279 75796539786206830462435919)
  ·
    refine ⟨113694809679310245693653879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75796539786206830462435919 113694809679310245693653879)
    ·
      refine ⟨170542214518965368540480819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113694809679310245693653879 170542214518965368540480819)
      ·
        refine ⟨255813321778448052810721229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170542214518965368540480819 255813321778448052810721229)
        ·
          refine ⟨95929995666918019804020461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255813321778448052810721229 95929995666918019804020461)
          ·
            refine ⟨35973748375094257426507673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95929995666918019804020461 35973748375094257426507673)
            ·
              refine ⟨26980311281320693069880755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35973748375094257426507673 26980311281320693069880755)
              ·
                refine ⟨40470466921981039604821133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26980311281320693069880755 40470466921981039604821133)
                ·
                  refine ⟨15176425095742889851807925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40470466921981039604821133 15176425095742889851807925)
                  ·
                    refine ⟨1422789852725895923606993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15176425095742889851807925 1422789852725895923606993)
                    ·
                      refine ⟨1067092389544421942705245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1422789852725895923606993 1067092389544421942705245)
                      ·
                        rfl

theorem cell23_2078155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 5, 2].length) (baseStart_2078155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078155 prefixEnd_2078155 := by exact prefixLift 2078155
  have htrace : WordTrace (prefixWord ++ tailWord_2078155) baseStart_2078155 baseEnd_2078155 := by
    simpa [prefixWord, tailWord_2078155, baseEnd_2078155] using wordTrace_append hprefix tailTrace_2078155
  have hstable : (prefixWord ++ tailWord_2078155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078155).length < 2 ^ (prefixWord ++ tailWord_2078155).sum := by decide
  have hdescent : baseEnd_2078155 < baseStart_2078155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078165 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 3, 5]
def baseStart_2078165 : Nat := 118140960795 + 2078165 * 2 ^ 59
def prefixEnd_2078165 : Nat := 4983230072969 + 3 ^ 40 * 2078165 * 2
def baseEnd_2078165 : Nat := 355699174783655634526733

theorem tailTrace_2078165 : CollatzResearch.WordTrace tailWord_2078165 prefixEnd_2078165 355699174783655634526733 := by
  unfold tailWord_2078165
  simp only [CollatzResearch.WordTrace]
  refine ⟨75796904516170602170299949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50531269677447068113533299 75796904516170602170299949)
  ·
    refine ⟨28423839193563975813862481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75796904516170602170299949 28423839193563975813862481)
    ·
      refine ⟨21317879395172981860396861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28423839193563975813862481 21317879395172981860396861)
      ·
        refine ⟨7994204773189868197648823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21317879395172981860396861 7994204773189868197648823)
        ·
          refine ⟨11991307159784802296473235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994204773189868197648823 11991307159784802296473235)
          ·
            refine ⟨17986960739677203444709853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11991307159784802296473235 17986960739677203444709853)
            ·
              refine ⟨6745110277378951291766195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17986960739677203444709853 6745110277378951291766195)
              ·
                refine ⟨10117665416068426937649293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6745110277378951291766195 10117665416068426937649293)
                ·
                  refine ⟨3794124531025660101618485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10117665416068426937649293 3794124531025660101618485)
                  ·
                    refine ⟨355699174783655634526733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3794124531025660101618485 355699174783655634526733)
                    ·
                      rfl

theorem cell23_2078165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_2078165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078165 prefixEnd_2078165 := by exact prefixLift 2078165
  have htrace : WordTrace (prefixWord ++ tailWord_2078165) baseStart_2078165 baseEnd_2078165 := by
    simpa [prefixWord, tailWord_2078165, baseEnd_2078165] using wordTrace_append hprefix tailTrace_2078165
  have hstable : (prefixWord ++ tailWord_2078165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078165).length < 2 ^ (prefixWord ++ tailWord_2078165).sum := by decide
  have hdescent : baseEnd_2078165 < baseStart_2078165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078185 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 4, 6, 2]
def baseStart_2078185 : Nat := 118140960795 + 2078185 * 2 ^ 59
def prefixEnd_2078185 : Nat := 4983230072969 + 3 ^ 40 * 2078185 * 2
def baseEnd_2078185 : Nat := 1067107793964056825330107

theorem tailTrace_2078185 : CollatzResearch.WordTrace tailWord_2078185 prefixEnd_2078185 1067107793964056825330107 := by
  unfold tailWord_2078185
  simp only [CollatzResearch.WordTrace]
  refine ⟨75797633976098145586028009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50531755984065430390685339 75797633976098145586028009)
  ·
    refine ⟨56848225482073609189521007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75797633976098145586028009 56848225482073609189521007)
    ·
      refine ⟨85272338223110413784281511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56848225482073609189521007 85272338223110413784281511)
      ·
        refine ⟨127908507334665620676422267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85272338223110413784281511 127908507334665620676422267)
        ·
          refine ⟨191862761001998431014633401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127908507334665620676422267 191862761001998431014633401)
          ·
            refine ⟨143897070751498823260975051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191862761001998431014633401 143897070751498823260975051)
            ·
              refine ⟨215845606127248234891462577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143897070751498823260975051 215845606127248234891462577)
              ·
                refine ⟨161884204595436176168596933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215845606127248234891462577 161884204595436176168596933)
                ·
                  refine ⟨30353288361644283031611925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161884204595436176168596933 30353288361644283031611925)
                  ·
                    refine ⟨1422810391952075767106809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30353288361644283031611925 1422810391952075767106809)
                    ·
                      refine ⟨1067107793964056825330107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1422810391952075767106809 1067107793964056825330107)
                      ·
                        rfl

theorem cell23_2078185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 6, 2].length) (baseStart_2078185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078185 prefixEnd_2078185 := by exact prefixLift 2078185
  have htrace : WordTrace (prefixWord ++ tailWord_2078185) baseStart_2078185 baseEnd_2078185 := by
    simpa [prefixWord, tailWord_2078185, baseEnd_2078185] using wordTrace_append hprefix tailTrace_2078185
  have hstable : (prefixWord ++ tailWord_2078185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078185).length < 2 ^ (prefixWord ++ tailWord_2078185).sum := by decide
  have hdescent : baseEnd_2078185 < baseStart_2078185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078225 : List Nat := [1, 2, 2, 1, 1, 2, 7, 7]
def baseStart_2078225 : Nat := 118140960795 + 2078225 * 2 ^ 59
def prefixEnd_2078225 : Nat := 4983230072969 + 3 ^ 40 * 2078225 * 2
def baseEnd_2078225 : Nat := 39523271599638395141849

theorem tailTrace_2078225 : CollatzResearch.WordTrace tailWord_2078225 prefixEnd_2078225 39523271599638395141849 := by
  unfold tailWord_2078225
  simp only [CollatzResearch.WordTrace]
  refine ⟨75799092895953232417484129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50532728597302154944989419 75799092895953232417484129)
  ·
    refine ⟨56849319671964924313113097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75799092895953232417484129 56849319671964924313113097)
    ·
      refine ⟨42636989753973693234834823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56849319671964924313113097 42636989753973693234834823)
      ·
        refine ⟨63955484630960539852252235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42636989753973693234834823 63955484630960539852252235)
        ·
          refine ⟨95933226946440809778378353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63955484630960539852252235 95933226946440809778378353)
          ·
            refine ⟨71949920209830607333783765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95933226946440809778378353 71949920209830607333783765)
            ·
              refine ⟨1686326254917904859385557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71949920209830607333783765 1686326254917904859385557)
              ·
                refine ⟨39523271599638395141849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1686326254917904859385557 39523271599638395141849)
                ·
                  rfl

theorem cell23_2078225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 7].length) (baseStart_2078225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078225 prefixEnd_2078225 := by exact prefixLift 2078225
  have htrace : WordTrace (prefixWord ++ tailWord_2078225) baseStart_2078225 baseEnd_2078225 := by
    simpa [prefixWord, tailWord_2078225, baseEnd_2078225] using wordTrace_append hprefix tailTrace_2078225
  have hstable : (prefixWord ++ tailWord_2078225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078225).length < 2 ^ (prefixWord ++ tailWord_2078225).sum := by decide
  have hdescent : baseEnd_2078225 < baseStart_2078225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078239 : List Nat := [1, 1, 2, 4, 1, 1, 6, 1, 1, 2, 3]
def baseStart_2078239 : Nat := 118140960795 + 2078239 * 2 ^ 59
def prefixEnd_2078239 : Nat := 4983230072969 + 3 ^ 40 * 2078239 * 2
def baseEnd_2078239 : Nat := 1067135521919399614054859

theorem tailTrace_2078239 : CollatzResearch.WordTrace tailWord_2078239 prefixEnd_2078239 1067135521919399614054859 := by
  unfold tailWord_2078239
  simp only [CollatzResearch.WordTrace]
  refine ⟨75799603517902512808493771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50533069011935008538995847 75799603517902512808493771)
  ·
    refine ⟨113699405276853769212740657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75799603517902512808493771 113699405276853769212740657)
    ·
      refine ⟨85274553957640326909555493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113699405276853769212740657 85274553957640326909555493)
      ·
        refine ⟨15988978867057561295541655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85274553957640326909555493 15988978867057561295541655)
        ·
          refine ⟨23983468300586341943312483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15988978867057561295541655 23983468300586341943312483)
          ·
            refine ⟨35975202450879512914968725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23983468300586341943312483 35975202450879512914968725)
            ·
              refine ⟨1686337614884977167889159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35975202450879512914968725 1686337614884977167889159)
              ·
                refine ⟨2529506422327465751833739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1686337614884977167889159 2529506422327465751833739)
                ·
                  refine ⟨3794259633491198627750609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529506422327465751833739 3794259633491198627750609)
                  ·
                    refine ⟨2845694725118398970812957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3794259633491198627750609 2845694725118398970812957)
                    ·
                      refine ⟨1067135521919399614054859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2845694725118398970812957 1067135521919399614054859)
                      ·
                        rfl

theorem cell23_2078239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_2078239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078239 prefixEnd_2078239 := by exact prefixLift 2078239
  have htrace : WordTrace (prefixWord ++ tailWord_2078239) baseStart_2078239 baseEnd_2078239 := by
    simpa [prefixWord, tailWord_2078239, baseEnd_2078239] using wordTrace_append hprefix tailTrace_2078239
  have hstable : (prefixWord ++ tailWord_2078239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078239).length < 2 ^ (prefixWord ++ tailWord_2078239).sum := by decide
  have hdescent : baseEnd_2078239 < baseStart_2078239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078295 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_2078295 : Nat := 118140960795 + 2078295 * 2 ^ 59
def prefixEnd_2078295 : Nat := 4983230072969 + 3 ^ 40 * 2078295 * 2
def baseEnd_2078295 : Nat := 1067164276836051394954601

theorem tailTrace_2078295 : CollatzResearch.WordTrace tailWord_2078295 prefixEnd_2078295 1067164276836051394954601 := by
  unfold tailWord_2078295
  simp only [CollatzResearch.WordTrace]
  refine ⟨75801646005699634372532339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50534430670466422915021559 75801646005699634372532339)
  ·
    refine ⟨113702469008549451558798509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75801646005699634372532339 113702469008549451558798509)
    ·
      refine ⟨42638425878206044334549441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113702469008549451558798509 42638425878206044334549441)
      ·
        refine ⟨31978819408654533250912081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42638425878206044334549441 31978819408654533250912081)
        ·
          refine ⟨23984114556490899938184061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31978819408654533250912081 23984114556490899938184061)
          ·
            refine ⟨8994042958684087476819023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23984114556490899938184061 8994042958684087476819023)
            ·
              refine ⟨13491064438026131215228535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8994042958684087476819023 13491064438026131215228535)
              ·
                refine ⟨20236596657039196822842803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13491064438026131215228535 20236596657039196822842803)
                ·
                  refine ⟨30354894985558795234264205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20236596657039196822842803 30354894985558795234264205)
                  ·
                    refine ⟨11383085619584548212849077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30354894985558795234264205 11383085619584548212849077)
                    ·
                      refine ⟨1067164276836051394954601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11383085619584548212849077 1067164276836051394954601)
                      ·
                        rfl

theorem cell23_2078295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_2078295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078295 prefixEnd_2078295 := by exact prefixLift 2078295
  have htrace : WordTrace (prefixWord ++ tailWord_2078295) baseStart_2078295 baseEnd_2078295 := by
    simpa [prefixWord, tailWord_2078295, baseEnd_2078295] using wordTrace_append hprefix tailTrace_2078295
  have hstable : (prefixWord ++ tailWord_2078295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078295).length < 2 ^ (prefixWord ++ tailWord_2078295).sum := by decide
  have hdescent : baseEnd_2078295 < baseStart_2078295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078345 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 1, 7]
def baseStart_2078345 : Nat := 118140960795 + 2078345 * 2 ^ 59
def prefixEnd_2078345 : Nat := 4983230072969 + 3 ^ 40 * 2078345 * 2
def baseEnd_2078345 : Nat := 355729983622925399776457

theorem tailTrace_2078345 : CollatzResearch.WordTrace tailWord_2078345 prefixEnd_2078345 355729983622925399776457 := by
  unfold tailWord_2078345
  simp only [CollatzResearch.WordTrace]
  refine ⟨75803469655518492911852489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50535646437012328607901659 75803469655518492911852489)
  ·
    refine ⟨56852602241638869683889367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75803469655518492911852489 56852602241638869683889367)
    ·
      refine ⟨85278903362458304525834051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56852602241638869683889367 85278903362458304525834051)
      ·
        refine ⟨127918355043687456788751077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85278903362458304525834051 127918355043687456788751077)
        ·
          refine ⟨23984691570691398147890827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127918355043687456788751077 23984691570691398147890827)
          ·
            refine ⟨35977037356037097221836241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23984691570691398147890827 35977037356037097221836241)
            ·
              refine ⟨26982778017027822916377181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35977037356037097221836241 26982778017027822916377181)
              ·
                refine ⟨10118541756385433593641443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26982778017027822916377181 10118541756385433593641443)
                ·
                  refine ⟨15177812634578150390462165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10118541756385433593641443 15177812634578150390462165)
                  ·
                    refine ⟨355729983622925399776457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15177812634578150390462165 355729983622925399776457)
                    ·
                      rfl

theorem cell23_2078345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_2078345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078345 prefixEnd_2078345 := by exact prefixLift 2078345
  have htrace : WordTrace (prefixWord ++ tailWord_2078345) baseStart_2078345 baseEnd_2078345 := by
    simpa [prefixWord, tailWord_2078345, baseEnd_2078345] using wordTrace_append hprefix tailTrace_2078345
  have hstable : (prefixWord ++ tailWord_2078345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078345).length < 2 ^ (prefixWord ++ tailWord_2078345).sum := by decide
  have hdescent : baseEnd_2078345 < baseStart_2078345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078352 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 4, 5, 2]
def baseStart_2078352 : Nat := 118140960795 + 2078352 * 2 ^ 59
def prefixEnd_2078352 : Nat := 4983230072969 + 3 ^ 40 * 2078352 * 2
def baseEnd_2078352 : Nat := 1067193545233357671941839

theorem tailTrace_2078352 : CollatzResearch.WordTrace tailWord_2078352 prefixEnd_2078352 1067193545233357671941839 := by
  unfold tailWord_2078352
  simp only [CollatzResearch.WordTrace]
  refine ⟨37901862483246566553678655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50535816644328755404904873 37901862483246566553678655)
  ·
    refine ⟨56852793724869849830517983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37901862483246566553678655 56852793724869849830517983)
    ·
      refine ⟨85279190587304774745776975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56852793724869849830517983 85279190587304774745776975)
      ·
        refine ⟨127918785880957162118665463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85279190587304774745776975 127918785880957162118665463)
        ·
          refine ⟨191878178821435743177998195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127918785880957162118665463 191878178821435743177998195)
          ·
            refine ⟨287817268232153614766997293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191878178821435743177998195 287817268232153614766997293)
            ·
              refine ⟨107931475587057605537623985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287817268232153614766997293 107931475587057605537623985)
              ·
                refine ⟨80948606690293204153217989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107931475587057605537623985 80948606690293204153217989)
                ·
                  refine ⟨15177863754429975778728373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80948606690293204153217989 15177863754429975778728373)
                  ·
                    refine ⟨1422924726977810229255785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15177863754429975778728373 1422924726977810229255785)
                    ·
                      refine ⟨1067193545233357671941839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1422924726977810229255785 1067193545233357671941839)
                      ·
                        rfl

theorem cell23_2078352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 5, 2].length) (baseStart_2078352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078352 prefixEnd_2078352 := by exact prefixLift 2078352
  have htrace : WordTrace (prefixWord ++ tailWord_2078352) baseStart_2078352 baseEnd_2078352 := by
    simpa [prefixWord, tailWord_2078352, baseEnd_2078352] using wordTrace_append hprefix tailTrace_2078352
  have hstable : (prefixWord ++ tailWord_2078352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078352).length < 2 ^ (prefixWord ++ tailWord_2078352).sum := by decide
  have hdescent : baseEnd_2078352 < baseStart_2078352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078366 : List Nat := [4, 3, 1, 1, 1, 3, 1, 4, 5]
def baseStart_2078366 : Nat := 118140960795 + 2078366 * 2 ^ 59
def prefixEnd_2078366 : Nat := 4983230072969 + 3 ^ 40 * 2078366 * 2
def baseEnd_2078366 : Nat := 118577859329168957462975

theorem tailTrace_2078366 : CollatzResearch.WordTrace tailWord_2078366 prefixEnd_2078366 118577859329168957462975 := by
  unfold tailWord_2078366
  simp only [CollatzResearch.WordTrace]
  refine ⟨9475529448555301687295869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50536157058961608998911301 9475529448555301687295869)
  ·
    refine ⟨3553323543208238132735951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9475529448555301687295869 3553323543208238132735951)
    ·
      refine ⟨5329985314812357199103927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3553323543208238132735951 5329985314812357199103927)
      ·
        refine ⟨7994977972218535798655891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329985314812357199103927 7994977972218535798655891)
        ·
          refine ⟨11992466958327803697983837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994977972218535798655891 11992466958327803697983837)
          ·
            refine ⟨4497175109372926386743939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11992466958327803697983837 4497175109372926386743939)
            ·
              refine ⟨6745762664059389580115909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4497175109372926386743939 6745762664059389580115909)
              ·
                refine ⟨1264830499511135546271733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6745762664059389580115909 1264830499511135546271733)
                ·
                  refine ⟨118577859329168957462975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1264830499511135546271733 118577859329168957462975)
                  ·
                    rfl

theorem cell23_2078366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_2078366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078366 prefixEnd_2078366 := by exact prefixLift 2078366
  have htrace : WordTrace (prefixWord ++ tailWord_2078366) baseStart_2078366 baseEnd_2078366 := by
    simpa [prefixWord, tailWord_2078366, baseEnd_2078366] using wordTrace_append hprefix tailTrace_2078366
  have hstable : (prefixWord ++ tailWord_2078366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078366).length < 2 ^ (prefixWord ++ tailWord_2078366).sum := by decide
  have hdescent : baseEnd_2078366 < baseStart_2078366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078369 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 2, 5, 2]
def baseStart_2078369 : Nat := 118140960795 + 2078369 * 2 ^ 59
def prefixEnd_2078369 : Nat := 4983230072969 + 3 ^ 40 * 2078369 * 2
def baseEnd_2078369 : Nat := 1067202274404484105429261

theorem tailTrace_2078369 : CollatzResearch.WordTrace tailWord_2078369 prefixEnd_2078369 1067202274404484105429261 := by
  unfold tailWord_2078369
  simp only [CollatzResearch.WordTrace]
  refine ⟨75804345007431545010726161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50536230004954363340484107 75804345007431545010726161)
  ·
    refine ⟨56853258755573658758044621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75804345007431545010726161 56853258755573658758044621)
    ·
      refine ⟨21319972033340122034266733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56853258755573658758044621 21319972033340122034266733)
      ·
        refine ⟨7994989512502545762850025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21319972033340122034266733 7994989512502545762850025)
        ·
          refine ⟨5996242134376909322137519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7994989512502545762850025 5996242134376909322137519)
          ·
            refine ⟨8994363201565363983206279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996242134376909322137519 8994363201565363983206279)
            ·
              refine ⟨13491544802348045974809419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8994363201565363983206279 13491544802348045974809419)
              ·
                refine ⟨20237317203522068962214129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13491544802348045974809419 20237317203522068962214129)
                ·
                  refine ⟨15177987902641551721660597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20237317203522068962214129 15177987902641551721660597)
                  ·
                    refine ⟨1422936365872645473905681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15177987902641551721660597 1422936365872645473905681)
                    ·
                      refine ⟨1067202274404484105429261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1422936365872645473905681 1067202274404484105429261)
                      ·
                        rfl

theorem cell23_2078369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_2078369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078369 prefixEnd_2078369 := by exact prefixLift 2078369
  have htrace : WordTrace (prefixWord ++ tailWord_2078369) baseStart_2078369 baseEnd_2078369 := by
    simpa [prefixWord, tailWord_2078369, baseEnd_2078369] using wordTrace_append hprefix tailTrace_2078369
  have hstable : (prefixWord ++ tailWord_2078369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078369).length < 2 ^ (prefixWord ++ tailWord_2078369).sum := by decide
  have hdescent : baseEnd_2078369 < baseStart_2078369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078372 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_2078372 : Nat := 118140960795 + 2078372 * 2 ^ 59
def prefixEnd_2078372 : Nat := 4983230072969 + 3 ^ 40 * 2078372 * 2
def baseEnd_2078372 : Nat := 1067203814846447593691747

theorem tailTrace_2078372 : CollatzResearch.WordTrace tailWord_2078372 prefixEnd_2078372 1067203814846447593691747 := by
  unfold tailWord_2078372
  simp only [CollatzResearch.WordTrace]
  refine ⟨37902227213210338261542685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50536302950947117682056913 37902227213210338261542685)
  ·
    refine ⟨14213335204953876848078507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37902227213210338261542685 14213335204953876848078507)
    ·
      refine ⟨21320002807430815272117761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14213335204953876848078507 21320002807430815272117761)
      ·
        refine ⟨15990002105573111454088321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21320002807430815272117761 15990002105573111454088321)
        ·
          refine ⟨11992501579179833590566241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15990002105573111454088321 11992501579179833590566241)
          ·
            refine ⟨8994376184384875192924681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11992501579179833590566241 8994376184384875192924681)
            ·
              refine ⟨6745782138288656394693511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8994376184384875192924681 6745782138288656394693511)
              ·
                refine ⟨10118673207432984592040267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6745782138288656394693511 10118673207432984592040267)
                ·
                  refine ⟨15178009811149476888060401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10118673207432984592040267 15178009811149476888060401)
                  ·
                    refine ⟨11383507358362107666045301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15178009811149476888060401 11383507358362107666045301)
                    ·
                      refine ⟨1067203814846447593691747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11383507358362107666045301 1067203814846447593691747)
                      ·
                        rfl

theorem cell23_2078372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_2078372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078372 prefixEnd_2078372 := by exact prefixLift 2078372
  have htrace : WordTrace (prefixWord ++ tailWord_2078372) baseStart_2078372 baseEnd_2078372 := by
    simpa [prefixWord, tailWord_2078372, baseEnd_2078372] using wordTrace_append hprefix tailTrace_2078372
  have hstable : (prefixWord ++ tailWord_2078372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078372).length < 2 ^ (prefixWord ++ tailWord_2078372).sum := by decide
  have hdescent : baseEnd_2078372 < baseStart_2078372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078395 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 6]
def baseStart_2078395 : Nat := 118140960795 + 2078395 * 2 ^ 59
def prefixEnd_2078395 : Nat := 4983230072969 + 3 ^ 40 * 2078395 * 2
def baseEnd_2078395 : Nat := 1067215624901501003704141

theorem tailTrace_2078395 : CollatzResearch.WordTrace tailWord_2078395 prefixEnd_2078395 1067215624901501003704141 := by
  unfold tailWord_2078395
  simp only [CollatzResearch.WordTrace]
  refine ⟨75805293305337351451172639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50536862203558234300781759 75805293305337351451172639)
  ·
    refine ⟨113707939958006027176758959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75805293305337351451172639 113707939958006027176758959)
    ·
      refine ⟨170561909937009040765138439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113707939958006027176758959 170561909937009040765138439)
      ·
        refine ⟨255842864905513561147707659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170561909937009040765138439 255842864905513561147707659)
        ·
          refine ⟨383764297358270341721561489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255842864905513561147707659 383764297358270341721561489)
          ·
            refine ⟨287823223018702756291171117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383764297358270341721561489 287823223018702756291171117)
            ·
              refine ⟨107933708632013533609189169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287823223018702756291171117 107933708632013533609189169)
              ·
                refine ⟨80950281474010150206891877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107933708632013533609189169 80950281474010150206891877)
                ·
                  refine ⟨15178177776376903163792227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80950281474010150206891877 15178177776376903163792227)
                  ·
                    refine ⟨22767266664565354745688341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15178177776376903163792227 22767266664565354745688341)
                    ·
                      refine ⟨1067215624901501003704141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22767266664565354745688341 1067215624901501003704141)
                      ·
                        rfl

theorem cell23_2078395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 6].length) (baseStart_2078395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078395 prefixEnd_2078395 := by exact prefixLift 2078395
  have htrace : WordTrace (prefixWord ++ tailWord_2078395) baseStart_2078395 baseEnd_2078395 := by
    simpa [prefixWord, tailWord_2078395, baseEnd_2078395] using wordTrace_append hprefix tailTrace_2078395
  have hstable : (prefixWord ++ tailWord_2078395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078395).length < 2 ^ (prefixWord ++ tailWord_2078395).sum := by decide
  have hdescent : baseEnd_2078395 < baseStart_2078395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078405 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 10]
def baseStart_2078405 : Nat := 118140960795 + 2078405 * 2 ^ 59
def prefixEnd_2078405 : Nat := 4983230072969 + 3 ^ 40 * 2078405 * 2
def baseEnd_2078405 : Nat := 118580084412005107175455

theorem tailTrace_2078405 : CollatzResearch.WordTrace tailWord_2078405 prefixEnd_2078405 118580084412005107175455 := by
  unfold tailWord_2078405
  simp only [CollatzResearch.WordTrace]
  refine ⟨75805658035301123159036669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50537105356867415439357779 75805658035301123159036669)
  ·
    refine ⟨28427121763237921184638751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75805658035301123159036669 28427121763237921184638751)
    ·
      refine ⟨42640682644856881776958127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28427121763237921184638751 42640682644856881776958127)
      ·
        refine ⟨63961023967285322665437191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42640682644856881776958127 63961023967285322665437191)
        ·
          refine ⟨95941535950927983998155787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63961023967285322665437191 95941535950927983998155787)
          ·
            refine ⟨143912303926391975997233681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95941535950927983998155787 143912303926391975997233681)
            ·
              refine ⟨107934227944793981997925261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143912303926391975997233681 107934227944793981997925261)
              ·
                refine ⟨40475335479297743249221973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107934227944793981997925261 40475335479297743249221973)
                ·
                  refine ⟨118580084412005107175455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 40475335479297743249221973 118580084412005107175455)
                  ·
                    rfl

theorem cell23_2078405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_2078405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078405 prefixEnd_2078405 := by exact prefixLift 2078405
  have htrace : WordTrace (prefixWord ++ tailWord_2078405) baseStart_2078405 baseEnd_2078405 := by
    simpa [prefixWord, tailWord_2078405, baseEnd_2078405] using wordTrace_append hprefix tailTrace_2078405
  have hstable : (prefixWord ++ tailWord_2078405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078405).length < 2 ^ (prefixWord ++ tailWord_2078405).sum := by decide
  have hdescent : baseEnd_2078405 < baseStart_2078405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078426 : List Nat := [3, 1, 1, 2, 2, 3, 2, 4, 1, 4]
def baseStart_2078426 : Nat := 118140960795 + 2078426 * 2 ^ 59
def prefixEnd_2078426 : Nat := 4983230072969 + 3 ^ 40 * 2078426 * 2
def baseEnd_2078426 : Nat := 355743847600596794138833

theorem tailTrace_2078426 : CollatzResearch.WordTrace tailWord_2078426 prefixEnd_2078426 355743847600596794138833 := by
  unfold tailWord_2078426
  simp only [CollatzResearch.WordTrace]
  refine ⟨18951605992056260936387783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50537615978816695830367421 18951605992056260936387783)
  ·
    refine ⟨28427408988084391404581675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18951605992056260936387783 28427408988084391404581675)
    ·
      refine ⟨42641113482126587106872513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28427408988084391404581675 42641113482126587106872513)
      ·
        refine ⟨31980835111594940330154385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42641113482126587106872513 31980835111594940330154385)
        ·
          refine ⟨23985626333696205247615789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31980835111594940330154385 23985626333696205247615789)
          ·
            refine ⟨8994609875136076967855921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23985626333696205247615789 8994609875136076967855921)
            ·
              refine ⟨6745957406352057725891941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8994609875136076967855921 6745957406352057725891941)
              ·
                refine ⟨1264867013691010823604739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6745957406352057725891941 1264867013691010823604739)
                ·
                  refine ⟨1897300520536516235407109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264867013691010823604739 1897300520536516235407109)
                  ·
                    refine ⟨355743847600596794138833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1897300520536516235407109 355743847600596794138833)
                    ·
                      rfl

theorem cell23_2078426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_2078426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078426 prefixEnd_2078426 := by exact prefixLift 2078426
  have htrace : WordTrace (prefixWord ++ tailWord_2078426) baseStart_2078426 baseEnd_2078426 := by
    simpa [prefixWord, tailWord_2078426, baseEnd_2078426] using wordTrace_append hprefix tailTrace_2078426
  have hstable : (prefixWord ++ tailWord_2078426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078426).length < 2 ^ (prefixWord ++ tailWord_2078426).sum := by decide
  have hdescent : baseEnd_2078426 < baseStart_2078426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078510 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_2078510 : Nat := 118140960795 + 2078510 * 2 ^ 59
def prefixEnd_2078510 : Nat := 4983230072969 + 3 ^ 40 * 2078510 * 2
def baseEnd_2078510 : Nat := 1067274675176768053766113

theorem tailTrace_2078510 : CollatzResearch.WordTrace tailWord_2078510 prefixEnd_2078510 1067274675176768053766113 := by
  unfold tailWord_2078510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9476185962490090761451123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50539658466613817394405989 9476185962490090761451123)
  ·
    refine ⟨14214278943735136142176685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9476185962490090761451123 14214278943735136142176685)
    ·
      refine ⟨5330354603900676053316257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14214278943735136142176685 5330354603900676053316257)
      ·
        refine ⟨3997765952925507039987193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5330354603900676053316257 3997765952925507039987193)
        ·
          refine ⟨2998324464694130279990395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3997765952925507039987193 2998324464694130279990395)
          ·
            refine ⟨4497486697041195419985593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2998324464694130279990395 4497486697041195419985593)
            ·
              refine ⟨3373115022780896564989195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4497486697041195419985593 3373115022780896564989195)
              ·
                refine ⟨5059672534171344847483793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373115022780896564989195 5059672534171344847483793)
                ·
                  refine ⟨3794754400628508635612845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5059672534171344847483793 3794754400628508635612845)
                  ·
                    refine ⟨1423032900235690738354817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3794754400628508635612845 1423032900235690738354817)
                    ·
                      refine ⟨1067274675176768053766113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1423032900235690738354817 1067274675176768053766113)
                      ·
                        rfl

theorem cell23_2078510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_2078510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078510 prefixEnd_2078510 := by exact prefixLift 2078510
  have htrace : WordTrace (prefixWord ++ tailWord_2078510) baseStart_2078510 baseEnd_2078510 := by
    simpa [prefixWord, tailWord_2078510, baseEnd_2078510] using wordTrace_append hprefix tailTrace_2078510
  have hstable : (prefixWord ++ tailWord_2078510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078510).length < 2 ^ (prefixWord ++ tailWord_2078510).sum := by decide
  have hdescent : baseEnd_2078510 < baseStart_2078510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078516 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_2078516 : Nat := 118140960795 + 2078516 * 2 ^ 59
def prefixEnd_2078516 : Nat := 4983230072969 + 3 ^ 40 * 2078516 * 2
def baseEnd_2078516 : Nat := 355759252020231676763695

theorem tailTrace_2078516 : CollatzResearch.WordTrace tailWord_2078516 prefixEnd_2078516 355759252020231676763695 := by
  unfold tailWord_2078516
  simp only [CollatzResearch.WordTrace]
  refine ⟨37904853268949494558163701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50539804358599326077551601 37904853268949494558163701)
  ·
    refine ⟨3553579993964015114827847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37904853268949494558163701 3553579993964015114827847)
    ·
      refine ⟨5330369990946022672241771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3553579993964015114827847 5330369990946022672241771)
      ·
        refine ⟨7995554986419034008362657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5330369990946022672241771 7995554986419034008362657)
        ·
          refine ⟨5996666239814275506271993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7995554986419034008362657 5996666239814275506271993)
          ·
            refine ⟨4497499679860706629703995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5996666239814275506271993 4497499679860706629703995)
            ·
              refine ⟨6746249519791059944555993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4497499679860706629703995 6746249519791059944555993)
              ·
                refine ⟨5059687139843294958416995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6746249519791059944555993 5059687139843294958416995)
                ·
                  refine ⟨7589530709764942437625493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059687139843294958416995 7589530709764942437625493)
                  ·
                    refine ⟨355759252020231676763695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7589530709764942437625493 355759252020231676763695)
                    ·
                      rfl

theorem cell23_2078516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_2078516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078516 prefixEnd_2078516 := by exact prefixLift 2078516
  have htrace : WordTrace (prefixWord ++ tailWord_2078516) baseStart_2078516 baseEnd_2078516 := by
    simpa [prefixWord, tailWord_2078516, baseEnd_2078516] using wordTrace_append hprefix tailTrace_2078516
  have hstable : (prefixWord ++ tailWord_2078516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078516).length < 2 ^ (prefixWord ++ tailWord_2078516).sum := by decide
  have hdescent : baseEnd_2078516 < baseStart_2078516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078526 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_2078526 : Nat := 118140960795 + 2078526 * 2 ^ 59
def prefixEnd_2078526 : Nat := 4983230072969 + 3 ^ 40 * 2078526 * 2
def baseEnd_2078526 : Nat := 1067282890867239991166039

theorem tailTrace_2078526 : CollatzResearch.WordTrace tailWord_2078526 prefixEnd_2078526 1067282890867239991166039 := by
  unfold tailWord_2078526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9476258908482845103023929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50540047511908507216127621 9476258908482845103023929)
  ·
    refine ⟨7107194181362133827267947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9476258908482845103023929 7107194181362133827267947)
    ·
      refine ⟨10660791272043200740901921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7107194181362133827267947 10660791272043200740901921)
      ·
        refine ⟨7995593454032400555676441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10660791272043200740901921 7995593454032400555676441)
        ·
          refine ⟨5996695090524300416757331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7995593454032400555676441 5996695090524300416757331)
          ·
            refine ⟨8995042635786450625135997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996695090524300416757331 8995042635786450625135997)
            ·
              refine ⟨3373140988419918984425999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8995042635786450625135997 3373140988419918984425999)
              ·
                refine ⟨5059711482629878476638999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373140988419918984425999 5059711482629878476638999)
                ·
                  refine ⟨7589567223944817714958499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059711482629878476638999 7589567223944817714958499)
                  ·
                    refine ⟨11384350835917226572437749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7589567223944817714958499 11384350835917226572437749)
                    ·
                      refine ⟨1067282890867239991166039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11384350835917226572437749 1067282890867239991166039)
                      ·
                        rfl

theorem cell23_2078526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_2078526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078526 prefixEnd_2078526 := by exact prefixLift 2078526
  have htrace : WordTrace (prefixWord ++ tailWord_2078526) baseStart_2078526 baseEnd_2078526 := by
    simpa [prefixWord, tailWord_2078526, baseEnd_2078526] using wordTrace_append hprefix tailTrace_2078526
  have hstable : (prefixWord ++ tailWord_2078526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078526).length < 2 ^ (prefixWord ++ tailWord_2078526).sum := by decide
  have hdescent : baseEnd_2078526 < baseStart_2078526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078534 : List Nat := [6, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_2078534 : Nat := 118140960795 + 2078534 * 2 ^ 59
def prefixEnd_2078534 : Nat := 4983230072969 + 3 ^ 40 * 2078534 * 2
def baseEnd_2078534 : Nat := 1067286998712475959866003

theorem tailTrace_2078534 : CollatzResearch.WordTrace tailWord_2078534 prefixEnd_2078534 1067286998712475959866003 := by
  unfold tailWord_2078534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2369073845369805568452583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50540242034555852126988437 2369073845369805568452583)
  ·
    refine ⟨3553610768054708352678875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2369073845369805568452583 3553610768054708352678875)
    ·
      refine ⟨5330416152082062529018313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3553610768054708352678875 5330416152082062529018313)
      ·
        refine ⟨3997812114061546896763735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5330416152082062529018313 3997812114061546896763735)
        ·
          refine ⟨5996718171092320345145603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3997812114061546896763735 5996718171092320345145603)
          ·
            refine ⟨8995077256638480517718405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996718171092320345145603 8995077256638480517718405)
            ·
              refine ⟨1686576985619715097072201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8995077256638480517718405 1686576985619715097072201)
              ·
                refine ⟨1264932739214786322804151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1686576985619715097072201 1264932739214786322804151)
                ·
                  refine ⟨1897399108822179484206227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264932739214786322804151 1897399108822179484206227)
                  ·
                    refine ⟨2846098663233269226309341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1897399108822179484206227 2846098663233269226309341)
                    ·
                      refine ⟨1067286998712475959866003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2846098663233269226309341 1067286998712475959866003)
                      ·
                        rfl

theorem cell23_2078534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_2078534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078534 prefixEnd_2078534 := by exact prefixLift 2078534
  have htrace : WordTrace (prefixWord ++ tailWord_2078534) baseStart_2078534 baseEnd_2078534 := by
    simpa [prefixWord, tailWord_2078534, baseEnd_2078534] using wordTrace_append hprefix tailTrace_2078534
  have hstable : (prefixWord ++ tailWord_2078534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078534).length < 2 ^ (prefixWord ++ tailWord_2078534).sum := by decide
  have hdescent : baseEnd_2078534 < baseStart_2078534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078552 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_2078552 : Nat := 118140960795 + 2078552 * 2 ^ 59
def prefixEnd_2078552 : Nat := 4983230072969 + 3 ^ 40 * 2078552 * 2
def baseEnd_2078552 : Nat := 1067296241364256889440919

theorem tailTrace_2078552 : CollatzResearch.WordTrace tailWord_2078552 prefixEnd_2078552 1067296241364256889440919 := by
  unfold tailWord_2078552
  simp only [CollatzResearch.WordTrace]
  refine ⟨37905509782884283632318955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50540679710512378176425273 37905509782884283632318955)
  ·
    refine ⟨56858264674326425448478433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37905509782884283632318955 56858264674326425448478433)
    ·
      refine ⟨42643698505744819086358825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56858264674326425448478433 42643698505744819086358825)
      ·
        refine ⟨31982773879308614314769119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42643698505744819086358825 31982773879308614314769119)
        ·
          refine ⟨47974160818962921472153679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31982773879308614314769119 47974160818962921472153679)
          ·
            refine ⟨71961241228444382208230519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47974160818962921472153679 71961241228444382208230519)
            ·
              refine ⟨107941861842666573312345779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71961241228444382208230519 107941861842666573312345779)
              ·
                refine ⟨161912792763999859968518669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107941861842666573312345779 161912792763999859968518669)
                ·
                  refine ⟨60717297286499947488194501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161912792763999859968518669 60717297286499947488194501)
                  ·
                    refine ⟨11384493241218740154036469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60717297286499947488194501 11384493241218740154036469)
                    ·
                      refine ⟨1067296241364256889440919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11384493241218740154036469 1067296241364256889440919)
                      ·
                        rfl

theorem cell23_2078552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_2078552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078552 prefixEnd_2078552 := by exact prefixLift 2078552
  have htrace : WordTrace (prefixWord ++ tailWord_2078552) baseStart_2078552 baseEnd_2078552 := by
    simpa [prefixWord, tailWord_2078552, baseEnd_2078552] using wordTrace_append hprefix tailTrace_2078552
  have hstable : (prefixWord ++ tailWord_2078552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078552).length < 2 ^ (prefixWord ++ tailWord_2078552).sum := by decide
  have hdescent : baseEnd_2078552 < baseStart_2078552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078590 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2078590 : Nat := 118140960795 + 2078590 * 2 ^ 59
def prefixEnd_2078590 : Nat := 4983230072969 + 3 ^ 40 * 2078590 * 2
def baseEnd_2078590 : Nat := 1067315753629127740765745

theorem tailTrace_2078590 : CollatzResearch.WordTrace tailWord_2078590 prefixEnd_2078590 1067315753629127740765745 := by
  unfold tailWord_2078590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9476550692453862469315153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50541603693087266503014149 9476550692453862469315153)
  ·
    refine ⟨7107413019340396851986365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9476550692453862469315153 7107413019340396851986365)
    ·
      refine ⟨2665279882252648819494887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7107413019340396851986365 2665279882252648819494887)
      ·
        refine ⟨3997919823378973229242331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2665279882252648819494887 3997919823378973229242331)
        ·
          refine ⟨5996879735068459843863497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3997919823378973229242331 5996879735068459843863497)
          ·
            refine ⟨4497659801301344882897623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5996879735068459843863497 4497659801301344882897623)
            ·
              refine ⟨6746489701952017324346435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4497659801301344882897623 6746489701952017324346435)
              ·
                refine ⟨10119734552928025986519653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6746489701952017324346435 10119734552928025986519653)
                ·
                  refine ⟨1897450228674004872472435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10119734552928025986519653 1897450228674004872472435)
                  ·
                    refine ⟨2846175343011007308708653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1897450228674004872472435 2846175343011007308708653)
                    ·
                      refine ⟨1067315753629127740765745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2846175343011007308708653 1067315753629127740765745)
                      ·
                        rfl

theorem cell23_2078590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2078590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078590 prefixEnd_2078590 := by exact prefixLift 2078590
  have htrace : WordTrace (prefixWord ++ tailWord_2078590) baseStart_2078590 baseEnd_2078590 := by
    simpa [prefixWord, tailWord_2078590, baseEnd_2078590] using wordTrace_append hprefix tailTrace_2078590
  have hstable : (prefixWord ++ tailWord_2078590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078590).length < 2 ^ (prefixWord ++ tailWord_2078590).sum := by decide
  have hdescent : baseEnd_2078590 < baseStart_2078590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078596 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_2078596 : Nat := 118140960795 + 2078596 * 2 ^ 59
def prefixEnd_2078596 : Nat := 4983230072969 + 3 ^ 40 * 2078596 * 2
def baseEnd_2078596 : Nat := 1067318834513054717290717

theorem tailTrace_2078596 : CollatzResearch.WordTrace tailWord_2078596 prefixEnd_2078596 1067318834513054717290717 := by
  unfold tailWord_2078596
  simp only [CollatzResearch.WordTrace]
  refine ⟨37906312188804581389619821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50541749585072775186159761 37906312188804581389619821)
  ·
    refine ⟨14214867070801718021107433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37906312188804581389619821 14214867070801718021107433)
    ·
      refine ⟨10661150303101288515830575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14214867070801718021107433 10661150303101288515830575)
      ·
        refine ⟨15991725454651932773745863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10661150303101288515830575 15991725454651932773745863)
        ·
          refine ⟨23987588181977899160618795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15991725454651932773745863 23987588181977899160618795)
          ·
            refine ⟨35981382272966848740928193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23987588181977899160618795 35981382272966848740928193)
            ·
              refine ⟨26986036704725136555696145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35981382272966848740928193 26986036704725136555696145)
              ·
                refine ⟨20239527528543852416772109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26986036704725136555696145 20239527528543852416772109)
                ·
                  refine ⟨7589822823203944656289541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20239527528543852416772109 7589822823203944656289541)
                  ·
                    refine ⟨1423091779350739623054289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7589822823203944656289541 1423091779350739623054289)
                    ·
                      refine ⟨1067318834513054717290717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1423091779350739623054289 1067318834513054717290717)
                      ·
                        rfl

theorem cell23_2078596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_2078596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078596 prefixEnd_2078596 := by exact prefixLift 2078596
  have htrace : WordTrace (prefixWord ++ tailWord_2078596) baseStart_2078596 baseEnd_2078596 := by
    simpa [prefixWord, tailWord_2078596, baseEnd_2078596] using wordTrace_append hprefix tailTrace_2078596
  have hstable : (prefixWord ++ tailWord_2078596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078596).length < 2 ^ (prefixWord ++ tailWord_2078596).sum := by decide
  have hdescent : baseEnd_2078596 < baseStart_2078596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078609 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_2078609 : Nat := 118140960795 + 2078609 * 2 ^ 59
def prefixEnd_2078609 : Nat := 4983230072969 + 3 ^ 40 * 2078609 * 2
def baseEnd_2078609 : Nat := 1067325509761563166428157

theorem tailTrace_2078609 : CollatzResearch.WordTrace tailWord_2078609 prefixEnd_2078609 1067325509761563166428157 := by
  unfold tailWord_2078609
  simp only [CollatzResearch.WordTrace]
  refine ⟨75813098526562065999462881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50542065684374710666308587 75813098526562065999462881)
  ·
    refine ⟨56859823894921549499597161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75813098526562065999462881 56859823894921549499597161)
    ·
      refine ⟨42644867921191162124697871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56859823894921549499597161 42644867921191162124697871)
      ·
        refine ⟨63967301881786743187046807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42644867921191162124697871 63967301881786743187046807)
        ·
          refine ⟨95950952822680114780570211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63967301881786743187046807 95950952822680114780570211)
          ·
            refine ⟨143926429234020172170855317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95950952822680114780570211 143926429234020172170855317)
            ·
              refine ⟨6746551370344695570508843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143926429234020172170855317 6746551370344695570508843)
              ·
                refine ⟨10119827055517043355763265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6746551370344695570508843 10119827055517043355763265)
                ·
                  refine ⟨7589870291637782516822449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10119827055517043355763265 7589870291637782516822449)
                  ·
                    refine ⟨5692402718728336887616837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7589870291637782516822449 5692402718728336887616837)
                    ·
                      refine ⟨1067325509761563166428157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5692402718728336887616837 1067325509761563166428157)
                      ·
                        rfl

theorem cell23_2078609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_2078609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078609 prefixEnd_2078609 := by exact prefixLift 2078609
  have htrace : WordTrace (prefixWord ++ tailWord_2078609) baseStart_2078609 baseEnd_2078609 := by
    simpa [prefixWord, tailWord_2078609, baseEnd_2078609] using wordTrace_append hprefix tailTrace_2078609
  have hstable : (prefixWord ++ tailWord_2078609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078609).length < 2 ^ (prefixWord ++ tailWord_2078609).sum := by decide
  have hdescent : baseEnd_2078609 < baseStart_2078609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078629 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 1, 5, 3]
def baseStart_2078629 : Nat := 118140960795 + 2078629 * 2 ^ 59
def prefixEnd_2078629 : Nat := 4983230072969 + 3 ^ 40 * 2078629 * 2
def baseEnd_2078629 : Nat := 1067335779374653088178065

theorem tailTrace_2078629 : CollatzResearch.WordTrace tailWord_2078629 prefixEnd_2078629 1067335779374653088178065 := by
  unfold tailWord_2078629
  simp only [CollatzResearch.WordTrace]
  refine ⟨75813827986489609415190941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50542551990993072943460627 75813827986489609415190941)
  ·
    refine ⟨28430185494933603530696603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75813827986489609415190941 28430185494933603530696603)
    ·
      refine ⟨42645278242400405296044905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28430185494933603530696603 42645278242400405296044905)
      ·
        refine ⟨31983958681800303972033679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42645278242400405296044905 31983958681800303972033679)
        ·
          refine ⟨47975938022700455958050519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31983958681800303972033679 47975938022700455958050519)
          ·
            refine ⟨71963907034050683937075779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47975938022700455958050519 71963907034050683937075779)
            ·
              refine ⟨107945860551076025905613669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71963907034050683937075779 107945860551076025905613669)
              ·
                refine ⟨20239848853326754857302563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107945860551076025905613669 20239848853326754857302563)
                ·
                  refine ⟨30359773279990132285953845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20239848853326754857302563 30359773279990132285953845)
                  ·
                    refine ⟨2846228744999074901808173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30359773279990132285953845 2846228744999074901808173)
                    ·
                      refine ⟨1067335779374653088178065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2846228744999074901808173 1067335779374653088178065)
                      ·
                        rfl

theorem cell23_2078629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_2078629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078629 prefixEnd_2078629 := by exact prefixLift 2078629
  have htrace : WordTrace (prefixWord ++ tailWord_2078629) baseStart_2078629 baseEnd_2078629 := by
    simpa [prefixWord, tailWord_2078629, baseEnd_2078629] using wordTrace_append hprefix tailTrace_2078629
  have hstable : (prefixWord ++ tailWord_2078629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078629).length < 2 ^ (prefixWord ++ tailWord_2078629).sum := by decide
  have hdescent : baseEnd_2078629 < baseStart_2078629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078656 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 2, 5, 2]
def baseStart_2078656 : Nat := 118140960795 + 2078656 * 2 ^ 59
def prefixEnd_2078656 : Nat := 4983230072969 + 3 ^ 40 * 2078656 * 2
def baseEnd_2078656 : Nat := 1067349643352324482540441

theorem tailTrace_2078656 : CollatzResearch.WordTrace tailWord_2078656 prefixEnd_2078656 1067349643352324482540441 := by
  unfold tailWord_2078656
  simp only [CollatzResearch.WordTrace]
  refine ⟨37907406378695896513211911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50543208504927862017615881 37907406378695896513211911)
  ·
    refine ⟨56861109568043844769817867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37907406378695896513211911 56861109568043844769817867)
    ·
      refine ⟨85291664352065767154726801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56861109568043844769817867 85291664352065767154726801)
      ·
        refine ⟨63968748264049325366045101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85291664352065767154726801 63968748264049325366045101)
        ·
          refine ⟨23988280599018497012266913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63968748264049325366045101 23988280599018497012266913)
          ·
            refine ⟨17991210449263872759200185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23988280599018497012266913 17991210449263872759200185)
            ·
              refine ⟨13493407836947904569400139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17991210449263872759200185 13493407836947904569400139)
              ·
                refine ⟨20240111755421856854100209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13493407836947904569400139 20240111755421856854100209)
                ·
                  refine ⟨15180083816566392640575157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20240111755421856854100209 15180083816566392640575157)
                  ·
                    refine ⟨1423132857803099310053921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15180083816566392640575157 1423132857803099310053921)
                    ·
                      refine ⟨1067349643352324482540441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1423132857803099310053921 1067349643352324482540441)
                      ·
                        rfl

theorem cell23_2078656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 5, 2].length) (baseStart_2078656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078656 prefixEnd_2078656 := by exact prefixLift 2078656
  have htrace : WordTrace (prefixWord ++ tailWord_2078656) baseStart_2078656 baseEnd_2078656 := by
    simpa [prefixWord, tailWord_2078656, baseEnd_2078656] using wordTrace_append hprefix tailTrace_2078656
  have hstable : (prefixWord ++ tailWord_2078656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078656).length < 2 ^ (prefixWord ++ tailWord_2078656).sum := by decide
  have hdescent : baseEnd_2078656 < baseStart_2078656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078770 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_2078770 : Nat := 118140960795 + 2078770 * 2 ^ 59
def prefixEnd_2078770 : Nat := 4983230072969 + 3 ^ 40 * 2078770 * 2
def baseEnd_2078770 : Nat := 1067408180146937036514917

theorem tailTrace_2078770 : CollatzResearch.WordTrace tailWord_2078770 prefixEnd_2078770 1067408180146937036514917 := by
  unfold tailWord_2078770
  simp only [CollatzResearch.WordTrace]
  refine ⟨18954742669744697624018441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50545980452652526997382509 18954742669744697624018441)
  ·
    refine ⟨14216057002308523218013831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18954742669744697624018441 14216057002308523218013831)
    ·
      refine ⟨21324085503462784827020747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14216057002308523218013831 21324085503462784827020747)
      ·
        refine ⟨31986128255194177240531121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21324085503462784827020747 31986128255194177240531121)
        ·
          refine ⟨23989596191395632930398341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31986128255194177240531121 23989596191395632930398341)
          ·
            refine ⟨4498049285886681174449689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23989596191395632930398341 4498049285886681174449689)
            ·
              refine ⟨3373536964415010880837267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4498049285886681174449689 3373536964415010880837267)
              ·
                refine ⟨5060305446622516321255901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373536964415010880837267 5060305446622516321255901)
                ·
                  refine ⟨1897614542483443620470963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5060305446622516321255901 1897614542483443620470963)
                  ·
                    refine ⟨2846421813725165430706445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1897614542483443620470963 2846421813725165430706445)
                    ·
                      refine ⟨1067408180146937036514917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2846421813725165430706445 1067408180146937036514917)
                      ·
                        rfl

theorem cell23_2078770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_2078770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078770 prefixEnd_2078770 := by exact prefixLift 2078770
  have htrace : WordTrace (prefixWord ++ tailWord_2078770) baseStart_2078770 baseEnd_2078770 := by
    simpa [prefixWord, tailWord_2078770, baseEnd_2078770] using wordTrace_append hprefix tailTrace_2078770
  have hstable : (prefixWord ++ tailWord_2078770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078770).length < 2 ^ (prefixWord ++ tailWord_2078770).sum := by decide
  have hdescent : baseEnd_2078770 < baseStart_2078770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078793 : List Nat := [1, 2, 1, 1, 2, 2, 6, 2, 1, 1, 4]
def baseStart_2078793 : Nat := 118140960795 + 2078793 * 2 ^ 59
def prefixEnd_2078793 : Nat := 4983230072969 + 3 ^ 40 * 2078793 * 2
def baseEnd_2078793 : Nat := 1067419990201990446527311

theorem tailTrace_2078793 : CollatzResearch.WordTrace tailWord_2078793 prefixEnd_2078793 1067419990201990446527311 := by
  unfold tailWord_2078793
  simp only [CollatzResearch.WordTrace]
  refine ⟨75819809557895465424161033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50546539705263643616107355 75819809557895465424161033)
  ·
    refine ⟨56864857168421599068120775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75819809557895465424161033 56864857168421599068120775)
    ·
      refine ⟨85297285752632398602181163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56864857168421599068120775 85297285752632398602181163)
      ·
        refine ⟨127945928628948597903271745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85297285752632398602181163 127945928628948597903271745)
        ·
          refine ⟨95959446471711448427453809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127945928628948597903271745 95959446471711448427453809)
          ·
            refine ⟨71969584853783586320590357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95959446471711448427453809 71969584853783586320590357)
            ·
              refine ⟨3373574290021105608777673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71969584853783586320590357 3373574290021105608777673)
              ·
                refine ⟨2530180717515829206583255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3373574290021105608777673 2530180717515829206583255)
                ·
                  refine ⟨3795271076273743809874883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530180717515829206583255 3795271076273743809874883)
                  ·
                    refine ⟨5692906614410615714812325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3795271076273743809874883 5692906614410615714812325)
                    ·
                      refine ⟨1067419990201990446527311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5692906614410615714812325 1067419990201990446527311)
                      ·
                        rfl

theorem cell23_2078793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 1, 4].length) (baseStart_2078793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078793 prefixEnd_2078793 := by exact prefixLift 2078793
  have htrace : WordTrace (prefixWord ++ tailWord_2078793) baseStart_2078793 baseEnd_2078793 := by
    simpa [prefixWord, tailWord_2078793, baseEnd_2078793] using wordTrace_append hprefix tailTrace_2078793
  have hstable : (prefixWord ++ tailWord_2078793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078793).length < 2 ^ (prefixWord ++ tailWord_2078793).sum := by decide
  have hdescent : baseEnd_2078793 < baseStart_2078793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078799 : List Nat := [1, 1, 2, 1, 1, 2, 2, 13]
def baseStart_2078799 : Nat := 118140960795 + 2078799 * 2 ^ 59
def prefixEnd_2078799 : Nat := 4983230072969 + 3 ^ 40 * 2078799 * 2
def baseEnd_2078799 : Nat := 39534187817996941594529

theorem tailTrace_2078799 : CollatzResearch.WordTrace tailWord_2078799 prefixEnd_2078799 39534187817996941594529 := by
  unfold tailWord_2078799
  simp only [CollatzResearch.WordTrace]
  refine ⟨75820028395873728448879451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50546685597249152299252967 75820028395873728448879451)
  ·
    refine ⟨113730042593810592673319177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75820028395873728448879451 113730042593810592673319177)
    ·
      refine ⟨85297531945357944504989383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113730042593810592673319177 85297531945357944504989383)
      ·
        refine ⟨127946297918036916757484075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85297531945357944504989383 127946297918036916757484075)
        ·
          refine ⟨191919446877055375136226113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127946297918036916757484075 191919446877055375136226113)
          ·
            refine ⟨143939585157791531352169585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191919446877055375136226113 143939585157791531352169585)
            ·
              refine ⟨107954688868343648514127189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143939585157791531352169585 107954688868343648514127189)
              ·
                refine ⟨39534187817996941594529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 107954688868343648514127189 39534187817996941594529)
                ·
                  rfl

theorem cell23_2078799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 13].length) (baseStart_2078799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078799 prefixEnd_2078799 := by exact prefixLift 2078799
  have htrace : WordTrace (prefixWord ++ tailWord_2078799) baseStart_2078799 baseEnd_2078799 := by
    simpa [prefixWord, tailWord_2078799, baseEnd_2078799] using wordTrace_append hprefix tailTrace_2078799
  have hstable : (prefixWord ++ tailWord_2078799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078799).length < 2 ^ (prefixWord ++ tailWord_2078799).sum := by decide
  have hdescent : baseEnd_2078799 < baseStart_2078799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078816 : List Nat := [2, 1, 1, 3, 2, 5, 9]
def baseStart_2078816 : Nat := 118140960795 + 2078816 * 2 ^ 59
def prefixEnd_2078816 : Nat := 4983230072969 + 3 ^ 40 * 2078816 * 2
def baseEnd_2078816 : Nat := 13178170373543751315305

theorem tailTrace_2078816 : CollatzResearch.WordTrace tailWord_2078816 prefixEnd_2078816 13178170373543751315305 := by
  unfold tailWord_2078816
  simp only [CollatzResearch.WordTrace]
  refine ⟨37910324218406070176124151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50547098957874760234832201 37910324218406070176124151)
  ·
    refine ⟨56865486327609105264186227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37910324218406070176124151 56865486327609105264186227)
    ·
      refine ⟨85298229491413657896279341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56865486327609105264186227 85298229491413657896279341)
      ·
        refine ⟨31986836059280121711104753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85298229491413657896279341 31986836059280121711104753)
        ·
          refine ⟨23990127044460091283328565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31986836059280121711104753 23990127044460091283328565)
          ·
            refine ⟨2249074410418133557812053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23990127044460091283328565 2249074410418133557812053)
            ·
              refine ⟨13178170373543751315305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2249074410418133557812053 13178170373543751315305)
              ·
                rfl

theorem cell23_2078816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 9].length) (baseStart_2078816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078816 prefixEnd_2078816 := by exact prefixLift 2078816
  have htrace : WordTrace (prefixWord ++ tailWord_2078816) baseStart_2078816 baseEnd_2078816 := by
    simpa [prefixWord, tailWord_2078816, baseEnd_2078816] using wordTrace_append hprefix tailTrace_2078816
  have hstable : (prefixWord ++ tailWord_2078816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078816).length < 2 ^ (prefixWord ++ tailWord_2078816).sum := by decide
  have hdescent : baseEnd_2078816 < baseStart_2078816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078877 : List Nat := [1, 4, 2, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_2078877 : Nat := 118140960795 + 2078877 * 2 ^ 59
def prefixEnd_2078877 : Nat := 4983230072969 + 3 ^ 40 * 2078877 * 2
def baseEnd_2078877 : Nat := 1067463122576968117876925

theorem tailTrace_2078877 : CollatzResearch.WordTrace tailWord_2078877 prefixEnd_2078877 1067463122576968117876925 := by
  unfold tailWord_2078877
  simp only [CollatzResearch.WordTrace]
  refine ⟨75822873289591147770218885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50548582193060765180145923 75822873289591147770218885)
  ·
    refine ⟨14216788741798340206916041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75822873289591147770218885 14216788741798340206916041)
    ·
      refine ⟨10662591556348755155187031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14216788741798340206916041 10662591556348755155187031)
      ·
        refine ⟨15993887334523132732780547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10662591556348755155187031 15993887334523132732780547)
        ·
          refine ⟨23990831001784699099170821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15993887334523132732780547 23990831001784699099170821)
          ·
            refine ⟨4498280812834631081094529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23990831001784699099170821 4498280812834631081094529)
            ·
              refine ⟨3373710609625973310820897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4498280812834631081094529 3373710609625973310820897)
              ·
                refine ⟨2530282957219479983115673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3373710609625973310820897 2530282957219479983115673)
                ·
                  refine ⟨1897712217914609987336755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2530282957219479983115673 1897712217914609987336755)
                  ·
                    refine ⟨2846568326871914981005133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1897712217914609987336755 2846568326871914981005133)
                    ·
                      refine ⟨1067463122576968117876925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2846568326871914981005133 1067463122576968117876925)
                      ·
                        rfl

theorem cell23_2078877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_2078877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078877 prefixEnd_2078877 := by exact prefixLift 2078877
  have htrace : WordTrace (prefixWord ++ tailWord_2078877) baseStart_2078877 baseEnd_2078877 := by
    simpa [prefixWord, tailWord_2078877, baseEnd_2078877] using wordTrace_append hprefix tailTrace_2078877
  have hstable : (prefixWord ++ tailWord_2078877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078877).length < 2 ^ (prefixWord ++ tailWord_2078877).sum := by decide
  have hdescent : baseEnd_2078877 < baseStart_2078877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078893 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2078893 : Nat := 118140960795 + 2078893 * 2 ^ 59
def prefixEnd_2078893 : Nat := 4983230072969 + 3 ^ 40 * 2078893 * 2
def baseEnd_2078893 : Nat := 355823779422480018425617

theorem tailTrace_2078893 : CollatzResearch.WordTrace tailWord_2078893 prefixEnd_2078893 355823779422480018425617 := by
  unfold tailWord_2078893
  simp only [CollatzResearch.WordTrace]
  refine ⟨75823456857533182502801333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50548971238355455001867555 75823456857533182502801333)
  ·
    refine ⟨7108449080393735859637625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75823456857533182502801333 7108449080393735859637625)
    ·
      refine ⟨5331336810295301894728219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7108449080393735859637625 5331336810295301894728219)
      ·
        refine ⟨7997005215442952842092329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5331336810295301894728219 7997005215442952842092329)
        ·
          refine ⟨5997753911582214631569247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7997005215442952842092329 5997753911582214631569247)
          ·
            refine ⟨8996630867373321947353871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5997753911582214631569247 8996630867373321947353871)
            ·
              refine ⟨13494946301059982921030807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996630867373321947353871 13494946301059982921030807)
              ·
                refine ⟨20242419451589974381546211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13494946301059982921030807 20242419451589974381546211)
                ·
                  refine ⟨30363629177384961572319317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20242419451589974381546211 30363629177384961572319317)
                  ·
                    refine ⟨355823779422480018425617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30363629177384961572319317 355823779422480018425617)
                    ·
                      rfl

theorem cell23_2078893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2078893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078893 prefixEnd_2078893 := by exact prefixLift 2078893
  have htrace : WordTrace (prefixWord ++ tailWord_2078893) baseStart_2078893 baseEnd_2078893 := by
    simpa [prefixWord, tailWord_2078893, baseEnd_2078893] using wordTrace_append hprefix tailTrace_2078893
  have hstable : (prefixWord ++ tailWord_2078893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078893).length < 2 ^ (prefixWord ++ tailWord_2078893).sum := by decide
  have hdescent : baseEnd_2078893 < baseStart_2078893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078894 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2078894 : Nat := 118140960795 + 2078894 * 2 ^ 59
def prefixEnd_2078894 : Nat := 4983230072969 + 3 ^ 40 * 2078894 * 2
def baseEnd_2078894 : Nat := 1067471851748094551364347

theorem tailTrace_2078894 : CollatzResearch.WordTrace tailWord_2078894 prefixEnd_2078894 1067471851748094551364347 := by
  unfold tailWord_2078894
  simp only [CollatzResearch.WordTrace]
  refine ⟨9477936666316194959198467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50548995553686373115725157 9477936666316194959198467)
  ·
    refine ⟨14216904999474292438797701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9477936666316194959198467 14216904999474292438797701)
    ·
      refine ⟨2665669687401429832274569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14216904999474292438797701 2665669687401429832274569)
      ·
        refine ⟨1999252265551072374205927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2665669687401429832274569 1999252265551072374205927)
        ·
          refine ⟨2998878398326608561308891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999252265551072374205927 2998878398326608561308891)
          ·
            refine ⟨4498317597489912841963337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2998878398326608561308891 4498317597489912841963337)
            ·
              refine ⟨3373738198117434631472503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4498317597489912841963337 3373738198117434631472503)
              ·
                refine ⟨5060607297176151947208755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373738198117434631472503 5060607297176151947208755)
                ·
                  refine ⟨7590910945764227920813133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5060607297176151947208755 7590910945764227920813133)
                  ·
                    refine ⟨2846591604661585470304925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7590910945764227920813133 2846591604661585470304925)
                    ·
                      refine ⟨1067471851748094551364347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2846591604661585470304925 1067471851748094551364347)
                      ·
                        rfl

theorem cell23_2078894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2078894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078894 prefixEnd_2078894 := by exact prefixLift 2078894
  have htrace : WordTrace (prefixWord ++ tailWord_2078894) baseStart_2078894 baseEnd_2078894 := by
    simpa [prefixWord, tailWord_2078894, baseEnd_2078894] using wordTrace_append hprefix tailTrace_2078894
  have hstable : (prefixWord ++ tailWord_2078894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078894).length < 2 ^ (prefixWord ++ tailWord_2078894).sum := by decide
  have hdescent : baseEnd_2078894 < baseStart_2078894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078906 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 9]
def baseStart_2078906 : Nat := 118140960795 + 2078906 * 2 ^ 59
def prefixEnd_2078906 : Nat := 4983230072969 + 3 ^ 40 * 2078906 * 2
def baseEnd_2078906 : Nat := 118608668168438722712699

theorem tailTrace_2078906 : CollatzResearch.WordTrace tailWord_2078906 prefixEnd_2078906 118608668168438722712699 := by
  unfold tailWord_2078906
  simp only [CollatzResearch.WordTrace]
  refine ⟨18955982751621521430756143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50549287337657390482016381 18955982751621521430756143)
  ·
    refine ⟨28433974127432282146134215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18955982751621521430756143 28433974127432282146134215)
    ·
      refine ⟨42650961191148423219201323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28433974127432282146134215 42650961191148423219201323)
      ·
        refine ⟨63976441786722634828801985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42650961191148423219201323 63976441786722634828801985)
        ·
          refine ⟨47982331340041976121601489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63976441786722634828801985 47982331340041976121601489)
          ·
            refine ⟨35986748505031482091201117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47982331340041976121601489 35986748505031482091201117)
            ·
              refine ⟨13495030689386805784200419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35986748505031482091201117 13495030689386805784200419)
              ·
                refine ⟨20242546034080208676300629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13495030689386805784200419 20242546034080208676300629)
                ·
                  refine ⟨118608668168438722712699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20242546034080208676300629 118608668168438722712699)
                  ·
                    rfl

theorem cell23_2078906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_2078906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078906 prefixEnd_2078906 := by exact prefixLift 2078906
  have htrace : WordTrace (prefixWord ++ tailWord_2078906) baseStart_2078906 baseEnd_2078906 := by
    simpa [prefixWord, tailWord_2078906, baseEnd_2078906] using wordTrace_append hprefix tailTrace_2078906
  have hstable : (prefixWord ++ tailWord_2078906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078906).length < 2 ^ (prefixWord ++ tailWord_2078906).sum := by decide
  have hdescent : baseEnd_2078906 < baseStart_2078906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078951 : List Nat := [1, 1, 5, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_2078951 : Nat := 118140960795 + 2078951 * 2 ^ 59
def prefixEnd_2078951 : Nat := 4983230072969 + 3 ^ 40 * 2078951 * 2
def baseEnd_2078951 : Nat := 1067501120145400828351585

theorem tailTrace_2078951 : CollatzResearch.WordTrace tailWord_2078951 prefixEnd_2078951 1067501120145400828351585 := by
  unfold tailWord_2078951
  simp only [CollatzResearch.WordTrace]
  refine ⟨75825572291323058408412707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50550381527548705605608471 75825572291323058408412707)
  ·
    refine ⟨113738358436984587612619061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75825572291323058408412707 113738358436984587612619061)
    ·
      refine ⟨10662971103467305088683037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113738358436984587612619061 10662971103467305088683037)
      ·
        refine ⟨3998614163800239408256139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10662971103467305088683037 3998614163800239408256139)
        ·
          refine ⟨5997921245700359112384209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3998614163800239408256139 5997921245700359112384209)
          ·
            refine ⟨4498440934275269334288157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5997921245700359112384209 4498440934275269334288157)
            ·
              refine ⟨1686915350353226000358059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4498440934275269334288157 1686915350353226000358059)
              ·
                refine ⟨2530373025529839000537089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1686915350353226000358059 2530373025529839000537089)
                ·
                  refine ⟨1897779769147379250402817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2530373025529839000537089 1897779769147379250402817)
                  ·
                    refine ⟨1423334826860534437802113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1897779769147379250402817 1423334826860534437802113)
                    ·
                      refine ⟨1067501120145400828351585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1423334826860534437802113 1067501120145400828351585)
                      ·
                        rfl

theorem cell23_2078951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_2078951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078951 prefixEnd_2078951 := by exact prefixLift 2078951
  have htrace : WordTrace (prefixWord ++ tailWord_2078951) baseStart_2078951 baseEnd_2078951 := by
    simpa [prefixWord, tailWord_2078951, baseEnd_2078951] using wordTrace_append hprefix tailTrace_2078951
  have hstable : (prefixWord ++ tailWord_2078951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078951).length < 2 ^ (prefixWord ++ tailWord_2078951).sum := by decide
  have hdescent : baseEnd_2078951 < baseStart_2078951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078973 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_2078973 : Nat := 118140960795 + 2078973 * 2 ^ 59
def prefixEnd_2078973 : Nat := 4983230072969 + 3 ^ 40 * 2078973 * 2
def baseEnd_2078973 : Nat := 1067512416719799742276483

theorem tailTrace_2078973 : CollatzResearch.WordTrace tailWord_2078973 prefixEnd_2078973 1067512416719799742276483 := by
  unfold tailWord_2078973
  simp only [CollatzResearch.WordTrace]
  refine ⟨75826374697243356165713573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50550916464828904110475715 75826374697243356165713573)
  ·
    refine ⟨14217445255733129281071295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75826374697243356165713573 14217445255733129281071295)
    ·
      refine ⟨21326167883599693921606943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14217445255733129281071295 21326167883599693921606943)
      ·
        refine ⟨31989251825399540882410415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21326167883599693921606943 31989251825399540882410415)
        ·
          refine ⟨47983877738099311323615623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31989251825399540882410415 47983877738099311323615623)
          ·
            refine ⟨71975816607148966985423435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47983877738099311323615623 71975816607148966985423435)
            ·
              refine ⟨107963724910723450478135153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71975816607148966985423435 107963724910723450478135153)
              ·
                refine ⟨80972793683042587858601365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107963724910723450478135153 80972793683042587858601365)
                ·
                  refine ⟨3795599703892621305871939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80972793683042587858601365 3795599703892621305871939)
                  ·
                    refine ⟨5693399555838931958807909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3795599703892621305871939 5693399555838931958807909)
                    ·
                      refine ⟨1067512416719799742276483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5693399555838931958807909 1067512416719799742276483)
                      ·
                        rfl

theorem cell23_2078973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_2078973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078973 prefixEnd_2078973 := by exact prefixLift 2078973
  have htrace : WordTrace (prefixWord ++ tailWord_2078973) baseStart_2078973 baseEnd_2078973 := by
    simpa [prefixWord, tailWord_2078973, baseEnd_2078973] using wordTrace_append hprefix tailTrace_2078973
  have hstable : (prefixWord ++ tailWord_2078973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078973).length < 2 ^ (prefixWord ++ tailWord_2078973).sum := by decide
  have hdescent : baseEnd_2078973 < baseStart_2078973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078990 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_2078990 : Nat := 118140960795 + 2078990 * 2 ^ 59
def prefixEnd_2078990 : Nat := 4983230072969 + 3 ^ 40 * 2078990 * 2
def baseEnd_2078990 : Nat := 1067521145890926175763905

theorem tailTrace_2078990 : CollatzResearch.WordTrace tailWord_2078990 prefixEnd_2078990 1067521145890926175763905 := by
  unfold tailWord_2078990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9478374342272721008635303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50551329825454512046054949 9478374342272721008635303)
  ·
    refine ⟨14217561513409081512952955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9478374342272721008635303 14217561513409081512952955)
    ·
      refine ⟨21326342270113622269429433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14217561513409081512952955 21326342270113622269429433)
      ·
        refine ⟨15994756702585216702072075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21326342270113622269429433 15994756702585216702072075)
        ·
          refine ⟨23992135053877825053108113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15994756702585216702072075 23992135053877825053108113)
          ·
            refine ⟨17994101290408368789831085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23992135053877825053108113 17994101290408368789831085)
            ·
              refine ⟨6747787983903138296186657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17994101290408368789831085 6747787983903138296186657)
              ·
                refine ⟨5060840987927353722139993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6747787983903138296186657 5060840987927353722139993)
                ·
                  refine ⟨3795630740945515291604995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5060840987927353722139993 3795630740945515291604995)
                  ·
                    refine ⟨5693446111418272937407493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3795630740945515291604995 5693446111418272937407493)
                    ·
                      refine ⟨1067521145890926175763905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5693446111418272937407493 1067521145890926175763905)
                      ·
                        rfl

theorem cell23_2078990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_2078990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2078990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2078990 prefixEnd_2078990 := by exact prefixLift 2078990
  have htrace : WordTrace (prefixWord ++ tailWord_2078990) baseStart_2078990 baseEnd_2078990 := by
    simpa [prefixWord, tailWord_2078990, baseEnd_2078990] using wordTrace_append hprefix tailTrace_2078990
  have hstable : (prefixWord ++ tailWord_2078990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078990).length < 2 ^ (prefixWord ++ tailWord_2078990).sum := by decide
  have hdescent : baseEnd_2078990 < baseStart_2078990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079023 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 3]
def baseStart_2079023 : Nat := 118140960795 + 2079023 * 2 ^ 59
def prefixEnd_2079023 : Nat := 4983230072969 + 3 ^ 40 * 2079023 * 2
def baseEnd_2079023 : Nat := 1067538090752524546651253

theorem tailTrace_2079023 : CollatzResearch.WordTrace tailWord_2079023 prefixEnd_2079023 1067538090752524546651253 := by
  unfold tailWord_2079023
  simp only [CollatzResearch.WordTrace]
  refine ⟨75828198347062214705033723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50552132231374809803355815 75828198347062214705033723)
  ·
    refine ⟨113742297520593322057550585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75828198347062214705033723 113742297520593322057550585)
    ·
      refine ⟨85306723140444991543162939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113742297520593322057550585 85306723140444991543162939)
      ·
        refine ⟨127960084710667487314744409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85306723140444991543162939 127960084710667487314744409)
        ·
          refine ⟨95970063533000615486058307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127960084710667487314744409 95970063533000615486058307)
          ·
            refine ⟨143955095299500923229087461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95970063533000615486058307 143955095299500923229087461)
            ·
              refine ⟨26991580368656423105453899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143955095299500923229087461 26991580368656423105453899)
              ·
                refine ⟨40487370552984634658180849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26991580368656423105453899 40487370552984634658180849)
                ·
                  refine ⟨30365527914738475993635637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40487370552984634658180849 30365527914738475993635637)
                  ·
                    refine ⟨2846768242006732124403341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30365527914738475993635637 2846768242006732124403341)
                    ·
                      refine ⟨1067538090752524546651253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2846768242006732124403341 1067538090752524546651253)
                      ·
                        rfl

theorem cell23_2079023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 3].length) (baseStart_2079023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079023 prefixEnd_2079023 := by exact prefixLift 2079023
  have htrace : WordTrace (prefixWord ++ tailWord_2079023) baseStart_2079023 baseEnd_2079023 := by
    simpa [prefixWord, tailWord_2079023, baseEnd_2079023] using wordTrace_append hprefix tailTrace_2079023
  have hstable : (prefixWord ++ tailWord_2079023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079023).length < 2 ^ (prefixWord ++ tailWord_2079023).sum := by decide
  have hdescent : baseEnd_2079023 < baseStart_2079023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079040 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 7, 1, 3]
def baseStart_2079040 : Nat := 118140960795 + 2079040 * 2 ^ 59
def prefixEnd_2079040 : Nat := 4983230072969 + 3 ^ 40 * 2079040 * 2
def baseEnd_2079040 : Nat := 1067546819923650980138675

theorem tailTrace_2079040 : CollatzResearch.WordTrace tailWord_2079040 prefixEnd_2079040 1067546819923650980138675 := by
  unfold tailWord_2079040
  simp only [CollatzResearch.WordTrace]
  refine ⟨37914409194000313304201287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50552545592000417738935049 37914409194000313304201287)
  ·
    refine ⟨56871613791000469956301931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37914409194000313304201287 56871613791000469956301931)
    ·
      refine ⟨85307420686500704934452897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56871613791000469956301931 85307420686500704934452897)
      ·
        refine ⟨63980565514875528700839673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85307420686500704934452897 63980565514875528700839673)
        ·
          refine ⟨47985424136156646525629755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63980565514875528700839673 47985424136156646525629755)
          ·
            refine ⟨71978136204234969788444633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47985424136156646525629755 71978136204234969788444633)
            ·
              refine ⟨53983602153176227341333475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71978136204234969788444633 53983602153176227341333475)
              ·
                refine ⟨80975403229764341012000213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53983602153176227341333475 80975403229764341012000213)
                ·
                  refine ⟨1897861013197601742468755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 80975403229764341012000213 1897861013197601742468755)
                  ·
                    refine ⟨2846791519796402613703133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1897861013197601742468755 2846791519796402613703133)
                    ·
                      refine ⟨1067546819923650980138675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2846791519796402613703133 1067546819923650980138675)
                      ·
                        rfl

theorem cell23_2079040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_2079040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079040 prefixEnd_2079040 := by exact prefixLift 2079040
  have htrace : WordTrace (prefixWord ++ tailWord_2079040) baseStart_2079040 baseEnd_2079040 := by
    simpa [prefixWord, tailWord_2079040, baseEnd_2079040] using wordTrace_append hprefix tailTrace_2079040
  have hstable : (prefixWord ++ tailWord_2079040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079040).length < 2 ^ (prefixWord ++ tailWord_2079040).sum := by decide
  have hdescent : baseEnd_2079040 < baseStart_2079040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079050 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 5, 5, 2]
def baseStart_2079050 : Nat := 118140960795 + 2079050 * 2 ^ 59
def prefixEnd_2079050 : Nat := 4983230072969 + 3 ^ 40 * 2079050 * 2
def baseEnd_2079050 : Nat := 1067551954730195941013629

theorem tailTrace_2079050 : CollatzResearch.WordTrace tailWord_2079050 prefixEnd_2079050 1067551954730195941013629 := by
  unfold tailWord_2079050
  simp only [CollatzResearch.WordTrace]
  refine ⟨18957295779491099579066651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50552788745309598877511069 18957295779491099579066651)
  ·
    refine ⟨28435943669236649368599977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18957295779491099579066651 28435943669236649368599977)
    ·
      refine ⟨21326957751927487026449983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28435943669236649368599977 21326957751927487026449983)
      ·
        refine ⟨31990436627891230539674975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21326957751927487026449983 31990436627891230539674975)
        ·
          refine ⟨47985654941836845809512463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31990436627891230539674975 47985654941836845809512463)
          ·
            refine ⟨71978482412755268714268695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47985654941836845809512463 71978482412755268714268695)
            ·
              refine ⟨107967723619132903071403043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71978482412755268714268695 107967723619132903071403043)
              ·
                refine ⟨161951585428699354607104565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107967723619132903071403043 161951585428699354607104565)
                ·
                  refine ⟨15182961133940564494416053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161951585428699354607104565 15182961133940564494416053)
                  ·
                    refine ⟨1423402606306927921351505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15182961133940564494416053 1423402606306927921351505)
                    ·
                      refine ⟨1067551954730195941013629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1423402606306927921351505 1067551954730195941013629)
                      ·
                        rfl

theorem cell23_2079050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_2079050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079050 prefixEnd_2079050 := by exact prefixLift 2079050
  have htrace : WordTrace (prefixWord ++ tailWord_2079050) baseStart_2079050 baseEnd_2079050 := by
    simpa [prefixWord, tailWord_2079050, baseEnd_2079050] using wordTrace_append hprefix tailTrace_2079050
  have hstable : (prefixWord ++ tailWord_2079050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079050).length < 2 ^ (prefixWord ++ tailWord_2079050).sum := by decide
  have hdescent : baseEnd_2079050 < baseStart_2079050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079060 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_2079060 : Nat := 118140960795 + 2079060 * 2 ^ 59
def prefixEnd_2079060 : Nat := 4983230072969 + 3 ^ 40 * 2079060 * 2
def baseEnd_2079060 : Nat := 355852363178913633962861

theorem tailTrace_2079060 : CollatzResearch.WordTrace tailWord_2079060 prefixEnd_2079060 355852363178913633962861 := by
  unfold tailWord_2079060
  simp only [CollatzResearch.WordTrace]
  refine ⟨37914773923964085012065317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50553031898618780016087089 37914773923964085012065317)
  ·
    refine ⟨7109020110743265939762247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37914773923964085012065317 7109020110743265939762247)
    ·
      refine ⟨10663530166114898909643371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7109020110743265939762247 10663530166114898909643371)
      ·
        refine ⟨15995295249172348364465057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10663530166114898909643371 15995295249172348364465057)
        ·
          refine ⟨11996471436879261273348793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15995295249172348364465057 11996471436879261273348793)
          ·
            refine ⟨8997353577659445955011595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11996471436879261273348793 8997353577659445955011595)
            ·
              refine ⟨13496030366489168932517393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8997353577659445955011595 13496030366489168932517393)
              ·
                refine ⟨10122022774866876699388045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13496030366489168932517393 10122022774866876699388045)
                ·
                  refine ⟨3795758540575078762270517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10122022774866876699388045 3795758540575078762270517)
                  ·
                    refine ⟨355852363178913633962861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3795758540575078762270517 355852363178913633962861)
                    ·
                      rfl

theorem cell23_2079060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_2079060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079060 prefixEnd_2079060 := by exact prefixLift 2079060
  have htrace : WordTrace (prefixWord ++ tailWord_2079060) baseStart_2079060 baseEnd_2079060 := by
    simpa [prefixWord, tailWord_2079060, baseEnd_2079060] using wordTrace_append hprefix tailTrace_2079060
  have hstable : (prefixWord ++ tailWord_2079060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079060).length < 2 ^ (prefixWord ++ tailWord_2079060).sum := by decide
  have hdescent : baseEnd_2079060 < baseStart_2079060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079074 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2079074 : Nat := 118140960795 + 2079074 * 2 ^ 59
def prefixEnd_2079074 : Nat := 4983230072969 + 3 ^ 40 * 2079074 * 2
def baseEnd_2079074 : Nat := 1067564278265903847113519

theorem tailTrace_2079074 : CollatzResearch.WordTrace tailWord_2079074 prefixEnd_2079074 1067564278265903847113519 := by
  unfold tailWord_2079074
  simp only [CollatzResearch.WordTrace]
  refine ⟨18957514617469362603785069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50553372313251633610093517 18957514617469362603785069)
  ·
    refine ⟨7109067981551010976419401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18957514617469362603785069 7109067981551010976419401)
    ·
      refine ⟨5331800986163258232314551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7109067981551010976419401 5331800986163258232314551)
      ·
        refine ⟨7997701479244887348471827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5331800986163258232314551 7997701479244887348471827)
        ·
          refine ⟨11996552218867331022707741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7997701479244887348471827 11996552218867331022707741)
          ·
            refine ⟨4498707082075249133515403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11996552218867331022707741 4498707082075249133515403)
            ·
              refine ⟨6748060623112873700273105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4498707082075249133515403 6748060623112873700273105)
              ·
                refine ⟨5061045467334655275204829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6748060623112873700273105 5061045467334655275204829)
                ·
                  refine ⟨1897892050250495728201811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5061045467334655275204829 1897892050250495728201811)
                  ·
                    refine ⟨2846838075375743592302717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1897892050250495728201811 2846838075375743592302717)
                    ·
                      refine ⟨1067564278265903847113519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2846838075375743592302717 1067564278265903847113519)
                      ·
                        rfl

theorem cell23_2079074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2079074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079074 prefixEnd_2079074 := by exact prefixLift 2079074
  have htrace : WordTrace (prefixWord ++ tailWord_2079074) baseStart_2079074 baseEnd_2079074 := by
    simpa [prefixWord, tailWord_2079074, baseEnd_2079074] using wordTrace_append hprefix tailTrace_2079074
  have hstable : (prefixWord ++ tailWord_2079074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079074).length < 2 ^ (prefixWord ++ tailWord_2079074).sum := by decide
  have hdescent : baseEnd_2079074 < baseStart_2079074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079083 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 5]
def baseStart_2079083 : Nat := 118140960795 + 2079083 * 2 ^ 59
def prefixEnd_2079083 : Nat := 4983230072969 + 3 ^ 40 * 2079083 * 2
def baseEnd_2079083 : Nat := 1067568899591794311900977

theorem tailTrace_2079083 : CollatzResearch.WordTrace tailWord_2079083 prefixEnd_2079083 1067568899591794311900977 := by
  unfold tailWord_2079083
  simp only [CollatzResearch.WordTrace]
  refine ⟨75830386726844844952217903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50553591151229896634811935 75830386726844844952217903)
  ·
    refine ⟨113745580090267267428326855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75830386726844844952217903 113745580090267267428326855)
    ·
      refine ⟨170618370135400901142490283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113745580090267267428326855 170618370135400901142490283)
      ·
        refine ⟨255927555203101351713735425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170618370135400901142490283 255927555203101351713735425)
        ·
          refine ⟨191945666402326013785301569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255927555203101351713735425 191945666402326013785301569)
          ·
            refine ⟨143959249801744510338976177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191945666402326013785301569 143959249801744510338976177)
            ·
              refine ⟨107969437351308382754232133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143959249801744510338976177 107969437351308382754232133)
              ·
                refine ⟨20244269503370321766418525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107969437351308382754232133 20244269503370321766418525)
                ·
                  refine ⟨7591601063763870662406947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20244269503370321766418525 7591601063763870662406947)
                  ·
                    refine ⟨11387401595645805993610421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7591601063763870662406947 11387401595645805993610421)
                    ·
                      refine ⟨1067568899591794311900977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11387401595645805993610421 1067568899591794311900977)
                      ·
                        rfl

theorem cell23_2079083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 5].length) (baseStart_2079083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079083 prefixEnd_2079083 := by exact prefixLift 2079083
  have htrace : WordTrace (prefixWord ++ tailWord_2079083) baseStart_2079083 baseEnd_2079083 := by
    simpa [prefixWord, tailWord_2079083, baseEnd_2079083] using wordTrace_append hprefix tailTrace_2079083
  have hstable : (prefixWord ++ tailWord_2079083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079083).length < 2 ^ (prefixWord ++ tailWord_2079083).sum := by decide
  have hdescent : baseEnd_2079083 < baseStart_2079083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079090 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_2079090 : Nat := 118140960795 + 2079090 * 2 ^ 59
def prefixEnd_2079090 : Nat := 4983230072969 + 3 ^ 40 * 2079090 * 2
def baseEnd_2079090 : Nat := 355857497985458594837815

theorem tailTrace_2079090 : CollatzResearch.WordTrace tailWord_2079090 prefixEnd_2079090 355857497985458594837815 := by
  unfold tailWord_2079090
  simp only [CollatzResearch.WordTrace]
  refine ⟨18957660509454871286930681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50553761358546323431815149 18957660509454871286930681)
  ·
    refine ⟨14218245382091153465198011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18957660509454871286930681 14218245382091153465198011)
    ·
      refine ⟨21327368073136730197797017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14218245382091153465198011 21327368073136730197797017)
      ·
        refine ⟨15995526054852547648347763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21327368073136730197797017 15995526054852547648347763)
        ·
          refine ⟨23993289082278821472521645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15995526054852547648347763 23993289082278821472521645)
          ·
            refine ⟨8997483405854558052195617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23993289082278821472521645 8997483405854558052195617)
            ·
              refine ⟨6748112554390918539146713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8997483405854558052195617 6748112554390918539146713)
              ·
                refine ⟨5061084415793188904360035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6748112554390918539146713 5061084415793188904360035)
                ·
                  refine ⟨7591626623689783356540053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5061084415793188904360035 7591626623689783356540053)
                  ·
                    refine ⟨355857497985458594837815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7591626623689783356540053 355857497985458594837815)
                    ·
                      rfl

theorem cell23_2079090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_2079090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079090 prefixEnd_2079090 := by exact prefixLift 2079090
  have htrace : WordTrace (prefixWord ++ tailWord_2079090) baseStart_2079090 baseEnd_2079090 := by
    simpa [prefixWord, tailWord_2079090, baseEnd_2079090] using wordTrace_append hprefix tailTrace_2079090
  have hstable : (prefixWord ++ tailWord_2079090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079090).length < 2 ^ (prefixWord ++ tailWord_2079090).sum := by decide
  have hdescent : baseEnd_2079090 < baseStart_2079090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079097 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 7, 2, 2]
def baseStart_2079097 : Nat := 118140960795 + 2079097 * 2 ^ 59
def prefixEnd_2079097 : Nat := 4983230072969 + 3 ^ 40 * 2079097 * 2
def baseEnd_2079097 : Nat := 1067576088320957257125913

theorem tailTrace_2079097 : CollatzResearch.WordTrace tailWord_2079097 prefixEnd_2079097 1067576088320957257125913 := by
  unfold tailWord_2079097
  simp only [CollatzResearch.WordTrace]
  refine ⟨75830897348794125343227545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50553931565862750228818363 75830897348794125343227545)
  ·
    refine ⟨56873173011595594007420659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75830897348794125343227545 56873173011595594007420659)
    ·
      refine ⟨85309759517393391011130989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56873173011595594007420659 85309759517393391011130989)
      ·
        refine ⟨31991159819022521629174121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85309759517393391011130989 31991159819022521629174121)
        ·
          refine ⟨23993369864266891221880591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31991159819022521629174121 23993369864266891221880591)
          ·
            refine ⟨35990054796400336832820887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23993369864266891221880591 35990054796400336832820887)
            ·
              refine ⟨53985082194600505249231331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35990054796400336832820887 53985082194600505249231331)
              ·
                refine ⟨80977623291900757873846997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53985082194600505249231331 80977623291900757873846997)
                ·
                  refine ⟨1897913045903924012668289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 80977623291900757873846997 1897913045903924012668289)
                  ·
                    refine ⟨1423434784427943009501217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1897913045903924012668289 1423434784427943009501217)
                    ·
                      refine ⟨1067576088320957257125913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1423434784427943009501217 1067576088320957257125913)
                      ·
                        rfl

theorem cell23_2079097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_2079097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079097 prefixEnd_2079097 := by exact prefixLift 2079097
  have htrace : WordTrace (prefixWord ++ tailWord_2079097) baseStart_2079097 baseEnd_2079097 := by
    simpa [prefixWord, tailWord_2079097, baseEnd_2079097] using wordTrace_append hprefix tailTrace_2079097
  have hstable : (prefixWord ++ tailWord_2079097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079097).length < 2 ^ (prefixWord ++ tailWord_2079097).sum := by decide
  have hdescent : baseEnd_2079097 < baseStart_2079097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079100 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_2079100 : Nat := 118140960795 + 2079100 * 2 ^ 59
def prefixEnd_2079100 : Nat := 4983230072969 + 3 ^ 40 * 2079100 * 2
def baseEnd_2079100 : Nat := 1067577628762920745388399

theorem tailTrace_2079100 : CollatzResearch.WordTrace tailWord_2079100 prefixEnd_2079100 1067577628762920745388399 := by
  unfold tailWord_2079100
  simp only [CollatzResearch.WordTrace]
  refine ⟨37915503383891628427793377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50554004511855504570391169 37915503383891628427793377)
  ·
    refine ⟨28436627537918721320845033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37915503383891628427793377 28436627537918721320845033)
    ·
      refine ⟨21327470653439040990633775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28436627537918721320845033 21327470653439040990633775)
      ·
        refine ⟨31991205980158561485950663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21327470653439040990633775 31991205980158561485950663)
        ·
          refine ⟨47986808970237842228925995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31991205980158561485950663 47986808970237842228925995)
          ·
            refine ⟨71980213455356763343388993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47986808970237842228925995 71980213455356763343388993)
            ·
              refine ⟨53985160091517572507541745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71980213455356763343388993 53985160091517572507541745)
              ·
                refine ⟨40488870068638179380656309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53985160091517572507541745 40488870068638179380656309)
                ·
                  refine ⟨3795831568934829316936529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40488870068638179380656309 3795831568934829316936529)
                  ·
                    refine ⟨2846873676701121987702397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3795831568934829316936529 2846873676701121987702397)
                    ·
                      refine ⟨1067577628762920745388399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2846873676701121987702397 1067577628762920745388399)
                      ·
                        rfl

theorem cell23_2079100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_2079100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079100 prefixEnd_2079100 := by exact prefixLift 2079100
  have htrace : WordTrace (prefixWord ++ tailWord_2079100) baseStart_2079100 baseEnd_2079100 := by
    simpa [prefixWord, tailWord_2079100, baseEnd_2079100] using wordTrace_append hprefix tailTrace_2079100
  have hstable : (prefixWord ++ tailWord_2079100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079100).length < 2 ^ (prefixWord ++ tailWord_2079100).sum := by decide
  have hdescent : baseEnd_2079100 < baseStart_2079100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079107 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 4, 4]
def baseStart_2079107 : Nat := 118140960795 + 2079107 * 2 ^ 59
def prefixEnd_2079107 : Nat := 4983230072969 + 3 ^ 40 * 2079107 * 2
def baseEnd_2079107 : Nat := 355860407709167406000289

theorem tailTrace_2079107 : CollatzResearch.WordTrace tailWord_2079107 prefixEnd_2079107 355860407709167406000289 := by
  unfold tailWord_2079107
  simp only [CollatzResearch.WordTrace]
  refine ⟨75831262078757897051091575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50554174719171931367394383 75831262078757897051091575)
  ·
    refine ⟨113746893118136845576637363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75831262078757897051091575 113746893118136845576637363)
    ·
      refine ⟨170620339677205268364956045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113746893118136845576637363 170620339677205268364956045)
      ·
        refine ⟨63982627378951975636858517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170620339677205268364956045 63982627378951975636858517)
        ·
          refine ⟨2999185658388373857977743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63982627378951975636858517 2999185658388373857977743)
          ·
            refine ⟨4498778487582560786966615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999185658388373857977743 4498778487582560786966615)
            ·
              refine ⟨6748167731373841180449923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4498778487582560786966615 6748167731373841180449923)
              ·
                refine ⟨10122251597060761770674885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6748167731373841180449923 10122251597060761770674885)
                ·
                  refine ⟨1897922174448892832001541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10122251597060761770674885 1897922174448892832001541)
                  ·
                    refine ⟨355860407709167406000289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1897922174448892832001541 355860407709167406000289)
                    ·
                      rfl

theorem cell23_2079107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 4].length) (baseStart_2079107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079107 prefixEnd_2079107 := by exact prefixLift 2079107
  have htrace : WordTrace (prefixWord ++ tailWord_2079107) baseStart_2079107 baseEnd_2079107 := by
    simpa [prefixWord, tailWord_2079107, baseEnd_2079107] using wordTrace_append hprefix tailTrace_2079107
  have hstable : (prefixWord ++ tailWord_2079107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079107).length < 2 ^ (prefixWord ++ tailWord_2079107).sum := by decide
  have hdescent : baseEnd_2079107 < baseStart_2079107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079124 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_2079124 : Nat := 118140960795 + 2079124 * 2 ^ 59
def prefixEnd_2079124 : Nat := 4983230072969 + 3 ^ 40 * 2079124 * 2
def baseEnd_2079124 : Nat := 355863317432876217162763

theorem tailTrace_2079124 : CollatzResearch.WordTrace tailWord_2079124 prefixEnd_2079124 355863317432876217162763 := by
  unfold tailWord_2079124
  simp only [CollatzResearch.WordTrace]
  refine ⟨37915941059848154477230213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50554588079797539302973617 37915941059848154477230213)
  ·
    refine ⟨7109238948721528964480665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37915941059848154477230213 7109238948721528964480665)
    ·
      refine ⟨5331929211541146723360499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7109238948721528964480665 5331929211541146723360499)
      ·
        refine ⟨7997893817311720085040749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5331929211541146723360499 7997893817311720085040749)
        ·
          refine ⟨2999210181491895031890281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7997893817311720085040749 2999210181491895031890281)
          ·
            refine ⟨2249407636118921273917711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2999210181491895031890281 2249407636118921273917711)
            ·
              refine ⟨3374111454178381910876567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249407636118921273917711 3374111454178381910876567)
              ·
                refine ⟨5061167181267572866314851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3374111454178381910876567 5061167181267572866314851)
                ·
                  refine ⟨7591750771901359299472277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5061167181267572866314851 7591750771901359299472277)
                  ·
                    refine ⟨355863317432876217162763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7591750771901359299472277 355863317432876217162763)
                    ·
                      rfl

theorem cell23_2079124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_2079124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079124 prefixEnd_2079124 := by exact prefixLift 2079124
  have htrace : WordTrace (prefixWord ++ tailWord_2079124) baseStart_2079124 baseEnd_2079124 := by
    simpa [prefixWord, tailWord_2079124, baseEnd_2079124] using wordTrace_append hprefix tailTrace_2079124
  have hstable : (prefixWord ++ tailWord_2079124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079124).length < 2 ^ (prefixWord ++ tailWord_2079124).sum := by decide
  have hdescent : baseEnd_2079124 < baseStart_2079124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079137 : List Nat := [1, 2, 3, 5, 1, 1, 1, 9]
def baseStart_2079137 : Nat := 118140960795 + 2079137 * 2 ^ 59
def prefixEnd_2079137 : Nat := 4983230072969 + 3 ^ 40 * 2079137 * 2
def baseEnd_2079137 : Nat := 39540615835079151875027

theorem tailTrace_2079137 : CollatzResearch.WordTrace tailWord_2079137 prefixEnd_2079137 39540615835079151875027 := by
  unfold tailWord_2079137
  simp only [CollatzResearch.WordTrace]
  refine ⟨75832356268649212174683665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50554904179099474783122443 75832356268649212174683665)
  ·
    refine ⟨56874267201486909131012749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75832356268649212174683665 56874267201486909131012749)
    ·
      refine ⟨21327850200557590924129781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56874267201486909131012749 21327850200557590924129781)
      ·
        refine ⟨1999485956302274149137167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21327850200557590924129781 1999485956302274149137167)
        ·
          refine ⟨2999228934453411223705751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999485956302274149137167 2999228934453411223705751)
          ·
            refine ⟨4498843401680116835558627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999228934453411223705751 4498843401680116835558627)
            ·
              refine ⟨6748265102520175253337941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4498843401680116835558627 6748265102520175253337941)
              ·
                refine ⟨39540615835079151875027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6748265102520175253337941 39540615835079151875027)
                ·
                  rfl

theorem cell23_2079137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 9].length) (baseStart_2079137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079137 prefixEnd_2079137 := by exact prefixLift 2079137
  have htrace : WordTrace (prefixWord ++ tailWord_2079137) baseStart_2079137 baseEnd_2079137 := by
    simpa [prefixWord, tailWord_2079137, baseEnd_2079137] using wordTrace_append hprefix tailTrace_2079137
  have hstable : (prefixWord ++ tailWord_2079137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079137).length < 2 ^ (prefixWord ++ tailWord_2079137).sum := by decide
  have hdescent : baseEnd_2079137 < baseStart_2079137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079163 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 5, 8]
def baseStart_2079163 : Nat := 118140960795 + 2079163 * 2 ^ 59
def prefixEnd_2079163 : Nat := 4983230072969 + 3 ^ 40 * 2079163 * 2
def baseEnd_2079163 : Nat := 355869992681384666300203

theorem tailTrace_2079163 : CollatzResearch.WordTrace tailWord_2079163 prefixEnd_2079163 355869992681384666300203 := by
  unfold tailWord_2079163
  simp only [CollatzResearch.WordTrace]
  refine ⟨75833304566555018615130143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50555536377703345743420095 75833304566555018615130143)
  ·
    refine ⟨113749956849832527922695215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75833304566555018615130143 113749956849832527922695215)
    ·
      refine ⟨170624935274748791884042823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113749956849832527922695215 170624935274748791884042823)
      ·
        refine ⟨255937402912123187826064235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170624935274748791884042823 255937402912123187826064235)
        ·
          refine ⟨383906104368184781739096353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255937402912123187826064235 383906104368184781739096353)
          ·
            refine ⟨287929578276138586304322265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383906104368184781739096353 287929578276138586304322265)
            ·
              refine ⟨215947183707103939728241699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287929578276138586304322265 215947183707103939728241699)
              ·
                refine ⟨323920775560655909592362549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215947183707103939728241699 323920775560655909592362549)
                ·
                  refine ⟨30367572708811491524283989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323920775560655909592362549 30367572708811491524283989)
                  ·
                    refine ⟨355869992681384666300203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30367572708811491524283989 355869992681384666300203)
                    ·
                      rfl

theorem cell23_2079163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 8].length) (baseStart_2079163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079163 prefixEnd_2079163 := by exact prefixLift 2079163
  have htrace : WordTrace (prefixWord ++ tailWord_2079163) baseStart_2079163 baseEnd_2079163 := by
    simpa [prefixWord, tailWord_2079163, baseEnd_2079163] using wordTrace_append hprefix tailTrace_2079163
  have hstable : (prefixWord ++ tailWord_2079163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079163).length < 2 ^ (prefixWord ++ tailWord_2079163).sum := by decide
  have hdescent : baseEnd_2079163 < baseStart_2079163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079164 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_2079164 : Nat := 118140960795 + 2079164 * 2 ^ 59
def prefixEnd_2079164 : Nat := 4983230072969 + 3 ^ 40 * 2079164 * 2
def baseEnd_2079164 : Nat := 1067610491524808494988105

theorem tailTrace_2079164 : CollatzResearch.WordTrace tailWord_2079164 prefixEnd_2079164 1067610491524808494988105 := by
  unfold tailWord_2079164
  simp only [CollatzResearch.WordTrace]
  refine ⟨37916670519775697892958273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50555560693034263857277697 37916670519775697892958273)
  ·
    refine ⟨28437502889831773419718705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37916670519775697892958273 28437502889831773419718705)
    ·
      refine ⟨21328127167373830064789029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28437502889831773419718705 21328127167373830064789029)
      ·
        refine ⟨3999023843882593137147943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21328127167373830064789029 3999023843882593137147943)
        ·
          refine ⟨5998535765823889705721915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3999023843882593137147943 5998535765823889705721915)
          ·
            refine ⟨8997803648735834558582873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5998535765823889705721915 8997803648735834558582873)
            ·
              refine ⟨6748352736551875918937155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8997803648735834558582873 6748352736551875918937155)
              ·
                refine ⟨10122529104827813878405733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6748352736551875918937155 10122529104827813878405733)
                ·
                  refine ⟨1897974207155215102201075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10122529104827813878405733 1897974207155215102201075)
                  ·
                    refine ⟨2846961310732822653301613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1897974207155215102201075 2846961310732822653301613)
                    ·
                      refine ⟨1067610491524808494988105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2846961310732822653301613 1067610491524808494988105)
                      ·
                        rfl

theorem cell23_2079164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_2079164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079164 prefixEnd_2079164 := by exact prefixLift 2079164
  have htrace : WordTrace (prefixWord ++ tailWord_2079164) baseStart_2079164 baseEnd_2079164 := by
    simpa [prefixWord, tailWord_2079164, baseEnd_2079164] using wordTrace_append hprefix tailTrace_2079164
  have hstable : (prefixWord ++ tailWord_2079164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079164).length < 2 ^ (prefixWord ++ tailWord_2079164).sum := by decide
  have hdescent : baseEnd_2079164 < baseStart_2079164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079240 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 1, 7]
def baseStart_2079240 : Nat := 118140960795 + 2079240 * 2 ^ 59
def prefixEnd_2079240 : Nat := 4983230072969 + 3 ^ 40 * 2079240 * 2
def baseEnd_2079240 : Nat := 355883172018183399212585

theorem tailTrace_2079240 : CollatzResearch.WordTrace tailWord_2079240 prefixEnd_2079240 355883172018183399212585 := by
  unfold tailWord_2079240
  simp only [CollatzResearch.WordTrace]
  refine ⟨37918056493638030382841587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50557408658184040510455449 37918056493638030382841587)
  ·
    refine ⟨56877084740457045574262381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37918056493638030382841587 56877084740457045574262381)
    ·
      refine ⟨21328906777671392090348393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56877084740457045574262381 21328906777671392090348393)
      ·
        refine ⟨15996680083253544067761295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21328906777671392090348393 15996680083253544067761295)
        ·
          refine ⟨23995020124880316101641943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15996680083253544067761295 23995020124880316101641943)
          ·
            refine ⟨35992530187320474152462915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23995020124880316101641943 35992530187320474152462915)
            ·
              refine ⟨53988795280980711228694373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35992530187320474152462915 53988795280980711228694373)
              ·
                refine ⟨10122899115183883355380195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53988795280980711228694373 10122899115183883355380195)
                ·
                  refine ⟨15184348672775825033070293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10122899115183883355380195 15184348672775825033070293)
                  ·
                    refine ⟨355883172018183399212585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15184348672775825033070293 355883172018183399212585)
                    ·
                      rfl

theorem cell23_2079240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_2079240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079240 prefixEnd_2079240 := by exact prefixLift 2079240
  have htrace : WordTrace (prefixWord ++ tailWord_2079240) baseStart_2079240 baseEnd_2079240 := by
    simpa [prefixWord, tailWord_2079240, baseEnd_2079240] using wordTrace_append hprefix tailTrace_2079240
  have hstable : (prefixWord ++ tailWord_2079240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079240).length < 2 ^ (prefixWord ++ tailWord_2079240).sum := by decide
  have hdescent : baseEnd_2079240 < baseStart_2079240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079280 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 5]
def baseStart_2079280 : Nat := 118140960795 + 2079280 * 2 ^ 59
def prefixEnd_2079280 : Nat := 4983230072969 + 3 ^ 40 * 2079280 * 2
def baseEnd_2079280 : Nat := 1067670055280730041137571

theorem tailTrace_2079280 : CollatzResearch.WordTrace tailWord_2079280 prefixEnd_2079280 1067670055280730041137571 := by
  unfold tailWord_2079280
  simp only [CollatzResearch.WordTrace]
  refine ⟨37918785953565573798569647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50558381271420765064759529 37918785953565573798569647)
  ·
    refine ⟨56878178930348360697854471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37918785953565573798569647 56878178930348360697854471)
    ·
      refine ⟨85317268395522541046781707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56878178930348360697854471 85317268395522541046781707)
      ·
        refine ⟨127975902593283811570172561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85317268395522541046781707 127975902593283811570172561)
        ·
          refine ⟨95981926944962858677629421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127975902593283811570172561 95981926944962858677629421)
          ·
            refine ⟨35993222604361072004111033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95981926944962858677629421 35993222604361072004111033)
            ·
              refine ⟨26994916953270804003083275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35993222604361072004111033 26994916953270804003083275)
              ·
                refine ⟨40492375429906206004624913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26994916953270804003083275 40492375429906206004624913)
                ·
                  refine ⟨30369281572429654503468685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40492375429906206004624913 30369281572429654503468685)
                  ·
                    refine ⟨11388480589661120438800757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30369281572429654503468685 11388480589661120438800757)
                    ·
                      refine ⟨1067670055280730041137571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11388480589661120438800757 1067670055280730041137571)
                      ·
                        rfl

theorem cell23_2079280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_2079280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079280 prefixEnd_2079280 := by exact prefixLift 2079280
  have htrace : WordTrace (prefixWord ++ tailWord_2079280) baseStart_2079280 baseEnd_2079280 := by
    simpa [prefixWord, tailWord_2079280, baseEnd_2079280] using wordTrace_append hprefix tailTrace_2079280
  have hstable : (prefixWord ++ tailWord_2079280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079280).length < 2 ^ (prefixWord ++ tailWord_2079280).sum := by decide
  have hdescent : baseEnd_2079280 < baseStart_2079280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079314 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_2079314 : Nat := 118140960795 + 2079314 * 2 ^ 59
def prefixEnd_2079314 : Nat := 4983230072969 + 3 ^ 40 * 2079314 * 2
def baseEnd_2079314 : Nat := 1067687513622982908112415

theorem tailTrace_2079314 : CollatzResearch.WordTrace tailWord_2079314 prefixEnd_2079314 1067687513622982908112415 := by
  unfold tailWord_2079314
  simp only [CollatzResearch.WordTrace]
  refine ⟨18959702997251992850969249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50559207992671980935917997 18959702997251992850969249)
  ·
    refine ⟨14219777247938994638226937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18959702997251992850969249 14219777247938994638226937)
    ·
      refine ⟨10664832935954245978670203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14219777247938994638226937 10664832935954245978670203)
      ·
        refine ⟨15997249403931368968005305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10664832935954245978670203 15997249403931368968005305)
        ·
          refine ⟨11997937052948526726003979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15997249403931368968005305 11997937052948526726003979)
          ·
            refine ⟨17996905579422790089005969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11997937052948526726003979 17996905579422790089005969)
            ·
              refine ⟨13497679184567092566754477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17996905579422790089005969 13497679184567092566754477)
              ·
                refine ⟨5061629694212659712532929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13497679184567092566754477 5061629694212659712532929)
                ·
                  refine ⟨3796222270659494784399697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5061629694212659712532929 3796222270659494784399697)
                  ·
                    refine ⟨2847166702994621088299773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3796222270659494784399697 2847166702994621088299773)
                    ·
                      refine ⟨1067687513622982908112415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2847166702994621088299773 1067687513622982908112415)
                      ·
                        rfl

theorem cell23_2079314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_2079314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079314 prefixEnd_2079314 := by exact prefixLift 2079314
  have htrace : WordTrace (prefixWord ++ tailWord_2079314) baseStart_2079314 baseEnd_2079314 := by
    simpa [prefixWord, tailWord_2079314, baseEnd_2079314] using wordTrace_append hprefix tailTrace_2079314
  have hstable : (prefixWord ++ tailWord_2079314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079314).length < 2 ^ (prefixWord ++ tailWord_2079314).sum := by decide
  have hdescent : baseEnd_2079314 < baseStart_2079314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079338 : List Nat := [3, 1, 3, 2, 1, 1, 5, 2, 1, 4]
def baseStart_2079338 : Nat := 118140960795 + 2079338 * 2 ^ 59
def prefixEnd_2079338 : Nat := 4983230072969 + 3 ^ 40 * 2079338 * 2
def baseEnd_2079338 : Nat := 355899945719563604737435

theorem tailTrace_2079338 : CollatzResearch.WordTrace tailWord_2079338 prefixEnd_2079338 355899945719563604737435 := by
  unfold tailWord_2079338
  simp only [CollatzResearch.WordTrace]
  refine ⟨18959921835230255875687667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50559791560614015668500445 18959921835230255875687667)
  ·
    refine ⟨28439882752845383813531501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18959921835230255875687667 28439882752845383813531501)
    ·
      refine ⟨10664956032317018930074313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28439882752845383813531501 10664956032317018930074313)
      ·
        refine ⟨7998717024237764197555735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10664956032317018930074313 7998717024237764197555735)
        ·
          refine ⟨11998075536356646296333603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7998717024237764197555735 11998075536356646296333603)
          ·
            refine ⟨17997113304534969444500405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11998075536356646296333603 17997113304534969444500405)
            ·
              refine ⟨1687229372300153385421913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17997113304534969444500405 1687229372300153385421913)
              ·
                refine ⟨1265422029225115039066435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1687229372300153385421913 1265422029225115039066435)
                ·
                  refine ⟨1898133043837672558599653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1265422029225115039066435 1898133043837672558599653)
                  ·
                    refine ⟨355899945719563604737435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1898133043837672558599653 355899945719563604737435)
                    ·
                      rfl

theorem cell23_2079338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_2079338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079338 prefixEnd_2079338 := by exact prefixLift 2079338
  have htrace : WordTrace (prefixWord ++ tailWord_2079338) baseStart_2079338 baseEnd_2079338 := by
    simpa [prefixWord, tailWord_2079338, baseEnd_2079338] using wordTrace_append hprefix tailTrace_2079338
  have hstable : (prefixWord ++ tailWord_2079338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079338).length < 2 ^ (prefixWord ++ tailWord_2079338).sum := by decide
  have hdescent : baseEnd_2079338 < baseStart_2079338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079364 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_2079364 : Nat := 118140960795 + 2079364 * 2 ^ 59
def prefixEnd_2079364 : Nat := 4983230072969 + 3 ^ 40 * 2079364 * 2
def baseEnd_2079364 : Nat := 355904395885235904162395

theorem tailTrace_2079364 : CollatzResearch.WordTrace tailWord_2079364 prefixEnd_2079364 355904395885235904162395 := by
  unfold tailWord_2079364
  simp only [CollatzResearch.WordTrace]
  refine ⟨37920317819413414971598573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50560423759217886628798097 37920317819413414971598573)
  ·
    refine ⟨14220119182280030614349465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37920317819413414971598573 14220119182280030614349465)
    ·
      refine ⟨10665089386710022960762099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14220119182280030614349465 10665089386710022960762099)
      ·
        refine ⟨15997634080065034441143149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10665089386710022960762099 15997634080065034441143149)
        ·
          refine ⟨5999112780024387915428681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15997634080065034441143149 5999112780024387915428681)
          ·
            refine ⟨4499334585018290936571511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5999112780024387915428681 4499334585018290936571511)
            ·
              refine ⟨6749001877527436404857267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4499334585018290936571511 6749001877527436404857267)
              ·
                refine ⟨10123502816291154607285901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6749001877527436404857267 10123502816291154607285901)
                ·
                  refine ⟨3796313556109182977732213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10123502816291154607285901 3796313556109182977732213)
                  ·
                    refine ⟨355904395885235904162395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3796313556109182977732213 355904395885235904162395)
                    ·
                      rfl

theorem cell23_2079364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_2079364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079364 prefixEnd_2079364 := by exact prefixLift 2079364
  have htrace : WordTrace (prefixWord ++ tailWord_2079364) baseStart_2079364 baseEnd_2079364 := by
    simpa [prefixWord, tailWord_2079364, baseEnd_2079364] using wordTrace_append hprefix tailTrace_2079364
  have hstable : (prefixWord ++ tailWord_2079364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079364).length < 2 ^ (prefixWord ++ tailWord_2079364).sum := by decide
  have hdescent : baseEnd_2079364 < baseStart_2079364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079397 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_2079397 : Nat := 118140960795 + 2079397 * 2 ^ 59
def prefixEnd_2079397 : Nat := 4983230072969 + 3 ^ 40 * 2079397 * 2
def baseEnd_2079397 : Nat := 1067730132517306083374533

theorem tailTrace_2079397 : CollatzResearch.WordTrace tailWord_2079397 prefixEnd_2079397 1067730132517306083374533 := by
  unfold tailWord_2079397
  simp only [CollatzResearch.WordTrace]
  refine ⟨75841839247707276579148445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50561226165138184386098963 75841839247707276579148445)
  ·
    refine ⟨28440689717890228717180667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75841839247707276579148445 28440689717890228717180667)
    ·
      refine ⟨42661034576835343075771001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28440689717890228717180667 42661034576835343075771001)
      ·
        refine ⟨31995775932626507306828251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42661034576835343075771001 31995775932626507306828251)
        ·
          refine ⟨47993663898939760960242377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31995775932626507306828251 47993663898939760960242377)
          ·
            refine ⟨35995247924204820720181783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47993663898939760960242377 35995247924204820720181783)
            ·
              refine ⟨53992871886307231080272675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35995247924204820720181783 53992871886307231080272675)
              ·
                refine ⟨80989307829460846620409013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53992871886307231080272675 80989307829460846620409013)
                ·
                  refine ⟨7592747609011954370663345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80989307829460846620409013 7592747609011954370663345)
                  ·
                    refine ⟨5694560706758965777997509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7592747609011954370663345 5694560706758965777997509)
                    ·
                      refine ⟨1067730132517306083374533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5694560706758965777997509 1067730132517306083374533)
                      ·
                        rfl

theorem cell23_2079397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_2079397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079397 prefixEnd_2079397 := by exact prefixLift 2079397
  have htrace : WordTrace (prefixWord ++ tailWord_2079397) baseStart_2079397 baseEnd_2079397 := by
    simpa [prefixWord, tailWord_2079397, baseEnd_2079397] using wordTrace_append hprefix tailTrace_2079397
  have hstable : (prefixWord ++ tailWord_2079397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079397).length < 2 ^ (prefixWord ++ tailWord_2079397).sum := by decide
  have hdescent : baseEnd_2079397 < baseStart_2079397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079407 : List Nat := [1, 1, 2, 1, 2, 5, 3, 8]
def baseStart_2079407 : Nat := 118140960795 + 2079407 * 2 ^ 59
def prefixEnd_2079407 : Nat := 4983230072969 + 3 ^ 40 * 2079407 * 2
def baseEnd_2079407 : Nat := 39545750641624112749981

theorem tailTrace_2079407 : CollatzResearch.WordTrace tailWord_2079407 prefixEnd_2079407 39545750641624112749981 := by
  unfold tailWord_2079407
  simp only [CollatzResearch.WordTrace]
  refine ⟨75842203977671048287012475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50561469318447365524674983 75842203977671048287012475)
  ·
    refine ⟨113763305966506572430518713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75842203977671048287012475 113763305966506572430518713)
    ·
      refine ⟨85322479474879929322889035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113763305966506572430518713 85322479474879929322889035)
      ·
        refine ⟨127983719212319893984333553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85322479474879929322889035 127983719212319893984333553)
        ·
          refine ⟨95987789409239920488250165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127983719212319893984333553 95987789409239920488250165)
          ·
            refine ⟨8998855257116242545773453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95987789409239920488250165 8998855257116242545773453)
            ·
              refine ⟨3374570721418590954665045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8998855257116242545773453 3374570721418590954665045)
              ·
                refine ⟨39545750641624112749981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3374570721418590954665045 39545750641624112749981)
                ·
                  rfl

theorem cell23_2079407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 8].length) (baseStart_2079407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079407 prefixEnd_2079407 := by exact prefixLift 2079407
  have htrace : WordTrace (prefixWord ++ tailWord_2079407) baseStart_2079407 baseEnd_2079407 := by
    simpa [prefixWord, tailWord_2079407, baseEnd_2079407] using wordTrace_append hprefix tailTrace_2079407
  have hstable : (prefixWord ++ tailWord_2079407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079407).length < 2 ^ (prefixWord ++ tailWord_2079407).sum := by decide
  have hdescent : baseEnd_2079407 < baseStart_2079407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079424 : List Nat := [2, 1, 1, 2, 4, 3, 3, 7]
def baseStart_2079424 : Nat := 118140960795 + 2079424 * 2 ^ 59
def prefixEnd_2079424 : Nat := 4983230072969 + 3 ^ 40 * 2079424 * 2
def baseEnd_2079424 : Nat := 39546073944258425101367

theorem tailTrace_2079424 : CollatzResearch.WordTrace tailWord_2079424 prefixEnd_2079424 39546073944258425101367 := by
  unfold tailWord_2079424
  simp only [CollatzResearch.WordTrace]
  refine ⟨37921412009304730095190663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50561882679072973460254217 37921412009304730095190663)
  ·
    refine ⟨56882118013957095142785995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37921412009304730095190663 56882118013957095142785995)
    ·
      refine ⟨85323177020935642714178993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56882118013957095142785995 85323177020935642714178993)
      ·
        refine ⟨63992382765701732035634245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85323177020935642714178993 63992382765701732035634245)
        ·
          refine ⟨11998571768569074756681421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63992382765701732035634245 11998571768569074756681421)
          ·
            refine ⟨4499464413213403033755533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11998571768569074756681421 4499464413213403033755533)
            ·
              refine ⟨1687299154955026137658325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4499464413213403033755533 1687299154955026137658325)
              ·
                refine ⟨39546073944258425101367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1687299154955026137658325 39546073944258425101367)
                ·
                  rfl

theorem cell23_2079424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 7].length) (baseStart_2079424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079424 prefixEnd_2079424 := by exact prefixLift 2079424
  have htrace : WordTrace (prefixWord ++ tailWord_2079424) baseStart_2079424 baseEnd_2079424 := by
    simpa [prefixWord, tailWord_2079424, baseEnd_2079424] using wordTrace_append hprefix tailTrace_2079424
  have hstable : (prefixWord ++ tailWord_2079424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079424).length < 2 ^ (prefixWord ++ tailWord_2079424).sum := by decide
  have hdescent : baseEnd_2079424 < baseStart_2079424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079438 : List Nat := [4, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3]
def baseStart_2079438 : Nat := 118140960795 + 2079438 * 2 ^ 59
def prefixEnd_2079438 : Nat := 4983230072969 + 3 ^ 40 * 2079438 * 2
def baseEnd_2079438 : Nat := 1067751185224140422961845

theorem tailTrace_2079438 : CollatzResearch.WordTrace tailWord_2079438 prefixEnd_2079438 1067751185224140422961845 := by
  unfold tailWord_2079438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9480416830069842572673871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50562223093705827054260645 9480416830069842572673871)
  ·
    refine ⟨14220625245104763859010807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9480416830069842572673871 14220625245104763859010807)
    ·
      refine ⟨21330937867657145788516211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14220625245104763859010807 21330937867657145788516211)
      ·
        refine ⟨31996406801485718682774317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21330937867657145788516211 31996406801485718682774317)
        ·
          refine ⟨11998652550557144506040369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31996406801485718682774317 11998652550557144506040369)
          ·
            refine ⟨8998989412917858379530277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11998652550557144506040369 8998989412917858379530277)
            ·
              refine ⟨1687310514922098446161927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8998989412917858379530277 1687310514922098446161927)
              ·
                refine ⟨2530965772383147669242891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687310514922098446161927 2530965772383147669242891)
                ·
                  refine ⟨3796448658574721503864337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530965772383147669242891 3796448658574721503864337)
                  ·
                    refine ⟨2847336493931041127898253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3796448658574721503864337 2847336493931041127898253)
                    ·
                      refine ⟨1067751185224140422961845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2847336493931041127898253 1067751185224140422961845)
                      ·
                        rfl

theorem cell23_2079438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_2079438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079438 prefixEnd_2079438 := by exact prefixLift 2079438
  have htrace : WordTrace (prefixWord ++ tailWord_2079438) baseStart_2079438 baseEnd_2079438 := by
    simpa [prefixWord, tailWord_2079438, baseEnd_2079438] using wordTrace_append hprefix tailTrace_2079438
  have hstable : (prefixWord ++ tailWord_2079438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079438).length < 2 ^ (prefixWord ++ tailWord_2079438).sum := by decide
  have hdescent : baseEnd_2079438 < baseStart_2079438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079445 : List Nat := [1, 3, 2, 5, 1, 2, 1, 2, 2, 4]
def baseStart_2079445 : Nat := 118140960795 + 2079445 * 2 ^ 59
def prefixEnd_2079445 : Nat := 4983230072969 + 3 ^ 40 * 2079445 * 2
def baseEnd_2079445 : Nat := 355918259862907298524771

theorem tailTrace_2079445 : CollatzResearch.WordTrace tailWord_2079445 prefixEnd_2079445 355918259862907298524771 := by
  unfold tailWord_2079445
  simp only [CollatzResearch.WordTrace]
  refine ⟨75843589951533380776895789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50562393301022253851263859 75843589951533380776895789)
  ·
    refine ⟨28441346231825017791335921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75843589951533380776895789 28441346231825017791335921)
    ·
      refine ⟨21331009673868763343501941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28441346231825017791335921 21331009673868763343501941)
      ·
        refine ⟨1999782156925196563453307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21331009673868763343501941 1999782156925196563453307)
        ·
          refine ⟨2999673235387794845179961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999782156925196563453307 2999673235387794845179961)
          ·
            refine ⟨2249754926540846133884971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2999673235387794845179961 2249754926540846133884971)
            ·
              refine ⟨3374632389811269200827457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249754926540846133884971 3374632389811269200827457)
              ·
                refine ⟨2530974292358451900620593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3374632389811269200827457 2530974292358451900620593)
                ·
                  refine ⟨1898230719268838925465445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2530974292358451900620593 1898230719268838925465445)
                  ·
                    refine ⟨355918259862907298524771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1898230719268838925465445 355918259862907298524771)
                    ·
                      rfl

theorem cell23_2079445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_2079445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079445 prefixEnd_2079445 := by exact prefixLift 2079445
  have htrace : WordTrace (prefixWord ++ tailWord_2079445) baseStart_2079445 baseEnd_2079445 := by
    simpa [prefixWord, tailWord_2079445, baseEnd_2079445] using wordTrace_append hprefix tailTrace_2079445
  have hstable : (prefixWord ++ tailWord_2079445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079445).length < 2 ^ (prefixWord ++ tailWord_2079445).sum := by decide
  have hdescent : baseEnd_2079445 < baseStart_2079445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079452 : List Nat := [2, 2, 5, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_2079452 : Nat := 118140960795 + 2079452 * 2 ^ 59
def prefixEnd_2079452 : Nat := 4983230072969 + 3 ^ 40 * 2079452 * 2
def baseEnd_2079452 : Nat := 1067758373953303368186781

theorem tailTrace_2079452 : CollatzResearch.WordTrace tailWord_2079452 prefixEnd_2079452 1067758373953303368186781 := by
  unfold tailWord_2079452
  simp only [CollatzResearch.WordTrace]
  refine ⟨37921922631254010486200305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50562563508338680648267073 37921922631254010486200305)
  ·
    refine ⟨28441441973440507864650229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37921922631254010486200305 28441441973440507864650229)
    ·
      refine ⟨2666385185010047612310959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28441441973440507864650229 2666385185010047612310959)
      ·
        refine ⟨3999577777515071418466439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2666385185010047612310959 3999577777515071418466439)
        ·
          refine ⟨5999366666272607127699659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3999577777515071418466439 5999366666272607127699659)
          ·
            refine ⟨8999049999408910691549489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5999366666272607127699659 8999049999408910691549489)
            ·
              refine ⟨6749287499556683018662117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8999049999408910691549489 6749287499556683018662117)
              ·
                refine ⟨1265491406166878065999147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6749287499556683018662117 1265491406166878065999147)
                ·
                  refine ⟨1898237109250317098998721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1265491406166878065999147 1898237109250317098998721)
                  ·
                    refine ⟨1423677831937737824249041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1898237109250317098998721 1423677831937737824249041)
                    ·
                      refine ⟨1067758373953303368186781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1423677831937737824249041 1067758373953303368186781)
                      ·
                        rfl

theorem cell23_2079452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_2079452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079452 prefixEnd_2079452 := by exact prefixLift 2079452
  have htrace : WordTrace (prefixWord ++ tailWord_2079452) baseStart_2079452 baseEnd_2079452 := by
    simpa [prefixWord, tailWord_2079452, baseEnd_2079452] using wordTrace_append hprefix tailTrace_2079452
  have hstable : (prefixWord ++ tailWord_2079452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079452).length < 2 ^ (prefixWord ++ tailWord_2079452).sum := by decide
  have hdescent : baseEnd_2079452 < baseStart_2079452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079497 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 9]
def baseStart_2079497 : Nat := 118140960795 + 2079497 * 2 ^ 59
def prefixEnd_2079497 : Nat := 4983230072969 + 3 ^ 40 * 2079497 * 2
def baseEnd_2079497 : Nat := 118642386731417299124897

theorem tailTrace_2079497 : CollatzResearch.WordTrace tailWord_2079497 prefixEnd_2079497 118642386731417299124897 := by
  unfold tailWord_2079497
  simp only [CollatzResearch.WordTrace]
  refine ⟨75845486547344993657788745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50563657698229995771859163 75845486547344993657788745)
  ·
    refine ⟨56884114910508745243341559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75845486547344993657788745 56884114910508745243341559)
    ·
      refine ⟨85326172365763117865012339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56884114910508745243341559 85326172365763117865012339)
      ·
        refine ⟨127989258548644676797518509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85326172365763117865012339 127989258548644676797518509)
        ·
          refine ⟨47995971955741753799069441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127989258548644676797518509 47995971955741753799069441)
          ·
            refine ⟨35996978966806315349302081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47995971955741753799069441 35996978966806315349302081)
            ·
              refine ⟨26997734225104736511976561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35996978966806315349302081 26997734225104736511976561)
              ·
                refine ⟨20248300668828552383982421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26997734225104736511976561 20248300668828552383982421)
                ·
                  refine ⟨118642386731417299124897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20248300668828552383982421 118642386731417299124897)
                  ·
                    rfl

theorem cell23_2079497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 9].length) (baseStart_2079497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079497 prefixEnd_2079497 := by exact prefixLift 2079497
  have htrace : WordTrace (prefixWord ++ tailWord_2079497) baseStart_2079497 baseEnd_2079497 := by
    simpa [prefixWord, tailWord_2079497, baseEnd_2079497] using wordTrace_append hprefix tailTrace_2079497
  have hstable : (prefixWord ++ tailWord_2079497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079497).length < 2 ^ (prefixWord ++ tailWord_2079497).sum := by decide
  have hdescent : baseEnd_2079497 < baseStart_2079497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079507 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 7]
def baseStart_2079507 : Nat := 118140960795 + 2079507 * 2 ^ 59
def prefixEnd_2079507 : Nat := 4983230072969 + 3 ^ 40 * 2079507 * 2
def baseEnd_2079507 : Nat := 1067786615389300652999027

theorem tailTrace_2079507 : CollatzResearch.WordTrace tailWord_2079507 prefixEnd_2079507 1067786615389300652999027 := by
  unfold tailWord_2079507
  simp only [CollatzResearch.WordTrace]
  refine ⟨75845851277308765365652775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50563900851539176910435183 75845851277308765365652775)
  ·
    refine ⟨113768776915963148048479163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75845851277308765365652775 113768776915963148048479163)
    ·
      refine ⟨170653165373944722072718745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113768776915963148048479163 170653165373944722072718745)
      ·
        refine ⟨127989874030458541554539059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170653165373944722072718745 127989874030458541554539059)
        ·
          refine ⟨191984811045687812331808589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127989874030458541554539059 191984811045687812331808589)
          ·
            refine ⟨71994304142132929624428221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191984811045687812331808589 71994304142132929624428221)
            ·
              refine ⟨26997864053299848609160583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71994304142132929624428221 26997864053299848609160583)
              ·
                refine ⟨40496796079949772913740875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26997864053299848609160583 40496796079949772913740875)
                ·
                  refine ⟨60745194119924659370611313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40496796079949772913740875 60745194119924659370611313)
                  ·
                    refine ⟨45558895589943494527958485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60745194119924659370611313 45558895589943494527958485)
                    ·
                      refine ⟨1067786615389300652999027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45558895589943494527958485 1067786615389300652999027)
                      ·
                        rfl

theorem cell23_2079507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_2079507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079507 prefixEnd_2079507 := by exact prefixLift 2079507
  have htrace : WordTrace (prefixWord ++ tailWord_2079507) baseStart_2079507 baseEnd_2079507 := by
    simpa [prefixWord, tailWord_2079507, baseEnd_2079507] using wordTrace_append hprefix tailTrace_2079507
  have hstable : (prefixWord ++ tailWord_2079507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079507).length < 2 ^ (prefixWord ++ tailWord_2079507).sum := by decide
  have hdescent : baseEnd_2079507 < baseStart_2079507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079565 : List Nat := [1, 6, 1, 2, 2, 1, 1, 4, 5]
def baseStart_2079565 : Nat := 118140960795 + 2079565 * 2 ^ 59
def prefixEnd_2079565 : Nat := 4983230072969 + 3 ^ 40 * 2079565 * 2
def baseEnd_2079565 : Nat := 118646266363029047341529

theorem tailTrace_2079565 : CollatzResearch.WordTrace tailWord_2079565 prefixEnd_2079565 118646266363029047341529 := by
  unfold tailWord_2079565
  simp only [CollatzResearch.WordTrace]
  refine ⟨75847966711098641271264149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50565311140732427514176099 75847966711098641271264149)
  ·
    refine ⟨3555373439582748809590507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75847966711098641271264149 3555373439582748809590507)
    ·
      refine ⟨5333060159374123214385761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3555373439582748809590507 5333060159374123214385761)
      ·
        refine ⟨3999795119530592410789321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5333060159374123214385761 3999795119530592410789321)
        ·
          refine ⟨2999846339647944308091991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3999795119530592410789321 2999846339647944308091991)
          ·
            refine ⟨4499769509471916462137987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999846339647944308091991 4499769509471916462137987)
            ·
              refine ⟨6749654264207874693206981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4499769509471916462137987 6749654264207874693206981)
              ·
                refine ⟨1265560174538976504976309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6749654264207874693206981 1265560174538976504976309)
                ·
                  refine ⟨118646266363029047341529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1265560174538976504976309 118646266363029047341529)
                  ·
                    rfl

theorem cell23_2079565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_2079565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079565 prefixEnd_2079565 := by exact prefixLift 2079565
  have htrace : WordTrace (prefixWord ++ tailWord_2079565) baseStart_2079565 baseEnd_2079565 := by
    simpa [prefixWord, tailWord_2079565, baseEnd_2079565] using wordTrace_append hprefix tailTrace_2079565
  have hstable : (prefixWord ++ tailWord_2079565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079565).length < 2 ^ (prefixWord ++ tailWord_2079565).sum := by decide
  have hdescent : baseEnd_2079565 < baseStart_2079565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079591 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 5, 4]
def baseStart_2079591 : Nat := 118140960795 + 2079591 * 2 ^ 59
def prefixEnd_2079591 : Nat := 4983230072969 + 3 ^ 40 * 2079591 * 2
def baseEnd_2079591 : Nat := 355943249254759441449547

theorem tailTrace_2079591 : CollatzResearch.WordTrace tailWord_2079591 prefixEnd_2079591 355943249254759441449547 := by
  unfold tailWord_2079591
  simp only [CollatzResearch.WordTrace]
  refine ⟨75848915009004447711710627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50565943339336298474473751 75848915009004447711710627)
  ·
    refine ⟨113773372513506671567565941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75848915009004447711710627 113773372513506671567565941)
    ·
      refine ⟨10666253673141250459459307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113773372513506671567565941 10666253673141250459459307)
      ·
        refine ⟨15999380509711875689188961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10666253673141250459459307 15999380509711875689188961)
        ·
          refine ⟨11999535382283906766891721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15999380509711875689188961 11999535382283906766891721)
          ·
            refine ⟨8999651536712930075168791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11999535382283906766891721 8999651536712930075168791)
            ·
              refine ⟨13499477305069395112753187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8999651536712930075168791 13499477305069395112753187)
              ·
                refine ⟨20249215957604092669129781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13499477305069395112753187 20249215957604092669129781)
                ·
                  refine ⟨1898363996025383687730917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20249215957604092669129781 1898363996025383687730917)
                  ·
                    refine ⟨355943249254759441449547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1898363996025383687730917 355943249254759441449547)
                    ·
                      rfl

theorem cell23_2079591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_2079591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079591 prefixEnd_2079591 := by exact prefixLift 2079591
  have htrace : WordTrace (prefixWord ++ tailWord_2079591) baseStart_2079591 baseEnd_2079591 := by
    simpa [prefixWord, tailWord_2079591, baseEnd_2079591] using wordTrace_append hprefix tailTrace_2079591
  have hstable : (prefixWord ++ tailWord_2079591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079591).length < 2 ^ (prefixWord ++ tailWord_2079591).sum := by decide
  have hdescent : baseEnd_2079591 < baseStart_2079591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079598 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2079598 : Nat := 118140960795 + 2079598 * 2 ^ 59
def prefixEnd_2079598 : Nat := 4983230072969 + 3 ^ 40 * 2079598 * 2
def baseEnd_2079598 : Nat := 1067833342128859796961109

theorem tailTrace_2079598 : CollatzResearch.WordTrace tailWord_2079598 prefixEnd_2079598 1067833342128859796961109 := by
  unfold tailWord_2079598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9481146289997385988401931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50566113546652725271476965 9481146289997385988401931)
  ·
    refine ⟨14221719434996078982602897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9481146289997385988401931 14221719434996078982602897)
    ·
      refine ⟨10666289576247059236952173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14221719434996078982602897 10666289576247059236952173)
      ·
        refine ⟨3999858591092647213857065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10666289576247059236952173 3999858591092647213857065)
        ·
          refine ⟨2999893943319485410392799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3999858591092647213857065 2999893943319485410392799)
          ·
            refine ⟨4499840914979228115589199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999893943319485410392799 4499840914979228115589199)
            ·
              refine ⟨6749761372468842173383799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4499840914979228115589199 6749761372468842173383799)
              ·
                refine ⟨10124642058703263260075699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6749761372468842173383799 10124642058703263260075699)
                ·
                  refine ⟨15186963088054894890113549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10124642058703263260075699 15186963088054894890113549)
                  ·
                    refine ⟨5695111158020585583792581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15186963088054894890113549 5695111158020585583792581)
                    ·
                      refine ⟨1067833342128859796961109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5695111158020585583792581 1067833342128859796961109)
                      ·
                        rfl

theorem cell23_2079598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2079598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079598 prefixEnd_2079598 := by exact prefixLift 2079598
  have htrace : WordTrace (prefixWord ++ tailWord_2079598) baseStart_2079598 baseEnd_2079598 := by
    simpa [prefixWord, tailWord_2079598, baseEnd_2079598] using wordTrace_append hprefix tailTrace_2079598
  have hstable : (prefixWord ++ tailWord_2079598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079598).length < 2 ^ (prefixWord ++ tailWord_2079598).sum := by decide
  have hdescent : baseEnd_2079598 < baseStart_2079598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079601 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 1, 4, 3]
def baseStart_2079601 : Nat := 118140960795 + 2079601 * 2 ^ 59
def prefixEnd_2079601 : Nat := 4983230072969 + 3 ^ 40 * 2079601 * 2
def baseEnd_2079601 : Nat := 1067834882570823285223595

theorem tailTrace_2079601 : CollatzResearch.WordTrace tailWord_2079601 prefixEnd_2079601 1067834882570823285223595 := by
  unfold tailWord_2079601
  simp only [CollatzResearch.WordTrace]
  refine ⟨75849279738968219419574657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50566186492645479613049771 75849279738968219419574657)
  ·
    refine ⟨56886959804226164564680993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75849279738968219419574657 56886959804226164564680993)
    ·
      refine ⟨42665219853169623423510745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56886959804226164564680993 42665219853169623423510745)
      ·
        refine ⟨31998914889877217567633059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42665219853169623423510745 31998914889877217567633059)
        ·
          refine ⟨47998372334815826351449589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31998914889877217567633059 47998372334815826351449589)
          ·
            refine ⟨4499847406388983720448399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47998372334815826351449589 4499847406388983720448399)
            ·
              refine ⟨6749771109583475580672599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4499847406388983720448399 6749771109583475580672599)
              ·
                refine ⟨10124656664375213371008899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6749771109583475580672599 10124656664375213371008899)
                ·
                  refine ⟨15186984996562820056513349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10124656664375213371008899 15186984996562820056513349)
                  ·
                    refine ⟨2847559686855528760596253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15186984996562820056513349 2847559686855528760596253)
                    ·
                      refine ⟨1067834882570823285223595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2847559686855528760596253 1067834882570823285223595)
                      ·
                        rfl

theorem cell23_2079601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_2079601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079601 prefixEnd_2079601 := by exact prefixLift 2079601
  have htrace : WordTrace (prefixWord ++ tailWord_2079601) baseStart_2079601 baseEnd_2079601 := by
    simpa [prefixWord, tailWord_2079601, baseEnd_2079601] using wordTrace_append hprefix tailTrace_2079601
  have hstable : (prefixWord ++ tailWord_2079601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079601).length < 2 ^ (prefixWord ++ tailWord_2079601).sum := by decide
  have hdescent : baseEnd_2079601 < baseStart_2079601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079621 : List Nat := [1, 3, 1, 1, 3, 3, 3, 2, 6]
def baseStart_2079621 : Nat := 118140960795 + 2079621 * 2 ^ 59
def prefixEnd_2079621 : Nat := 4983230072969 + 3 ^ 40 * 2079621 * 2
def baseEnd_2079621 : Nat := 118649461353768134108167

theorem tailTrace_2079621 : CollatzResearch.WordTrace tailWord_2079621 prefixEnd_2079621 118649461353768134108167 := by
  unfold tailWord_2079621
  simp only [CollatzResearch.WordTrace]
  refine ⟨75850009198895762835302717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50566672799263841890201811 75850009198895762835302717)
  ·
    refine ⟨28443753449585911063238519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75850009198895762835302717 28443753449585911063238519)
    ·
      refine ⟨42665630174378866594857779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28443753449585911063238519 42665630174378866594857779)
      ·
        refine ⟨63998445261568299892286669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42665630174378866594857779 63998445261568299892286669)
        ·
          refine ⟨23999416973088112459607501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63998445261568299892286669 23999416973088112459607501)
          ·
            refine ⟨8999781364908042172352813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23999416973088112459607501 8999781364908042172352813)
            ·
              refine ⟨3374918011840515814632305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8999781364908042172352813 3374918011840515814632305)
              ·
                refine ⟨2531188508880386860974229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3374918011840515814632305 2531188508880386860974229)
                ·
                  refine ⟨118649461353768134108167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2531188508880386860974229 118649461353768134108167)
                  ·
                    rfl

theorem cell23_2079621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_2079621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079621 prefixEnd_2079621 := by exact prefixLift 2079621
  have htrace : WordTrace (prefixWord ++ tailWord_2079621) baseStart_2079621 baseEnd_2079621 := by
    simpa [prefixWord, tailWord_2079621, baseEnd_2079621] using wordTrace_append hprefix tailTrace_2079621
  have hstable : (prefixWord ++ tailWord_2079621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079621).length < 2 ^ (prefixWord ++ tailWord_2079621).sum := by decide
  have hdescent : baseEnd_2079621 < baseStart_2079621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079648 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 3, 1, 3]
def baseStart_2079648 : Nat := 118140960795 + 2079648 * 2 ^ 59
def prefixEnd_2079648 : Nat := 4983230072969 + 3 ^ 40 * 2079648 * 2
def baseEnd_2079648 : Nat := 1067859016161584601335879

theorem tailTrace_2079648 : CollatzResearch.WordTrace tailWord_2079648 prefixEnd_2079648 1067859016161584601335879 := by
  unfold tailWord_2079648
  simp only [CollatzResearch.WordTrace]
  refine ⟨37925496984898973223267799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50567329313198630964357065 37925496984898973223267799)
  ·
    refine ⟨56888245477348459834901699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37925496984898973223267799 56888245477348459834901699)
    ·
      refine ⟨85332368216022689752352549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56888245477348459834901699 85332368216022689752352549)
      ·
        refine ⟨15999819040504254328566103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85332368216022689752352549 15999819040504254328566103)
        ·
          refine ⟨23999728560756381492849155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15999819040504254328566103 23999728560756381492849155)
          ·
            refine ⟨35999592841134572239273733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23999728560756381492849155 35999592841134572239273733)
            ·
              refine ⟨6749923657712732294863825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35999592841134572239273733 6749923657712732294863825)
              ·
                refine ⟨5062442743284549221147869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6749923657712732294863825 5062442743284549221147869)
                ·
                  refine ⟨1898416028731705957930451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5062442743284549221147869 1898416028731705957930451)
                  ·
                    refine ⟨2847624043097558936895677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1898416028731705957930451 2847624043097558936895677)
                    ·
                      refine ⟨1067859016161584601335879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2847624043097558936895677 1067859016161584601335879)
                      ·
                        rfl

theorem cell23_2079648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_2079648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079648 prefixEnd_2079648 := by exact prefixLift 2079648
  have htrace : WordTrace (prefixWord ++ tailWord_2079648) baseStart_2079648 baseEnd_2079648 := by
    simpa [prefixWord, tailWord_2079648, baseEnd_2079648] using wordTrace_append hprefix tailTrace_2079648
  have hstable : (prefixWord ++ tailWord_2079648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079648).length < 2 ^ (prefixWord ++ tailWord_2079648).sum := by decide
  have hdescent : baseEnd_2079648 < baseStart_2079648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079651 : List Nat := [1, 1, 1, 4, 1, 2, 3, 4, 1, 5]
def baseStart_2079651 : Nat := 118140960795 + 2079651 * 2 ^ 59
def prefixEnd_2079651 : Nat := 4983230072969 + 3 ^ 40 * 2079651 * 2
def baseEnd_2079651 : Nat := 355953518867849363199455

theorem tailTrace_2079651 : CollatzResearch.WordTrace tailWord_2079651 prefixEnd_2079651 355953518867849363199455 := by
  unfold tailWord_2079651
  simp only [CollatzResearch.WordTrace]
  refine ⟨75851103388787077958894807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50567402259191385305929871 75851103388787077958894807)
  ·
    refine ⟨113776655083180616938342211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75851103388787077958894807 113776655083180616938342211)
    ·
      refine ⟨170664982624770925407513317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113776655083180616938342211 170664982624770925407513317)
      ·
        refine ⟨31999684242144548513908747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170664982624770925407513317 31999684242144548513908747)
        ·
          refine ⟨47999526363216822770863121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31999684242144548513908747 47999526363216822770863121)
          ·
            refine ⟨35999644772412617078147341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47999526363216822770863121 35999644772412617078147341)
            ·
              refine ⟨13499866789654731404305253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35999644772412617078147341 13499866789654731404305253)
              ·
                refine ⟨2531225023060262138307235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13499866789654731404305253 2531225023060262138307235)
                ·
                  refine ⟨3796837534590393207460853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531225023060262138307235 3796837534590393207460853)
                  ·
                    refine ⟨355953518867849363199455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3796837534590393207460853 355953518867849363199455)
                    ·
                      rfl

theorem cell23_2079651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 5].length) (baseStart_2079651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079651 prefixEnd_2079651 := by exact prefixLift 2079651
  have htrace : WordTrace (prefixWord ++ tailWord_2079651) baseStart_2079651 baseEnd_2079651 := by
    simpa [prefixWord, tailWord_2079651, baseEnd_2079651] using wordTrace_append hprefix tailTrace_2079651
  have hstable : (prefixWord ++ tailWord_2079651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079651).length < 2 ^ (prefixWord ++ tailWord_2079651).sum := by decide
  have hdescent : baseEnd_2079651 < baseStart_2079651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079691 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 5]
def baseStart_2079691 : Nat := 118140960795 + 2079691 * 2 ^ 59
def prefixEnd_2079691 : Nat := 4983230072969 + 3 ^ 40 * 2079691 * 2
def baseEnd_2079691 : Nat := 1067881095829727933098181

theorem tailTrace_2079691 : CollatzResearch.WordTrace tailWord_2079691 prefixEnd_2079691 1067881095829727933098181 := by
  unfold tailWord_2079691
  simp only [CollatzResearch.WordTrace]
  refine ⟨75852562308642164790350927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50568374872428109860233951 75852562308642164790350927)
  ·
    refine ⟨113778843462963247185526391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75852562308642164790350927 113778843462963247185526391)
    ·
      refine ⟨170668265194444870778289587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113778843462963247185526391 170668265194444870778289587)
      ·
        refine ⟨256002397791667306167434381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170668265194444870778289587 256002397791667306167434381)
        ·
          refine ⟨96000899171875239812787893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256002397791667306167434381 96000899171875239812787893)
          ·
            refine ⟨9000084297363303732448865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96000899171875239812787893 9000084297363303732448865)
            ·
              refine ⟨6750063223022477799336649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9000084297363303732448865 6750063223022477799336649)
              ·
                refine ⟨5062547417266858349502487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6750063223022477799336649 5062547417266858349502487)
                ·
                  refine ⟨7593821125900287524253731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5062547417266858349502487 7593821125900287524253731)
                  ·
                    refine ⟨11390731688850431286380597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7593821125900287524253731 11390731688850431286380597)
                    ·
                      refine ⟨1067881095829727933098181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11390731688850431286380597 1067881095829727933098181)
                      ·
                        rfl

theorem cell23_2079691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 5].length) (baseStart_2079691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079691 prefixEnd_2079691 := by exact prefixLift 2079691
  have htrace : WordTrace (prefixWord ++ tailWord_2079691) baseStart_2079691 baseEnd_2079691 := by
    simpa [prefixWord, tailWord_2079691, baseEnd_2079691] using wordTrace_append hprefix tailTrace_2079691
  have hstable : (prefixWord ++ tailWord_2079691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079691).length < 2 ^ (prefixWord ++ tailWord_2079691).sum := by decide
  have hdescent : baseEnd_2079691 < baseStart_2079691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079702 : List Nat := [5, 2, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2079702 : Nat := 118140960795 + 2079702 * 2 ^ 59
def prefixEnd_2079702 : Nat := 4983230072969 + 3 ^ 40 * 2079702 * 2
def baseEnd_2079702 : Nat := 355962248038975796686877

theorem tailTrace_2079702 : CollatzResearch.WordTrace tailWord_2079702 prefixEnd_2079702 355962248038975796686877 := by
  unfold tailWord_2079702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4740810219475144604312585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50568642341068209112667573 4740810219475144604312585)
  ·
    refine ⟨3555607664606358453234439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4740810219475144604312585 3555607664606358453234439)
    ·
      refine ⟨5333411496909537679851659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3555607664606358453234439 5333411496909537679851659)
      ·
        refine ⟨8000117245364306519777489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5333411496909537679851659 8000117245364306519777489)
        ·
          refine ⟨6000087934023229889833117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8000117245364306519777489 6000087934023229889833117)
          ·
            refine ⟨2250032975258711208687419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6000087934023229889833117 2250032975258711208687419)
            ·
              refine ⟨3375049462888066813031129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250032975258711208687419 3375049462888066813031129)
              ·
                refine ⟨2531287097166050109773347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3375049462888066813031129 2531287097166050109773347)
                ·
                  refine ⟨3796930645749075164660021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531287097166050109773347 3796930645749075164660021)
                  ·
                    refine ⟨355962248038975796686877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3796930645749075164660021 355962248038975796686877)
                    ·
                      rfl

theorem cell23_2079702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2079702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079702 prefixEnd_2079702 := by exact prefixLift 2079702
  have htrace : WordTrace (prefixWord ++ tailWord_2079702) baseStart_2079702 baseEnd_2079702 := by
    simpa [prefixWord, tailWord_2079702, baseEnd_2079702] using wordTrace_append hprefix tailTrace_2079702
  have hstable : (prefixWord ++ tailWord_2079702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079702).length < 2 ^ (prefixWord ++ tailWord_2079702).sum := by decide
  have hdescent : baseEnd_2079702 < baseStart_2079702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079705 : List Nat := [1, 2, 1, 2, 5, 3, 1, 2, 1, 1, 4]
def baseStart_2079705 : Nat := 118140960795 + 2079705 * 2 ^ 59
def prefixEnd_2079705 : Nat := 4983230072969 + 3 ^ 40 * 2079705 * 2
def baseEnd_2079705 : Nat := 1067888284558890878323117

theorem tailTrace_2079705 : CollatzResearch.WordTrace tailWord_2079705 prefixEnd_2079705 1067888284558890878323117 := by
  unfold tailWord_2079705
  simp only [CollatzResearch.WordTrace]
  refine ⟨75853072930591445181360569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50568715287060963454240379 75853072930591445181360569)
  ·
    refine ⟨56889804697943583886020427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75853072930591445181360569 56889804697943583886020427)
    ·
      refine ⟨85334707046915375829030641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56889804697943583886020427 85334707046915375829030641)
      ·
        refine ⟨64001030285186531871772981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85334707046915375829030641 64001030285186531871772981)
        ·
          refine ⟨6000096589236237362978717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64001030285186531871772981 6000096589236237362978717)
          ·
            refine ⟨2250036220963589011117019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6000096589236237362978717 2250036220963589011117019)
            ·
              refine ⟨3375054331445383516675529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250036220963589011117019 3375054331445383516675529)
              ·
                refine ⟨2531290748584037637506647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3375054331445383516675529 2531290748584037637506647)
                ·
                  refine ⟨3796936122876056456259971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531290748584037637506647 3796936122876056456259971)
                  ·
                    refine ⟨5695404184314084684389957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3796936122876056456259971 5695404184314084684389957)
                    ·
                      refine ⟨1067888284558890878323117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5695404184314084684389957 1067888284558890878323117)
                      ·
                        rfl

theorem cell23_2079705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_2079705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079705 prefixEnd_2079705 := by exact prefixLift 2079705
  have htrace : WordTrace (prefixWord ++ tailWord_2079705) baseStart_2079705 baseEnd_2079705 := by
    simpa [prefixWord, tailWord_2079705, baseEnd_2079705] using wordTrace_append hprefix tailTrace_2079705
  have hstable : (prefixWord ++ tailWord_2079705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079705).length < 2 ^ (prefixWord ++ tailWord_2079705).sum := by decide
  have hdescent : baseEnd_2079705 < baseStart_2079705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079733 : List Nat := [1, 3, 5, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2079733 : Nat := 118140960795 + 2079733 * 2 ^ 59
def prefixEnd_2079733 : Nat := 4983230072969 + 3 ^ 40 * 2079733 * 2
def baseEnd_2079733 : Nat := 1067902662017216768772989

theorem tailTrace_2079733 : CollatzResearch.WordTrace tailWord_2079733 prefixEnd_2079733 1067902662017216768772989 := by
  unfold tailWord_2079733
  simp only [CollatzResearch.WordTrace]
  refine ⟨75854094174490005963379853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50569396116326670642253235 75854094174490005963379853)
  ·
    refine ⟨28445285315433752236267445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75854094174490005963379853 28445285315433752236267445)
    ·
      refine ⟨2666745498321914272150073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28445285315433752236267445 2666745498321914272150073)
      ·
        refine ⟨2000059123741435704112555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2666745498321914272150073 2000059123741435704112555)
        ·
          refine ⟨3000088685612153556168833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000059123741435704112555 3000088685612153556168833)
          ·
            refine ⟨2250066514209115167126625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3000088685612153556168833 2250066514209115167126625)
            ·
              refine ⟨1687549885656836375344969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2250066514209115167126625 1687549885656836375344969)
              ·
                refine ⟨1265662414242627281508727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1687549885656836375344969 1265662414242627281508727)
                ·
                  refine ⟨1898493621363940922263091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1265662414242627281508727 1898493621363940922263091)
                  ·
                    refine ⟨2847740432045911383394637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1898493621363940922263091 2847740432045911383394637)
                    ·
                      refine ⟨1067902662017216768772989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2847740432045911383394637 1067902662017216768772989)
                      ·
                        rfl

theorem cell23_2079733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2079733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079733 prefixEnd_2079733 := by exact prefixLift 2079733
  have htrace : WordTrace (prefixWord ++ tailWord_2079733) baseStart_2079733 baseEnd_2079733 := by
    simpa [prefixWord, tailWord_2079733, baseEnd_2079733] using wordTrace_append hprefix tailTrace_2079733
  have hstable : (prefixWord ++ tailWord_2079733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079733).length < 2 ^ (prefixWord ++ tailWord_2079733).sum := by decide
  have hdescent : baseEnd_2079733 < baseStart_2079733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079738 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3]
def baseStart_2079738 : Nat := 118140960795 + 2079738 * 2 ^ 59
def prefixEnd_2079738 : Nat := 4983230072969 + 3 ^ 40 * 2079738 * 2
def baseEnd_2079738 : Nat := 1067905229420489249210465

theorem tailTrace_2079738 : CollatzResearch.WordTrace tailWord_2079738 prefixEnd_2079738 1067905229420489249210465 := by
  unfold tailWord_2079738
  simp only [CollatzResearch.WordTrace]
  refine ⟨18963569134867972954327967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50569517692981261211541245 18963569134867972954327967)
  ·
    refine ⟨28445353702301959431491951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18963569134867972954327967 28445353702301959431491951)
    ·
      refine ⟨42668030553452939147237927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28445353702301959431491951 42668030553452939147237927)
      ·
        refine ⟨64002045830179408720856891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42668030553452939147237927 64002045830179408720856891)
        ·
          refine ⟨96003068745269113081285337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64002045830179408720856891 96003068745269113081285337)
          ·
            refine ⟨72002301558951834810964003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96003068745269113081285337 72002301558951834810964003)
            ·
              refine ⟨108003452338427752216446005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72002301558951834810964003 108003452338427752216446005)
              ·
                refine ⟨10125323656727601770291813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108003452338427752216446005 10125323656727601770291813)
                ·
                  refine ⟨1898498185636425331929715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10125323656727601770291813 1898498185636425331929715)
                  ·
                    refine ⟨2847747278454637997894573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1898498185636425331929715 2847747278454637997894573)
                    ·
                      refine ⟨1067905229420489249210465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2847747278454637997894573 1067905229420489249210465)
                      ·
                        rfl

theorem cell23_2079738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_2079738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079738 prefixEnd_2079738 := by exact prefixLift 2079738
  have htrace : WordTrace (prefixWord ++ tailWord_2079738) baseStart_2079738 baseEnd_2079738 := by
    simpa [prefixWord, tailWord_2079738, baseEnd_2079738] using wordTrace_append hprefix tailTrace_2079738
  have hstable : (prefixWord ++ tailWord_2079738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079738).length < 2 ^ (prefixWord ++ tailWord_2079738).sum := by decide
  have hdescent : baseEnd_2079738 < baseStart_2079738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079755 : List Nat := [1, 1, 1, 1, 6, 2, 2, 3, 2, 1, 3]
def baseStart_2079755 : Nat := 118140960795 + 2079755 * 2 ^ 59
def prefixEnd_2079755 : Nat := 4983230072969 + 3 ^ 40 * 2079755 * 2
def baseEnd_2079755 : Nat := 1067913958591615682697887

theorem tailTrace_2079755 : CollatzResearch.WordTrace tailWord_2079755 prefixEnd_2079755 1067913958591615682697887 := by
  unfold tailWord_2079755
  simp only [CollatzResearch.WordTrace]
  refine ⟨75854896580410303720680719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50569931053606869147120479 75854896580410303720680719)
  ·
    refine ⟨113782344870615455581021079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75854896580410303720680719 113782344870615455581021079)
    ·
      refine ⟨170673517305923183371531619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113782344870615455581021079 170673517305923183371531619)
      ·
        refine ⟨256010275958884775057297429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170673517305923183371531619 256010275958884775057297429)
        ·
          refine ⟨12000481685572723830810817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 256010275958884775057297429 12000481685572723830810817)
          ·
            refine ⟨9000361264179542873108113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12000481685572723830810817 9000361264179542873108113)
            ·
              refine ⟨6750270948134657154831085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9000361264179542873108113 6750270948134657154831085)
              ·
                refine ⟨2531351605550496433061657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6750270948134657154831085 2531351605550496433061657)
                ·
                  refine ⟨1898513704162872324796243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2531351605550496433061657 1898513704162872324796243)
                  ·
                    refine ⟨2847770556244308487194365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1898513704162872324796243 2847770556244308487194365)
                    ·
                      refine ⟨1067913958591615682697887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2847770556244308487194365 1067913958591615682697887)
                      ·
                        rfl

theorem cell23_2079755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 1, 3].length) (baseStart_2079755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079755 prefixEnd_2079755 := by exact prefixLift 2079755
  have htrace : WordTrace (prefixWord ++ tailWord_2079755) baseStart_2079755 baseEnd_2079755 := by
    simpa [prefixWord, tailWord_2079755, baseEnd_2079755] using wordTrace_append hprefix tailTrace_2079755
  have hstable : (prefixWord ++ tailWord_2079755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079755).length < 2 ^ (prefixWord ++ tailWord_2079755).sum := by decide
  have hdescent : baseEnd_2079755 < baseStart_2079755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079765 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 3, 3, 2]
def baseStart_2079765 : Nat := 118140960795 + 2079765 * 2 ^ 59
def prefixEnd_2079765 : Nat := 4983230072969 + 3 ^ 40 * 2079765 * 2
def baseEnd_2079765 : Nat := 1067919093398160643572841

theorem tailTrace_2079765 : CollatzResearch.WordTrace tailWord_2079765 prefixEnd_2079765 1067919093398160643572841 := by
  unfold tailWord_2079765
  simp only [CollatzResearch.WordTrace]
  refine ⟨75855261310374075428544749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50570174206916050285696499 75855261310374075428544749)
  ·
    refine ⟨28445722991390278285704281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75855261310374075428544749 28445722991390278285704281)
    ·
      refine ⟨21334292243542708714278211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28445722991390278285704281 21334292243542708714278211)
      ·
        refine ⟨32001438365314063071417317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21334292243542708714278211 32001438365314063071417317)
        ·
          refine ⟨6000269693496386825890747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32001438365314063071417317 6000269693496386825890747)
          ·
            refine ⟨9000404540244580238836121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6000269693496386825890747 9000404540244580238836121)
            ·
              refine ⟨6750303405183435179127091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9000404540244580238836121 6750303405183435179127091)
              ·
                refine ⟨10125455107775152768690637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6750303405183435179127091 10125455107775152768690637)
                ·
                  refine ⟨3797045665415682288258989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10125455107775152768690637 3797045665415682288258989)
                  ·
                    refine ⟨1423892124530880858097121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3797045665415682288258989 1423892124530880858097121)
                    ·
                      refine ⟨1067919093398160643572841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1423892124530880858097121 1067919093398160643572841)
                      ·
                        rfl

theorem cell23_2079765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_2079765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079765 prefixEnd_2079765 := by exact prefixLift 2079765
  have htrace : WordTrace (prefixWord ++ tailWord_2079765) baseStart_2079765 baseEnd_2079765 := by
    simpa [prefixWord, tailWord_2079765, baseEnd_2079765] using wordTrace_append hprefix tailTrace_2079765
  have hstable : (prefixWord ++ tailWord_2079765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079765).length < 2 ^ (prefixWord ++ tailWord_2079765).sum := by decide
  have hdescent : baseEnd_2079765 < baseStart_2079765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079776 : List Nat := [2, 1, 1, 7, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2079776 : Nat := 118140960795 + 2079776 * 2 ^ 59
def prefixEnd_2079776 : Nat := 4983230072969 + 3 ^ 40 * 2079776 * 2
def baseEnd_2079776 : Nat := 1067924741685360100535291

theorem tailTrace_2079776 : CollatzResearch.WordTrace tailWord_2079776 prefixEnd_2079776 1067924741685360100535291 := by
  unfold tailWord_2079776
  simp only [CollatzResearch.WordTrace]
  refine ⟨37927831256667112153597591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50570441675556149538130121 37927831256667112153597591)
  ·
    refine ⟨56891746885000668230396387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37927831256667112153597591 56891746885000668230396387)
    ·
      refine ⟨85337620327501002345594581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56891746885000668230396387 85337620327501002345594581)
      ·
        refine ⟨2000100476425804742474873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 85337620327501002345594581 2000100476425804742474873)
        ·
          refine ⟨1500075357319353556856155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2000100476425804742474873 1500075357319353556856155)
          ·
            refine ⟨2250113035979030335284233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500075357319353556856155 2250113035979030335284233)
            ·
              refine ⟨1687584776984272751463175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2250113035979030335284233 1687584776984272751463175)
              ·
                refine ⟨2531377165476409127194763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687584776984272751463175 2531377165476409127194763)
                ·
                  refine ⟨3797065748214613690792145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531377165476409127194763 3797065748214613690792145)
                  ·
                    refine ⟨2847799311160960268094109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3797065748214613690792145 2847799311160960268094109)
                    ·
                      refine ⟨1067924741685360100535291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2847799311160960268094109 1067924741685360100535291)
                      ·
                        rfl

theorem cell23_2079776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2079776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079776 prefixEnd_2079776 := by exact prefixLift 2079776
  have htrace : WordTrace (prefixWord ++ tailWord_2079776) baseStart_2079776 baseEnd_2079776 := by
    simpa [prefixWord, tailWord_2079776, baseEnd_2079776] using wordTrace_append hprefix tailTrace_2079776
  have hstable : (prefixWord ++ tailWord_2079776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079776).length < 2 ^ (prefixWord ++ tailWord_2079776).sum := by decide
  have hdescent : baseEnd_2079776 < baseStart_2079776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079781 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_2079781 : Nat := 118140960795 + 2079781 * 2 ^ 59
def prefixEnd_2079781 : Nat := 4983230072969 + 3 ^ 40 * 2079781 * 2
def baseEnd_2079781 : Nat := 1067927309088632580972767

theorem tailTrace_2079781 : CollatzResearch.WordTrace tailWord_2079781 prefixEnd_2079781 1067927309088632580972767 := by
  unfold tailWord_2079781
  simp only [CollatzResearch.WordTrace]
  refine ⟨75855844878316110161127197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50570563252210740107418131 75855844878316110161127197)
  ·
    refine ⟨28445941829368541310422699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75855844878316110161127197 28445941829368541310422699)
    ·
      refine ⟨42668912744052811965634049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28445941829368541310422699 42668912744052811965634049)
      ·
        refine ⟨32001684558039608974225537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42668912744052811965634049 32001684558039608974225537)
        ·
          refine ⟨24001263418529706730669153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32001684558039608974225537 24001263418529706730669153)
          ·
            refine ⟨18000947563897280048001865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24001263418529706730669153 18000947563897280048001865)
            ·
              refine ⟨13500710672922960036001399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18000947563897280048001865 13500710672922960036001399)
              ·
                refine ⟨20251066009384440054002099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13500710672922960036001399 20251066009384440054002099)
                ·
                  refine ⟨30376599014076660081003149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20251066009384440054002099 30376599014076660081003149)
                  ·
                    refine ⟨11391224630278747530376181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30376599014076660081003149 11391224630278747530376181)
                    ·
                      refine ⟨1067927309088632580972767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11391224630278747530376181 1067927309088632580972767)
                      ·
                        rfl

theorem cell23_2079781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_2079781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079781 prefixEnd_2079781 := by exact prefixLift 2079781
  have htrace : WordTrace (prefixWord ++ tailWord_2079781) baseStart_2079781 baseEnd_2079781 := by
    simpa [prefixWord, tailWord_2079781, baseEnd_2079781] using wordTrace_append hprefix tailTrace_2079781
  have hstable : (prefixWord ++ tailWord_2079781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079781).length < 2 ^ (prefixWord ++ tailWord_2079781).sum := by decide
  have hdescent : baseEnd_2079781 < baseStart_2079781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079828 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_2079828 : Nat := 118140960795 + 2079828 * 2 ^ 59
def prefixEnd_2079828 : Nat := 4983230072969 + 3 ^ 40 * 2079828 * 2
def baseEnd_2079828 : Nat := 1067951442679393897085051

theorem tailTrace_2079828 : CollatzResearch.WordTrace tailWord_2079828 prefixEnd_2079828 1067951442679393897085051 := by
  unfold tailWord_2079828
  simp only [CollatzResearch.WordTrace]
  refine ⟨37928779554572918594044069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50571706072763891458725425 37928779554572918594044069)
  ·
    refine ⟨7111646166482422236383263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37928779554572918594044069 7111646166482422236383263)
    ·
      refine ⟨10667469249723633354574895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7111646166482422236383263 10667469249723633354574895)
      ·
        refine ⟨16001203874585450031862343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10667469249723633354574895 16001203874585450031862343)
        ·
          refine ⟨24001805811878175047793515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16001203874585450031862343 24001805811878175047793515)
          ·
            refine ⟨36002708717817262571690273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24001805811878175047793515 36002708717817262571690273)
            ·
              refine ⟨27002031538362946928767705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36002708717817262571690273 27002031538362946928767705)
              ·
                refine ⟨20251523653772210196575779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27002031538362946928767705 20251523653772210196575779)
                ·
                  refine ⟨30377285480658315294863669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20251523653772210196575779 30377285480658315294863669)
                  ·
                    refine ⟨2847870513811717058893469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30377285480658315294863669 2847870513811717058893469)
                    ·
                      refine ⟨1067951442679393897085051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2847870513811717058893469 1067951442679393897085051)
                      ·
                        rfl

theorem cell23_2079828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_2079828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079828 prefixEnd_2079828 := by exact prefixLift 2079828
  have htrace : WordTrace (prefixWord ++ tailWord_2079828) baseStart_2079828 baseEnd_2079828 := by
    simpa [prefixWord, tailWord_2079828, baseEnd_2079828] using wordTrace_append hprefix tailTrace_2079828
  have hstable : (prefixWord ++ tailWord_2079828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079828).length < 2 ^ (prefixWord ++ tailWord_2079828).sum := by decide
  have hdescent : baseEnd_2079828 < baseStart_2079828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079851 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 4]
def baseStart_2079851 : Nat := 118140960795 + 2079851 * 2 ^ 59
def prefixEnd_2079851 : Nat := 4983230072969 + 3 ^ 40 * 2079851 * 2
def baseEnd_2079851 : Nat := 1067963252734447307097445

theorem tailTrace_2079851 : CollatzResearch.WordTrace tailWord_2079851 prefixEnd_2079851 1067963252734447307097445 := by
  unfold tailWord_2079851
  simp only [CollatzResearch.WordTrace]
  refine ⟨75858397988062512116175407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50572265325375008077450271 75858397988062512116175407)
  ·
    refine ⟨113787596982093768174263111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75858397988062512116175407 113787596982093768174263111)
    ·
      refine ⟨170681395473140652261394667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113787596982093768174263111 170681395473140652261394667)
      ·
        refine ⟨256022093209710978392092001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170681395473140652261394667 256022093209710978392092001)
        ·
          refine ⟨192016569907283233794069001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256022093209710978392092001 192016569907283233794069001)
          ·
            refine ⟨144012427430462425345551751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192016569907283233794069001 144012427430462425345551751)
            ·
              refine ⟨216018641145693638018327627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144012427430462425345551751 216018641145693638018327627)
              ·
                refine ⟨324027961718540457027491441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216018641145693638018327627 324027961718540457027491441)
                ·
                  refine ⟨243020971288905342770618581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324027961718540457027491441 243020971288905342770618581)
                  ·
                    refine ⟨5695804014583718971186373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 243020971288905342770618581 5695804014583718971186373)
                    ·
                      refine ⟨1067963252734447307097445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5695804014583718971186373 1067963252734447307097445)
                      ·
                        rfl

theorem cell23_2079851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 4].length) (baseStart_2079851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079851 prefixEnd_2079851 := by exact prefixLift 2079851
  have htrace : WordTrace (prefixWord ++ tailWord_2079851) baseStart_2079851 baseEnd_2079851 := by
    simpa [prefixWord, tailWord_2079851, baseEnd_2079851] using wordTrace_append hprefix tailTrace_2079851
  have hstable : (prefixWord ++ tailWord_2079851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079851).length < 2 ^ (prefixWord ++ tailWord_2079851).sum := by decide
  have hdescent : baseEnd_2079851 < baseStart_2079851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079858 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2079858 : Nat := 118140960795 + 2079858 * 2 ^ 59
def prefixEnd_2079858 : Nat := 4983230072969 + 3 ^ 40 * 2079858 * 2
def baseEnd_2079858 : Nat := 1067966847099028779709913

theorem tailTrace_2079858 : CollatzResearch.WordTrace tailWord_2079858 prefixEnd_2079858 1067966847099028779709913 := by
  unfold tailWord_2079858
  simp only [CollatzResearch.WordTrace]
  refine ⟨18964663324759288077920057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50572435532691434874453485 18964663324759288077920057)
  ·
    refine ⟨14223497493569466058440043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18964663324759288077920057 14223497493569466058440043)
    ·
      refine ⟨21335246240354199087660065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14223497493569466058440043 21335246240354199087660065)
      ·
        refine ⟨16001434680265649315745049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21335246240354199087660065 16001434680265649315745049)
        ·
          refine ⟨12001076010199236986808787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16001434680265649315745049 12001076010199236986808787)
          ·
            refine ⟨18001614015298855480213181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12001076010199236986808787 18001614015298855480213181)
            ·
              refine ⟨6750605255737070805079943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18001614015298855480213181 6750605255737070805079943)
              ·
                refine ⟨10125907883605606207619915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6750605255737070805079943 10125907883605606207619915)
                ·
                  refine ⟨15188861825408409311429873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10125907883605606207619915 15188861825408409311429873)
                  ·
                    refine ⟨11391646369056306983572405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15188861825408409311429873 11391646369056306983572405)
                    ·
                      refine ⟨1067966847099028779709913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11391646369056306983572405 1067966847099028779709913)
                      ·
                        rfl

theorem cell23_2079858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2079858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079858 prefixEnd_2079858 := by exact prefixLift 2079858
  have htrace : WordTrace (prefixWord ++ tailWord_2079858) baseStart_2079858 baseEnd_2079858 := by
    simpa [prefixWord, tailWord_2079858, baseEnd_2079858] using wordTrace_append hprefix tailTrace_2079858
  have hstable : (prefixWord ++ tailWord_2079858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079858).length < 2 ^ (prefixWord ++ tailWord_2079858).sum := by decide
  have hdescent : baseEnd_2079858 < baseStart_2079858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079868 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_2079868 : Nat := 118140960795 + 2079868 * 2 ^ 59
def prefixEnd_2079868 : Nat := 4983230072969 + 3 ^ 40 * 2079868 * 2
def baseEnd_2079868 : Nat := 1067971981905573740584867

theorem tailTrace_2079868 : CollatzResearch.WordTrace tailWord_2079868 prefixEnd_2079868 1067971981905573740584867 := by
  unfold tailWord_2079868
  simp only [CollatzResearch.WordTrace]
  refine ⟨37929509014500462009772129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50572678686000616013029505 37929509014500462009772129)
  ·
    refine ⟨28447131760875346507329097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37929509014500462009772129 28447131760875346507329097)
    ·
      refine ⟨21335348820656509880496823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28447131760875346507329097 21335348820656509880496823)
      ·
        refine ⟨32003023230984764820745235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21335348820656509880496823 32003023230984764820745235)
        ·
          refine ⟨48004534846477147231117853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32003023230984764820745235 48004534846477147231117853)
          ·
            refine ⟨18001700567428930211669195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48004534846477147231117853 18001700567428930211669195)
            ·
              refine ⟨27002550851143395317503793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18001700567428930211669195 27002550851143395317503793)
              ·
                refine ⟨20251913138357546488127845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27002550851143395317503793 20251913138357546488127845)
                ·
                  refine ⟨3797233713442039966523971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20251913138357546488127845 3797233713442039966523971)
                  ·
                    refine ⟨5695850570163059949785957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3797233713442039966523971 5695850570163059949785957)
                    ·
                      refine ⟨1067971981905573740584867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5695850570163059949785957 1067971981905573740584867)
                      ·
                        rfl

theorem cell23_2079868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_2079868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079868 prefixEnd_2079868 := by exact prefixLift 2079868
  have htrace : WordTrace (prefixWord ++ tailWord_2079868) baseStart_2079868 baseEnd_2079868 := by
    simpa [prefixWord, tailWord_2079868, baseEnd_2079868] using wordTrace_append hprefix tailTrace_2079868
  have hstable : (prefixWord ++ tailWord_2079868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079868).length < 2 ^ (prefixWord ++ tailWord_2079868).sum := by decide
  have hdescent : baseEnd_2079868 < baseStart_2079868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079871 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 5]
def baseStart_2079871 : Nat := 118140960795 + 2079871 * 2 ^ 59
def prefixEnd_2079871 : Nat := 4983230072969 + 3 ^ 40 * 2079871 * 2
def baseEnd_2079871 : Nat := 1067973522347537228847353

theorem tailTrace_2079871 : CollatzResearch.WordTrace tailWord_2079871 prefixEnd_2079871 1067973522347537228847353 := by
  unfold tailWord_2079871
  simp only [CollatzResearch.WordTrace]
  refine ⟨75859127447990055531903467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50572751631993370354602311 75859127447990055531903467)
  ·
    refine ⟨113788691171985083297855201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75859127447990055531903467 113788691171985083297855201)
    ·
      refine ⟨85341518378988812473391401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113788691171985083297855201 85341518378988812473391401)
      ·
        refine ⟨64006138784241609355043551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85341518378988812473391401 64006138784241609355043551)
        ·
          refine ⟨96009208176362414032565327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64006138784241609355043551 96009208176362414032565327)
          ·
            refine ⟨144013812264543621048847991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96009208176362414032565327 144013812264543621048847991)
            ·
              refine ⟨216020718396815431573271987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144013812264543621048847991 216020718396815431573271987)
              ·
                refine ⟨324031077595223147359907981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216020718396815431573271987 324031077595223147359907981)
                ·
                  refine ⟨121511654098208680259965493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324031077595223147359907981 121511654098208680259965493)
                  ·
                    refine ⟨11391717571707063774371765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121511654098208680259965493 11391717571707063774371765)
                    ·
                      refine ⟨1067973522347537228847353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11391717571707063774371765 1067973522347537228847353)
                      ·
                        rfl

theorem cell23_2079871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_2079871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079871 prefixEnd_2079871 := by exact prefixLift 2079871
  have htrace : WordTrace (prefixWord ++ tailWord_2079871) baseStart_2079871 baseEnd_2079871 := by
    simpa [prefixWord, tailWord_2079871, baseEnd_2079871] using wordTrace_append hprefix tailTrace_2079871
  have hstable : (prefixWord ++ tailWord_2079871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079871).length < 2 ^ (prefixWord ++ tailWord_2079871).sum := by decide
  have hdescent : baseEnd_2079871 < baseStart_2079871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079891 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 10]
def baseStart_2079891 : Nat := 118140960795 + 2079891 * 2 ^ 59
def prefixEnd_2079891 : Nat := 4983230072969 + 3 ^ 40 * 2079891 * 2
def baseEnd_2079891 : Nat := 118664865773403016733029

theorem tailTrace_2079891 : CollatzResearch.WordTrace tailWord_2079891 prefixEnd_2079891 118664865773403016733029 := by
  unfold tailWord_2079891
  simp only [CollatzResearch.WordTrace]
  refine ⟨75859856907917598947631527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50573237938611732631754351 75859856907917598947631527)
  ·
    refine ⟨113789785361876398421447291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75859856907917598947631527 113789785361876398421447291)
    ·
      refine ⟨170684678042814597632170937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113789785361876398421447291 170684678042814597632170937)
      ·
        refine ⟨128013508532110948224128203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170684678042814597632170937 128013508532110948224128203)
        ·
          refine ⟨192020262798166422336192305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128013508532110948224128203 192020262798166422336192305)
          ·
            refine ⟨144015197098624816752144229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192020262798166422336192305 144015197098624816752144229)
            ·
              refine ⟨27002849455992153141027043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144015197098624816752144229 27002849455992153141027043)
              ·
                refine ⟨40504274183988229711540565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27002849455992153141027043 40504274183988229711540565)
                ·
                  refine ⟨118664865773403016733029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 40504274183988229711540565 118664865773403016733029)
                  ·
                    rfl

theorem cell23_2079891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 10].length) (baseStart_2079891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079891 prefixEnd_2079891 := by exact prefixLift 2079891
  have htrace : WordTrace (prefixWord ++ tailWord_2079891) baseStart_2079891 baseEnd_2079891 := by
    simpa [prefixWord, tailWord_2079891, baseEnd_2079891] using wordTrace_append hprefix tailTrace_2079891
  have hstable : (prefixWord ++ tailWord_2079891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079891).length < 2 ^ (prefixWord ++ tailWord_2079891).sum := by decide
  have hdescent : baseEnd_2079891 < baseStart_2079891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079902 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_2079902 : Nat := 118140960795 + 2079902 * 2 ^ 59
def prefixEnd_2079902 : Nat := 4983230072969 + 3 ^ 40 * 2079902 * 2
def baseEnd_2079902 : Nat := 1067989440247826607559711

theorem tailTrace_2079902 : CollatzResearch.WordTrace tailWord_2079902 prefixEnd_2079902 1067989440247826607559711 := by
  unfold tailWord_2079902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9482532263859718478285245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50573505407251831884187973 9482532263859718478285245)
  ·
    refine ⟨3555949598947394429356967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9482532263859718478285245 3555949598947394429356967)
    ·
      refine ⟨5333924398421091644035451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3555949598947394429356967 5333924398421091644035451)
      ·
        refine ⟨8000886597631637466053177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5333924398421091644035451 8000886597631637466053177)
        ·
          refine ⟨6000664948223728099539883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8000886597631637466053177 6000664948223728099539883)
          ·
            refine ⟨9000997422335592149309825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6000664948223728099539883 9000997422335592149309825)
            ·
              refine ⟨6750748066751694111982369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9000997422335592149309825 6750748066751694111982369)
              ·
                refine ⟨5063061050063770583986777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6750748066751694111982369 5063061050063770583986777)
                ·
                  refine ⟨3797295787547827937990083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5063061050063770583986777 3797295787547827937990083)
                  ·
                    refine ⟨5695943681321741906985125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3797295787547827937990083 5695943681321741906985125)
                    ·
                      refine ⟨1067989440247826607559711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5695943681321741906985125 1067989440247826607559711)
                      ·
                        rfl

theorem cell23_2079902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_2079902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079902 prefixEnd_2079902 := by exact prefixLift 2079902
  have htrace : WordTrace (prefixWord ++ tailWord_2079902) baseStart_2079902 baseEnd_2079902 := by
    simpa [prefixWord, tailWord_2079902, baseEnd_2079902] using wordTrace_append hprefix tailTrace_2079902
  have hstable : (prefixWord ++ tailWord_2079902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079902).length < 2 ^ (prefixWord ++ tailWord_2079902).sum := by decide
  have hdescent : baseEnd_2079902 < baseStart_2079902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079905 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2079905 : Nat := 118140960795 + 2079905 * 2 ^ 59
def prefixEnd_2079905 : Nat := 4983230072969 + 3 ^ 40 * 2079905 * 2
def baseEnd_2079905 : Nat := 1067990980689790095822197

theorem tailTrace_2079905 : CollatzResearch.WordTrace tailWord_2079905 prefixEnd_2079905 1067990980689790095822197 := by
  unfold tailWord_2079905
  simp only [CollatzResearch.WordTrace]
  refine ⟨75860367529866879338641169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50573578353244586225760779 75860367529866879338641169)
  ·
    refine ⟨56895275647400159503980877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75860367529866879338641169 56895275647400159503980877)
    ·
      refine ⟨21335728367775059813992829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56895275647400159503980877 21335728367775059813992829)
      ·
        refine ⟨8000898137915647430247311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21335728367775059813992829 8000898137915647430247311)
        ·
          refine ⟨12001347206873471145370967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8000898137915647430247311 12001347206873471145370967)
          ·
            refine ⟨18002020810310206718056451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12001347206873471145370967 18002020810310206718056451)
            ·
              refine ⟨27003031215465310077084677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18002020810310206718056451 27003031215465310077084677)
              ·
                refine ⟨5063068352899745639453377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27003031215465310077084677 5063068352899745639453377)
                ·
                  refine ⟨3797301264674809229590033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5063068352899745639453377 3797301264674809229590033)
                  ·
                    refine ⟨2847975948506106922192525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3797301264674809229590033 2847975948506106922192525)
                    ·
                      refine ⟨1067990980689790095822197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2847975948506106922192525 1067990980689790095822197)
                      ·
                        rfl

theorem cell23_2079905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2079905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079905 prefixEnd_2079905 := by exact prefixLift 2079905
  have htrace : WordTrace (prefixWord ++ tailWord_2079905) baseStart_2079905 baseEnd_2079905 := by
    simpa [prefixWord, tailWord_2079905, baseEnd_2079905] using wordTrace_append hprefix tailTrace_2079905
  have hstable : (prefixWord ++ tailWord_2079905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079905).length < 2 ^ (prefixWord ++ tailWord_2079905).sum := by decide
  have hdescent : baseEnd_2079905 < baseStart_2079905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079935 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 5, 1, 3]
def baseStart_2079935 : Nat := 118140960795 + 2079935 * 2 ^ 59
def prefixEnd_2079935 : Nat := 4983230072969 + 3 ^ 40 * 2079935 * 2
def baseEnd_2079935 : Nat := 1068006385109424978447059

theorem tailTrace_2079935 : CollatzResearch.WordTrace tailWord_2079935 prefixEnd_2079935 1068006385109424978447059 := by
  unfold tailWord_2079935
  simp only [CollatzResearch.WordTrace]
  refine ⟨75861461719758194462233259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50574307813172129641488839 75861461719758194462233259)
  ·
    refine ⟨113792192579637291693349889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75861461719758194462233259 113792192579637291693349889)
    ·
      refine ⟨85344144434727968770012417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113792192579637291693349889 85344144434727968770012417)
      ·
        refine ⟨64008108326045976577509313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85344144434727968770012417 64008108326045976577509313)
        ·
          refine ⟨48006081244534482433131985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64008108326045976577509313 48006081244534482433131985)
          ·
            refine ⟨36004560933400861824848989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48006081244534482433131985 36004560933400861824848989)
            ·
              refine ⟨13501710350025323184318371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36004560933400861824848989 13501710350025323184318371)
              ·
                refine ⟨20252565525037984776477557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13501710350025323184318371 20252565525037984776477557)
                ·
                  refine ⟨1898678017972311072794771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20252565525037984776477557 1898678017972311072794771)
                  ·
                    refine ⟨2848017026958466609192157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1898678017972311072794771 2848017026958466609192157)
                    ·
                      refine ⟨1068006385109424978447059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2848017026958466609192157 1068006385109424978447059)
                      ·
                        rfl

theorem cell23_2079935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_2079935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079935 prefixEnd_2079935 := by exact prefixLift 2079935
  have htrace : WordTrace (prefixWord ++ tailWord_2079935) baseStart_2079935 baseEnd_2079935 := by
    simpa [prefixWord, tailWord_2079935, baseEnd_2079935] using wordTrace_append hprefix tailTrace_2079935
  have hstable : (prefixWord ++ tailWord_2079935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079935).length < 2 ^ (prefixWord ++ tailWord_2079935).sum := by decide
  have hdescent : baseEnd_2079935 < baseStart_2079935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2079969 : List Nat := [1, 2, 3, 1, 3, 2, 2, 4, 1, 1, 3]
def baseStart_2079969 : Nat := 118140960795 + 2079969 * 2 ^ 59
def prefixEnd_2079969 : Nat := 4983230072969 + 3 ^ 40 * 2079969 * 2
def baseEnd_2079969 : Nat := 1068023843451677845421903

theorem tailTrace_2079969 : CollatzResearch.WordTrace tailWord_2079969 prefixEnd_2079969 1068023843451677845421903 := by
  unfold tailWord_2079969
  simp only [CollatzResearch.WordTrace]
  refine ⟨75862701801635018268970961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50575134534423345512647307 75862701801635018268970961)
  ·
    refine ⟨56897026351226263701728221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75862701801635018268970961 56897026351226263701728221)
    ·
      refine ⟨21336384881709848888148083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56897026351226263701728221 21336384881709848888148083)
      ·
        refine ⟨32004577322564773332222125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21336384881709848888148083 32004577322564773332222125)
        ·
          refine ⟨12001716495961789999583297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32004577322564773332222125 12001716495961789999583297)
          ·
            refine ⟨9001287371971342499687473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12001716495961789999583297 9001287371971342499687473)
            ·
              refine ⟨6750965528978506874765605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9001287371971342499687473 6750965528978506874765605)
              ·
                refine ⟨1265806036683470039018551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6750965528978506874765605 1265806036683470039018551)
                ·
                  refine ⟨1898709055025205058527827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1265806036683470039018551 1898709055025205058527827)
                  ·
                    refine ⟨2848063582537807587791741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1898709055025205058527827 2848063582537807587791741)
                    ·
                      refine ⟨1068023843451677845421903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2848063582537807587791741 1068023843451677845421903)
                      ·
                        rfl

theorem cell23_2079969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_2079969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2079969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2079969 prefixEnd_2079969 := by exact prefixLift 2079969
  have htrace : WordTrace (prefixWord ++ tailWord_2079969) baseStart_2079969 baseEnd_2079969 := by
    simpa [prefixWord, tailWord_2079969, baseEnd_2079969] using wordTrace_append hprefix tailTrace_2079969
  have hstable : (prefixWord ++ tailWord_2079969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2079969).length < 2 ^ (prefixWord ++ tailWord_2079969).sum := by decide
  have hdescent : baseEnd_2079969 < baseStart_2079969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2079969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080012 : List Nat := [2, 2, 1, 2, 2, 3, 2, 3, 1, 2, 3]
def baseStart_2080012 : Nat := 118140960795 + 2080012 * 2 ^ 59
def prefixEnd_2080012 : Nat := 4983230072969 + 3 ^ 40 * 2080012 * 2
def baseEnd_2080012 : Nat := 1068045923119821177184205

theorem tailTrace_2080012 : CollatzResearch.WordTrace tailWord_2080012 prefixEnd_2080012 1068045923119821177184205 := by
  unfold tailWord_2080012
  simp only [CollatzResearch.WordTrace]
  refine ⟨37932135070239618306393145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50576180093652824408524193 37932135070239618306393145)
  ·
    refine ⟨28449101302679713729794859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37932135070239618306393145 28449101302679713729794859)
    ·
      refine ⟨42673651954019570594692289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28449101302679713729794859 42673651954019570594692289)
      ·
        refine ⟨32005238965514677946019217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42673651954019570594692289 32005238965514677946019217)
        ·
          refine ⟨24003929224136008459514413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32005238965514677946019217 24003929224136008459514413)
          ·
            refine ⟨9001473459051003172317905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24003929224136008459514413 9001473459051003172317905)
            ·
              refine ⟨6751105094288252379238429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9001473459051003172317905 6751105094288252379238429)
              ·
                refine ⟨2531664410358094642214411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6751105094288252379238429 2531664410358094642214411)
                ·
                  refine ⟨3797496615537141963321617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531664410358094642214411 3797496615537141963321617)
                  ·
                    refine ⟨2848122461652856472491213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3797496615537141963321617 2848122461652856472491213)
                    ·
                      refine ⟨1068045923119821177184205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2848122461652856472491213 1068045923119821177184205)
                      ·
                        rfl

theorem cell23_2080012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_2080012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080012 prefixEnd_2080012 := by exact prefixLift 2080012
  have htrace : WordTrace (prefixWord ++ tailWord_2080012) baseStart_2080012 baseEnd_2080012 := by
    simpa [prefixWord, tailWord_2080012, baseEnd_2080012] using wordTrace_append hprefix tailTrace_2080012
  have hstable : (prefixWord ++ tailWord_2080012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080012).length < 2 ^ (prefixWord ++ tailWord_2080012).sum := by decide
  have hdescent : baseEnd_2080012 < baseStart_2080012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080026 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2]
def baseStart_2080026 : Nat := 118140960795 + 2080026 * 2 ^ 59
def prefixEnd_2080026 : Nat := 4983230072969 + 3 ^ 40 * 2080026 * 2
def baseEnd_2080026 : Nat := 1068053111848984122409141

theorem tailTrace_2080026 : CollatzResearch.WordTrace tailWord_2080026 prefixEnd_2080026 1068053111848984122409141 := by
  unfold tailWord_2080026
  simp only [CollatzResearch.WordTrace]
  refine ⟨18966195190607129250948983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50576520508285678002530621 18966195190607129250948983)
  ·
    refine ⟨28449292785910693876423475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18966195190607129250948983 28449292785910693876423475)
    ·
      refine ⟨42673939178866040814635213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28449292785910693876423475 42673939178866040814635213)
      ·
        refine ⟨16002727192074765305488205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42673939178866040814635213 16002727192074765305488205)
        ·
          refine ⟨6001022697028036989558077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16002727192074765305488205 6001022697028036989558077)
          ·
            refine ⟨2250383511385513871084279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6001022697028036989558077 2250383511385513871084279)
            ·
              refine ⟨3375575267078270806626419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250383511385513871084279 3375575267078270806626419)
              ·
                refine ⟨5063362900617406209939629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3375575267078270806626419 5063362900617406209939629)
                ·
                  refine ⟨1898761087731527328727361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5063362900617406209939629 1898761087731527328727361)
                  ·
                    refine ⟨1424070815798645496545521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1898761087731527328727361 1424070815798645496545521)
                    ·
                      refine ⟨1068053111848984122409141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424070815798645496545521 1068053111848984122409141)
                      ·
                        rfl

theorem cell23_2080026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_2080026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080026 prefixEnd_2080026 := by exact prefixLift 2080026
  have htrace : WordTrace (prefixWord ++ tailWord_2080026) baseStart_2080026 baseEnd_2080026 := by
    simpa [prefixWord, tailWord_2080026, baseEnd_2080026] using wordTrace_append hprefix tailTrace_2080026
  have hstable : (prefixWord ++ tailWord_2080026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080026).length < 2 ^ (prefixWord ++ tailWord_2080026).sum := by decide
  have hdescent : baseEnd_2080026 < baseStart_2080026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080082 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_2080082 : Nat := 118140960795 + 2080082 * 2 ^ 59
def prefixEnd_2080082 : Nat := 4983230072969 + 3 ^ 40 * 2080082 * 2
def baseEnd_2080082 : Nat := 1068081866765635903308883

theorem tailTrace_2080082 : CollatzResearch.WordTrace tailWord_2080082 prefixEnd_2080082 1068081866765635903308883 := by
  unfold tailWord_2080082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18966705812556409641958625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50577882166817092378556333 18966705812556409641958625)
  ·
    refine ⟨14225029359417307231468969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18966705812556409641958625 14225029359417307231468969)
    ·
      refine ⟨10668772019562980423601727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14225029359417307231468969 10668772019562980423601727)
      ·
        refine ⟨16003158029344470635402591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10668772019562980423601727 16003158029344470635402591)
        ·
          refine ⟨24004737044016705953103887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16003158029344470635402591 24004737044016705953103887)
          ·
            refine ⟨36007105566025058929655831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24004737044016705953103887 36007105566025058929655831)
            ·
              refine ⟨54010658349037588394483747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36007105566025058929655831 54010658349037588394483747)
              ·
                refine ⟨81015987523556382591725621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54010658349037588394483747 81015987523556382591725621)
                ·
                  refine ⟨7595248830333410867974277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81015987523556382591725621 7595248830333410867974277)
                  ·
                    refine ⟨1424109155687514537745177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7595248830333410867974277 1424109155687514537745177)
                    ·
                      refine ⟨1068081866765635903308883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424109155687514537745177 1068081866765635903308883)
                      ·
                        rfl

theorem cell23_2080082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_2080082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080082 prefixEnd_2080082 := by exact prefixLift 2080082
  have htrace : WordTrace (prefixWord ++ tailWord_2080082) baseStart_2080082 baseEnd_2080082 := by
    simpa [prefixWord, tailWord_2080082, baseEnd_2080082] using wordTrace_append hprefix tailTrace_2080082
  have hstable : (prefixWord ++ tailWord_2080082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080082).length < 2 ^ (prefixWord ++ tailWord_2080082).sum := by decide
  have hdescent : baseEnd_2080082 < baseStart_2080082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080093 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2080093 : Nat := 118140960795 + 2080093 * 2 ^ 59
def prefixEnd_2080093 : Nat := 4983230072969 + 3 ^ 40 * 2080093 * 2
def baseEnd_2080093 : Nat := 1068087515052835360271333

theorem tailTrace_2080093 : CollatzResearch.WordTrace tailWord_2080093 prefixEnd_2080093 1068087515052835360271333 := by
  unfold tailWord_2080093
  simp only [CollatzResearch.WordTrace]
  refine ⟨75867224453185787446484933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50578149635457191630989955 75867224453185787446484933)
  ·
    refine ⟨14225104584972335146215925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75867224453185787446484933 14225104584972335146215925)
    ·
      refine ⟨1333603554841156419957743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14225104584972335146215925 1333603554841156419957743)
      ·
        refine ⟨2000405332261734629936615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333603554841156419957743 2000405332261734629936615)
        ·
          refine ⟨3000607998392601944904923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000405332261734629936615 3000607998392601944904923)
          ·
            refine ⟨4500911997588902917357385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000607998392601944904923 4500911997588902917357385)
            ·
              refine ⟨3375683998191677188018039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4500911997588902917357385 3375683998191677188018039)
              ·
                refine ⟨5063525997287515782027059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3375683998191677188018039 5063525997287515782027059)
                ·
                  refine ⟨7595288995931273673040589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063525997287515782027059 7595288995931273673040589)
                  ·
                    refine ⟨2848233373474227627390221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7595288995931273673040589 2848233373474227627390221)
                    ·
                      refine ⟨1068087515052835360271333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2848233373474227627390221 1068087515052835360271333)
                      ·
                        rfl

theorem cell23_2080093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2080093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080093 prefixEnd_2080093 := by exact prefixLift 2080093
  have htrace : WordTrace (prefixWord ++ tailWord_2080093) baseStart_2080093 baseEnd_2080093 := by
    simpa [prefixWord, tailWord_2080093, baseEnd_2080093] using wordTrace_append hprefix tailTrace_2080093
  have hstable : (prefixWord ++ tailWord_2080093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080093).length < 2 ^ (prefixWord ++ tailWord_2080093).sum := by decide
  have hdescent : baseEnd_2080093 < baseStart_2080093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080099 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 1, 4, 2]
def baseStart_2080099 : Nat := 118140960795 + 2080099 * 2 ^ 59
def prefixEnd_2080099 : Nat := 4983230072969 + 3 ^ 40 * 2080099 * 2
def baseEnd_2080099 : Nat := 1068090595936762336796305

theorem tailTrace_2080099 : CollatzResearch.WordTrace tailWord_2080099 prefixEnd_2080099 1068090595936762336796305 := by
  unfold tailWord_2080099
  simp only [CollatzResearch.WordTrace]
  refine ⟨75867443291164050471203351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50578295527442700314135567 75867443291164050471203351)
  ·
    refine ⟨113801164936746075706805027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75867443291164050471203351 113801164936746075706805027)
    ·
      refine ⟨170701747405119113560207541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113801164936746075706805027 170701747405119113560207541)
      ·
        refine ⟨16003288819229916896269457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170701747405119113560207541 16003288819229916896269457)
        ·
          refine ⟨12002466614422437672202093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16003288819229916896269457 12002466614422437672202093)
          ·
            refine ⟨4500924980408414127075785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12002466614422437672202093 4500924980408414127075785)
            ·
              refine ⟨3375693735306310595306839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4500924980408414127075785 3375693735306310595306839)
              ·
                refine ⟨5063540602959465892960259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3375693735306310595306839 5063540602959465892960259)
                ·
                  refine ⟨7595310904439198839440389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063540602959465892960259 7595310904439198839440389)
                  ·
                    refine ⟨1424120794582349782395073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7595310904439198839440389 1424120794582349782395073)
                    ·
                      refine ⟨1068090595936762336796305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424120794582349782395073 1068090595936762336796305)
                      ·
                        rfl

theorem cell23_2080099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_2080099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080099 prefixEnd_2080099 := by exact prefixLift 2080099
  have htrace : WordTrace (prefixWord ++ tailWord_2080099) baseStart_2080099 baseEnd_2080099 := by
    simpa [prefixWord, tailWord_2080099, baseEnd_2080099] using wordTrace_append hprefix tailTrace_2080099
  have hstable : (prefixWord ++ tailWord_2080099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080099).length < 2 ^ (prefixWord ++ tailWord_2080099).sum := by decide
  have hdescent : baseEnd_2080099 < baseStart_2080099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080115 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 3]
def baseStart_2080115 : Nat := 118140960795 + 2080115 * 2 ^ 59
def prefixEnd_2080115 : Nat := 4983230072969 + 3 ^ 40 * 2080115 * 2
def baseEnd_2080115 : Nat := 1068098811627234274196231

theorem tailTrace_2080115 : CollatzResearch.WordTrace tailWord_2080115 prefixEnd_2080115 1068098811627234274196231 := by
  unfold tailWord_2080115
  simp only [CollatzResearch.WordTrace]
  refine ⟨75868026859106085203785799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50578684572737390135857199 75868026859106085203785799)
  ·
    refine ⟨113802040288659127805678699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75868026859106085203785799 113802040288659127805678699)
    ·
      refine ⟨170703060432988691708518049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113802040288659127805678699 170703060432988691708518049)
      ·
        refine ⟨128027295324741518781388537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170703060432988691708518049 128027295324741518781388537)
        ·
          refine ⟨96020471493556139086041403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128027295324741518781388537 96020471493556139086041403)
          ·
            refine ⟨144030707240334208629062105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96020471493556139086041403 144030707240334208629062105)
            ·
              refine ⟨108023030430250656471796579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144030707240334208629062105 108023030430250656471796579)
              ·
                refine ⟨162034545645375984707694869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108023030430250656471796579 162034545645375984707694869)
                ·
                  refine ⟨7595369327126999283173197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162034545645375984707694869 7595369327126999283173197)
                  ·
                    refine ⟨2848263497672624731189949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7595369327126999283173197 2848263497672624731189949)
                    ·
                      refine ⟨1068098811627234274196231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2848263497672624731189949 1068098811627234274196231)
                      ·
                        rfl

theorem cell23_2080115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 3].length) (baseStart_2080115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080115 prefixEnd_2080115 := by exact prefixLift 2080115
  have htrace : WordTrace (prefixWord ++ tailWord_2080115) baseStart_2080115 baseEnd_2080115 := by
    simpa [prefixWord, tailWord_2080115, baseEnd_2080115] using wordTrace_append hprefix tailTrace_2080115
  have hstable : (prefixWord ++ tailWord_2080115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080115).length < 2 ^ (prefixWord ++ tailWord_2080115).sum := by decide
  have hdescent : baseEnd_2080115 < baseStart_2080115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080132 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_2080132 : Nat := 118140960795 + 2080132 * 2 ^ 59
def prefixEnd_2080132 : Nat := 4983230072969 + 3 ^ 40 * 2080132 * 2
def baseEnd_2080132 : Nat := 1068107540798360707683653

theorem tailTrace_2080132 : CollatzResearch.WordTrace tailWord_2080132 prefixEnd_2080132 1068107540798360707683653 := by
  unfold tailWord_2080132
  simp only [CollatzResearch.WordTrace]
  refine ⟨37934323450022248553577325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50579097933362998071436433 37934323450022248553577325)
  ·
    refine ⟨14225371293758343207591497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37934323450022248553577325 14225371293758343207591497)
    ·
      refine ⟨10669028470318757405693623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14225371293758343207591497 10669028470318757405693623)
      ·
        refine ⟨16003542705478136108540435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10669028470318757405693623 16003542705478136108540435)
        ·
          refine ⟨24005314058217204162810653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16003542705478136108540435 24005314058217204162810653)
          ·
            refine ⟨9001992771831451561053995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24005314058217204162810653 9001992771831451561053995)
            ·
              refine ⟨13502989157747177341580993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9001992771831451561053995 13502989157747177341580993)
              ·
                refine ⟨10127241868310383006185745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13502989157747177341580993 10127241868310383006185745)
                ·
                  refine ⟨7595431401232787254639309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10127241868310383006185745 7595431401232787254639309)
                  ·
                    refine ⟨2848286775462295220489741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7595431401232787254639309 2848286775462295220489741)
                    ·
                      refine ⟨1068107540798360707683653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2848286775462295220489741 1068107540798360707683653)
                      ·
                        rfl

theorem cell23_2080132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_2080132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080132 prefixEnd_2080132 := by exact prefixLift 2080132
  have htrace : WordTrace (prefixWord ++ tailWord_2080132) baseStart_2080132 baseEnd_2080132 := by
    simpa [prefixWord, tailWord_2080132, baseEnd_2080132] using wordTrace_append hprefix tailTrace_2080132
  have hstable : (prefixWord ++ tailWord_2080132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080132).length < 2 ^ (prefixWord ++ tailWord_2080132).sum := by decide
  have hdescent : baseEnd_2080132 < baseStart_2080132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080172 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 1, 6, 2]
def baseStart_2080172 : Nat := 118140960795 + 2080172 * 2 ^ 59
def prefixEnd_2080172 : Nat := 4983230072969 + 3 ^ 40 * 2080172 * 2
def baseEnd_2080172 : Nat := 1068128080024540551183469

theorem tailTrace_2080172 : CollatzResearch.WordTrace tailWord_2080172 prefixEnd_2080172 1068128080024540551183469 := by
  unfold tailWord_2080172
  simp only [CollatzResearch.WordTrace]
  refine ⟨37935052909949791969305385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50580070546599722625740513 37935052909949791969305385)
  ·
    refine ⟨28451289682462343976979039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37935052909949791969305385 28451289682462343976979039)
    ·
      refine ⟨42676934523693515965468559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28451289682462343976979039 42676934523693515965468559)
      ·
        refine ⟨64015401785540273948202839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42676934523693515965468559 64015401785540273948202839)
        ·
          refine ⟨96023102678310410922304259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64015401785540273948202839 96023102678310410922304259)
          ·
            refine ⟨144034654017465616383456389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96023102678310410922304259 144034654017465616383456389)
            ·
              refine ⟨27006497628274803071898073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144034654017465616383456389 27006497628274803071898073)
              ·
                refine ⟨20254873221206102303923555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27006497628274803071898073 20254873221206102303923555)
                ·
                  refine ⟨30382309831809153455885333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20254873221206102303923555 30382309831809153455885333)
                  ·
                    refine ⟨1424170773366054068244625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30382309831809153455885333 1424170773366054068244625)
                    ·
                      refine ⟨1068128080024540551183469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424170773366054068244625 1068128080024540551183469)
                      ·
                        rfl

theorem cell23_2080172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 6, 2].length) (baseStart_2080172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080172 prefixEnd_2080172 := by exact prefixLift 2080172
  have htrace : WordTrace (prefixWord ++ tailWord_2080172) baseStart_2080172 baseEnd_2080172 := by
    simpa [prefixWord, tailWord_2080172, baseEnd_2080172] using wordTrace_append hprefix tailTrace_2080172
  have hstable : (prefixWord ++ tailWord_2080172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080172).length < 2 ^ (prefixWord ++ tailWord_2080172).sum := by decide
  have hdescent : baseEnd_2080172 < baseStart_2080172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080192 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 3]
def baseStart_2080192 : Nat := 118140960795 + 2080192 * 2 ^ 59
def prefixEnd_2080192 : Nat := 4983230072969 + 3 ^ 40 * 2080192 * 2
def baseEnd_2080192 : Nat := 1068138349637630472933377

theorem tailTrace_2080192 : CollatzResearch.WordTrace tailWord_2080192 prefixEnd_2080192 1068138349637630472933377 := by
  unfold tailWord_2080192
  simp only [CollatzResearch.WordTrace]
  refine ⟨37935417639913563677169415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50580556853218084902892553 37935417639913563677169415)
  ·
    refine ⟨56903126459870345515754123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37935417639913563677169415 56903126459870345515754123)
    ·
      refine ⟨85354689689805518273631185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56903126459870345515754123 85354689689805518273631185)
      ·
        refine ⟨64016017267354138705223389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85354689689805518273631185 64016017267354138705223389)
        ·
          refine ⟨24006006475257802014458771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64016017267354138705223389 24006006475257802014458771)
          ·
            refine ⟨36009009712886703021688157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24006006475257802014458771 36009009712886703021688157)
            ·
              refine ⟨13503378642332513633133059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36009009712886703021688157 13503378642332513633133059)
              ·
                refine ⟨20255067963498770449699589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13503378642332513633133059 20255067963498770449699589)
                ·
                  refine ⟨3797825243156019459318673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20255067963498770449699589 3797825243156019459318673)
                  ·
                    refine ⟨2848368932367014594489005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3797825243156019459318673 2848368932367014594489005)
                    ·
                      refine ⟨1068138349637630472933377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2848368932367014594489005 1068138349637630472933377)
                      ·
                        rfl

theorem cell23_2080192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_2080192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080192 prefixEnd_2080192 := by exact prefixLift 2080192
  have htrace : WordTrace (prefixWord ++ tailWord_2080192) baseStart_2080192 baseEnd_2080192 := by
    simpa [prefixWord, tailWord_2080192, baseEnd_2080192] using wordTrace_append hprefix tailTrace_2080192
  have hstable : (prefixWord ++ tailWord_2080192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080192).length < 2 ^ (prefixWord ++ tailWord_2080192).sum := by decide
  have hdescent : baseEnd_2080192 < baseStart_2080192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080195 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 8]
def baseStart_2080195 : Nat := 118140960795 + 2080195 * 2 ^ 59
def prefixEnd_2080195 : Nat := 4983230072969 + 3 ^ 40 * 2080195 * 2
def baseEnd_2080195 : Nat := 118682210008843773466207

theorem tailTrace_2080195 : CollatzResearch.WordTrace tailWord_2080195 prefixEnd_2080195 118682210008843773466207 := by
  unfold tailWord_2080195
  simp only [CollatzResearch.WordTrace]
  refine ⟨75870944698816258866698039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50580629799210839244465359 75870944698816258866698039)
  ·
    refine ⟨113806417048224388300047059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75870944698816258866698039 113806417048224388300047059)
    ·
      refine ⟨170709625572336582450070589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113806417048224388300047059 170709625572336582450070589)
      ·
        refine ⟨64016109589626218418776471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170709625572336582450070589 64016109589626218418776471)
        ·
          refine ⟨96024164384439327628164707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64016109589626218418776471 96024164384439327628164707)
          ·
            refine ⟨144036246576658991442247061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96024164384439327628164707 144036246576658991442247061)
            ·
              refine ⟨6751699058280890223855331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144036246576658991442247061 6751699058280890223855331)
              ·
                refine ⟨10127548587421335335782997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6751699058280890223855331 10127548587421335335782997)
                ·
                  refine ⟨118682210008843773466207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10127548587421335335782997 118682210008843773466207)
                  ·
                    rfl

theorem cell23_2080195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 8].length) (baseStart_2080195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080195 prefixEnd_2080195 := by exact prefixLift 2080195
  have htrace : WordTrace (prefixWord ++ tailWord_2080195) baseStart_2080195 baseEnd_2080195 := by
    simpa [prefixWord, tailWord_2080195, baseEnd_2080195] using wordTrace_append hprefix tailTrace_2080195
  have hstable : (prefixWord ++ tailWord_2080195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080195).length < 2 ^ (prefixWord ++ tailWord_2080195).sum := by decide
  have hdescent : baseEnd_2080195 < baseStart_2080195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080215 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_2080215 : Nat := 118140960795 + 2080215 * 2 ^ 59
def prefixEnd_2080215 : Nat := 4983230072969 + 3 ^ 40 * 2080215 * 2
def baseEnd_2080215 : Nat := 1068150159692683882945771

theorem tailTrace_2080215 : CollatzResearch.WordTrace tailWord_2080215 prefixEnd_2080215 1068150159692683882945771 := by
  unfold tailWord_2080215
  simp only [CollatzResearch.WordTrace]
  refine ⟨75871674158743802282426099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50581116105829201521617399 75871674158743802282426099)
  ·
    refine ⟨113807511238115703423639149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75871674158743802282426099 113807511238115703423639149)
    ·
      refine ⟨42677816714293388783864681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113807511238115703423639149 42677816714293388783864681)
      ·
        refine ⟨32008362535720041587898511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42677816714293388783864681 32008362535720041587898511)
        ·
          refine ⟨48012543803580062381847767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32008362535720041587898511 48012543803580062381847767)
          ·
            refine ⟨72018815705370093572771651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48012543803580062381847767 72018815705370093572771651)
            ·
              refine ⟨108028223558055140359157477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72018815705370093572771651 108028223558055140359157477)
              ·
                refine ⟨20255291917135338817342027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108028223558055140359157477 20255291917135338817342027)
                ·
                  refine ⟨30382937875703008226013041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20255291917135338817342027 30382937875703008226013041)
                  ·
                    refine ⟨22787203406777256169509781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30382937875703008226013041 22787203406777256169509781)
                    ·
                      refine ⟨1068150159692683882945771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22787203406777256169509781 1068150159692683882945771)
                      ·
                        rfl

theorem cell23_2080215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_2080215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080215 prefixEnd_2080215 := by exact prefixLift 2080215
  have htrace : WordTrace (prefixWord ++ tailWord_2080215) baseStart_2080215 baseEnd_2080215 := by
    simpa [prefixWord, tailWord_2080215, baseEnd_2080215] using wordTrace_append hprefix tailTrace_2080215
  have hstable : (prefixWord ++ tailWord_2080215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080215).length < 2 ^ (prefixWord ++ tailWord_2080215).sum := by decide
  have hdescent : baseEnd_2080215 < baseStart_2080215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080235 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 5]
def baseStart_2080235 : Nat := 118140960795 + 2080235 * 2 ^ 59
def prefixEnd_2080235 : Nat := 4983230072969 + 3 ^ 40 * 2080235 * 2
def baseEnd_2080235 : Nat := 1068160429305773804695679

theorem tailTrace_2080235 : CollatzResearch.WordTrace tailWord_2080235 prefixEnd_2080235 1068160429305773804695679 := by
  unfold tailWord_2080235
  simp only [CollatzResearch.WordTrace]
  refine ⟨75872403618671345698154159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50581602412447563798769439 75872403618671345698154159)
  ·
    refine ⟨113808605428007018547231239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75872403618671345698154159 113808605428007018547231239)
    ·
      refine ⟨170712908142010527820846859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113808605428007018547231239 170712908142010527820846859)
      ·
        refine ⟨256069362213015791731270289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170712908142010527820846859 256069362213015791731270289)
        ·
          refine ⟨192052021659761843798452717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256069362213015791731270289 192052021659761843798452717)
          ·
            refine ⟨72019508122410691424419769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192052021659761843798452717 72019508122410691424419769)
            ·
              refine ⟨54014631091808018568314827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72019508122410691424419769 54014631091808018568314827)
              ·
                refine ⟨81021946637712027852472241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54014631091808018568314827 81021946637712027852472241)
                ·
                  refine ⟨60766459978284020889354181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81021946637712027852472241 60766459978284020889354181)
                  ·
                    refine ⟨11393711245928253916753909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60766459978284020889354181 11393711245928253916753909)
                    ·
                      refine ⟨1068160429305773804695679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11393711245928253916753909 1068160429305773804695679)
                      ·
                        rfl

theorem cell23_2080235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 5].length) (baseStart_2080235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080235 prefixEnd_2080235 := by exact prefixLift 2080235
  have htrace : WordTrace (prefixWord ++ tailWord_2080235) baseStart_2080235 baseEnd_2080235 := by
    simpa [prefixWord, tailWord_2080235, baseEnd_2080235] using wordTrace_append hprefix tailTrace_2080235
  have hstable : (prefixWord ++ tailWord_2080235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080235).length < 2 ^ (prefixWord ++ tailWord_2080235).sum := by decide
  have hdescent : baseEnd_2080235 < baseStart_2080235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080313 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 3, 2, 2]
def baseStart_2080313 : Nat := 118140960795 + 2080313 * 2 ^ 59
def prefixEnd_2080313 : Nat := 4983230072969 + 3 ^ 40 * 2080313 * 2
def baseEnd_2080313 : Nat := 1068200480796824499520321

theorem tailTrace_2080313 : CollatzResearch.WordTrace tailWord_2080313 prefixEnd_2080313 1068200480796824499520321 := by
  unfold tailWord_2080313
  simp only [CollatzResearch.WordTrace]
  refine ⟨75875248512388765019493593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50583499008259176679662395 75875248512388765019493593)
  ·
    refine ⟨56906436384291573764620195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75875248512388765019493593 56906436384291573764620195)
    ·
      refine ⟨85359654576437360646930293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56906436384291573764620195 85359654576437360646930293)
      ·
        refine ⟨8002467616541002560649715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85359654576437360646930293 8002467616541002560649715)
        ·
          refine ⟨12003701424811503840974573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8002467616541002560649715 12003701424811503840974573)
          ·
            refine ⟨4501388034304313940365465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12003701424811503840974573 4501388034304313940365465)
            ·
              refine ⟨3376041025728235455274099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4501388034304313940365465 3376041025728235455274099)
              ·
                refine ⟨5064061538592353182911149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376041025728235455274099 5064061538592353182911149)
                ·
                  refine ⟨1899023076972132443591681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5064061538592353182911149 1899023076972132443591681)
                  ·
                    refine ⟨1424267307729099332693761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1899023076972132443591681 1424267307729099332693761)
                    ·
                      refine ⟨1068200480796824499520321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424267307729099332693761 1068200480796824499520321)
                      ·
                        rfl

theorem cell23_2080313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_2080313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080313 prefixEnd_2080313 := by exact prefixLift 2080313
  have htrace : WordTrace (prefixWord ++ tailWord_2080313) baseStart_2080313 baseEnd_2080313 := by
    simpa [prefixWord, tailWord_2080313, baseEnd_2080313] using wordTrace_append hprefix tailTrace_2080313
  have hstable : (prefixWord ++ tailWord_2080313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080313).length < 2 ^ (prefixWord ++ tailWord_2080313).sum := by decide
  have hdescent : baseEnd_2080313 < baseStart_2080313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080352 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 4]
def baseStart_2080352 : Nat := 118140960795 + 2080352 * 2 ^ 59
def prefixEnd_2080352 : Nat := 4983230072969 + 3 ^ 40 * 2080352 * 2
def baseEnd_2080352 : Nat := 1068220506542349846932641

theorem tailTrace_2080352 : CollatzResearch.WordTrace tailWord_2080352 prefixEnd_2080352 1068220506542349846932641 := by
  unfold tailWord_2080352
  simp only [CollatzResearch.WordTrace]
  refine ⟨37938335479623737340081655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50584447306164983120108873 37938335479623737340081655)
  ·
    refine ⟨56907503219435606010122483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37938335479623737340081655 56907503219435606010122483)
    ·
      refine ⟨85361254829153409015183725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56907503219435606010122483 85361254829153409015183725)
      ·
        refine ⟨32010470560932528380693897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85361254829153409015183725 32010470560932528380693897)
        ·
          refine ⟨24007852920699396285520423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32010470560932528380693897 24007852920699396285520423)
          ·
            refine ⟨36011779381049094428280635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24007852920699396285520423 36011779381049094428280635)
            ·
              refine ⟨54017669071573641642420953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36011779381049094428280635 54017669071573641642420953)
              ·
                refine ⟨40513251803680231231815715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54017669071573641642420953 40513251803680231231815715)
                ·
                  refine ⟨60769877705520346847723573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40513251803680231231815715 60769877705520346847723573)
                  ·
                    refine ⟨5697176034892532516974085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60769877705520346847723573 5697176034892532516974085)
                    ·
                      refine ⟨1068220506542349846932641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5697176034892532516974085 1068220506542349846932641)
                      ·
                        rfl

theorem cell23_2080352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_2080352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080352 prefixEnd_2080352 := by exact prefixLift 2080352
  have htrace : WordTrace (prefixWord ++ tailWord_2080352) baseStart_2080352 baseEnd_2080352 := by
    simpa [prefixWord, tailWord_2080352, baseEnd_2080352] using wordTrace_append hprefix tailTrace_2080352
  have hstable : (prefixWord ++ tailWord_2080352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080352).length < 2 ^ (prefixWord ++ tailWord_2080352).sum := by decide
  have hdescent : baseEnd_2080352 < baseStart_2080352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080419 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 3]
def baseStart_2080419 : Nat := 118140960795 + 2080419 * 2 ^ 59
def prefixEnd_2080419 : Nat := 4983230072969 + 3 ^ 40 * 2080419 * 2
def baseEnd_2080419 : Nat := 1068254909746201084794833

theorem tailTrace_2080419 : CollatzResearch.WordTrace tailWord_2080419 prefixEnd_2080419 1068254909746201084794833 := by
  unfold tailWord_2080419
  simp only [CollatzResearch.WordTrace]
  refine ⟨75879114650004745122852311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50586076433336496748568207 75879114650004745122852311)
  ·
    refine ⟨113818671975007117684278467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75879114650004745122852311 113818671975007117684278467)
    ·
      refine ⟨170728007962510676526417701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113818671975007117684278467 170728007962510676526417701)
      ·
        refine ⟨32011501492970751848703319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170728007962510676526417701 32011501492970751848703319)
        ·
          refine ⟨48017252239456127773054979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32011501492970751848703319 48017252239456127773054979)
          ·
            refine ⟨72025878359184191659582469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48017252239456127773054979 72025878359184191659582469)
            ·
              refine ⟨13504852192347035936171713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72025878359184191659582469 13504852192347035936171713)
              ·
                refine ⟨10128639144260276952128785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13504852192347035936171713 10128639144260276952128785)
                ·
                  refine ⟨7596479358195207714096589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10128639144260276952128785 7596479358195207714096589)
                  ·
                    refine ⟨2848679759323202892786221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7596479358195207714096589 2848679759323202892786221)
                    ·
                      refine ⟨1068254909746201084794833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2848679759323202892786221 1068254909746201084794833)
                      ·
                        rfl

theorem cell23_2080419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_2080419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080419 prefixEnd_2080419 := by exact prefixLift 2080419
  have htrace : WordTrace (prefixWord ++ tailWord_2080419) baseStart_2080419 baseEnd_2080419 := by
    simpa [prefixWord, tailWord_2080419, baseEnd_2080419] using wordTrace_append hprefix tailTrace_2080419
  have hstable : (prefixWord ++ tailWord_2080419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080419).length < 2 ^ (prefixWord ++ tailWord_2080419).sum := by decide
  have hdescent : baseEnd_2080419 < baseStart_2080419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080420 : List Nat := [2, 3, 1, 2, 2, 3, 2, 2, 2, 2, 2]
def baseStart_2080420 : Nat := 118140960795 + 2080420 * 2 ^ 59
def prefixEnd_2080420 : Nat := 4983230072969 + 3 ^ 40 * 2080420 * 2
def baseEnd_2080420 : Nat := 1068255423226855580882329

theorem tailTrace_2080420 : CollatzResearch.WordTrace tailWord_2080420 prefixEnd_2080420 1068255423226855580882329 := by
  unfold tailWord_2080420
  simp only [CollatzResearch.WordTrace]
  refine ⟨37939575561500561146819357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50586100748667414862425809 37939575561500561146819357)
  ·
    refine ⟨14227340835562710430057259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37939575561500561146819357 14227340835562710430057259)
    ·
      refine ⟨21341011253344065645085889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14227340835562710430057259 21341011253344065645085889)
      ·
        refine ⟨16005758440008049233814417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21341011253344065645085889 16005758440008049233814417)
        ·
          refine ⟨12004318830006036925360813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16005758440008049233814417 12004318830006036925360813)
          ·
            refine ⟨4501619561252263847010305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12004318830006036925360813 4501619561252263847010305)
            ·
              refine ⟨3376214670939197885257729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4501619561252263847010305 3376214670939197885257729)
              ·
                refine ⟨2532161003204398413943297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3376214670939197885257729 2532161003204398413943297)
                ·
                  refine ⟨1899120752403298810457473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2532161003204398413943297 1899120752403298810457473)
                  ·
                    refine ⟨1424340564302474107843105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1899120752403298810457473 1424340564302474107843105)
                    ·
                      refine ⟨1068255423226855580882329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424340564302474107843105 1068255423226855580882329)
                      ·
                        rfl

theorem cell23_2080420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_2080420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080420 prefixEnd_2080420 := by exact prefixLift 2080420
  have htrace : WordTrace (prefixWord ++ tailWord_2080420) baseStart_2080420 baseEnd_2080420 := by
    simpa [prefixWord, tailWord_2080420, baseEnd_2080420] using wordTrace_append hprefix tailTrace_2080420
  have hstable : (prefixWord ++ tailWord_2080420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080420).length < 2 ^ (prefixWord ++ tailWord_2080420).sum := by decide
  have hdescent : baseEnd_2080420 < baseStart_2080420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080493 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_2080493 : Nat := 118140960795 + 2080493 * 2 ^ 59
def prefixEnd_2080493 : Nat := 4983230072969 + 3 ^ 40 * 2080493 * 2
def baseEnd_2080493 : Nat := 1068292907314633795269493

theorem tailTrace_2080493 : CollatzResearch.WordTrace tailWord_2080493 prefixEnd_2080493 1068292907314633795269493 := by
  unfold tailWord_2080493
  simp only [CollatzResearch.WordTrace]
  refine ⟨75881813651736655761046133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50587875767824437174030755 75881813651736655761046133)
  ·
    refine ⟨7113920029850311477598075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75881813651736655761046133 7113920029850311477598075)
    ·
      refine ⟨10670880044775467216397113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7113920029850311477598075 10670880044775467216397113)
      ·
        refine ⟨8003160033581600412297835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10670880044775467216397113 8003160033581600412297835)
        ·
          refine ⟨12004740050372400618446753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8003160033581600412297835 12004740050372400618446753)
          ·
            refine ⟨9003555037779300463835065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12004740050372400618446753 9003555037779300463835065)
            ·
              refine ⟨6752666278334475347876299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9003555037779300463835065 6752666278334475347876299)
              ·
                refine ⟨10128999417501713021814449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6752666278334475347876299 10128999417501713021814449)
                ·
                  refine ⟨7596749563126284766360837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10128999417501713021814449 7596749563126284766360837)
                  ·
                    refine ⟨1424390543086178393692657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7596749563126284766360837 1424390543086178393692657)
                    ·
                      refine ⟨1068292907314633795269493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424390543086178393692657 1068292907314633795269493)
                      ·
                        rfl

theorem cell23_2080493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_2080493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080493 prefixEnd_2080493 := by exact prefixLift 2080493
  have htrace : WordTrace (prefixWord ++ tailWord_2080493) baseStart_2080493 baseEnd_2080493 := by
    simpa [prefixWord, tailWord_2080493, baseEnd_2080493] using wordTrace_append hprefix tailTrace_2080493
  have hstable : (prefixWord ++ tailWord_2080493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080493).length < 2 ^ (prefixWord ++ tailWord_2080493).sum := by decide
  have hdescent : baseEnd_2080493 < baseStart_2080493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080499 : List Nat := [1, 1, 1, 2, 2, 3, 2, 5, 6]
def baseStart_2080499 : Nat := 118140960795 + 2080499 * 2 ^ 59
def prefixEnd_2080499 : Nat := 4983230072969 + 3 ^ 40 * 2080499 * 2
def baseEnd_2080499 : Nat := 118699554244284530199385

theorem tailTrace_2080499 : CollatzResearch.WordTrace tailWord_2080499 prefixEnd_2080499 118699554244284530199385 := by
  unfold tailWord_2080499
  simp only [CollatzResearch.WordTrace]
  refine ⟨75882032489714918785764551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50588021659809945857176367 75882032489714918785764551)
  ·
    refine ⟨113823048734572378178646827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75882032489714918785764551 113823048734572378178646827)
    ·
      refine ⟨170734573101858567267970241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113823048734572378178646827 170734573101858567267970241)
      ·
        refine ⟨128050929826393925450977681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170734573101858567267970241 128050929826393925450977681)
        ·
          refine ⟨96038197369795444088233261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128050929826393925450977681 96038197369795444088233261)
          ·
            refine ⟨36014324013673291533087473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96038197369795444088233261 36014324013673291533087473)
            ·
              refine ⟨27010743010254968649815605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36014324013673291533087473 27010743010254968649815605)
              ·
                refine ⟨2532257157211403310920213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27010743010254968649815605 2532257157211403310920213)
                ·
                  refine ⟨118699554244284530199385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2532257157211403310920213 118699554244284530199385)
                  ·
                    rfl

theorem cell23_2080499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 6].length) (baseStart_2080499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080499 prefixEnd_2080499 := by exact prefixLift 2080499
  have htrace : WordTrace (prefixWord ++ tailWord_2080499) baseStart_2080499 baseEnd_2080499 := by
    simpa [prefixWord, tailWord_2080499, baseEnd_2080499] using wordTrace_append hprefix tailTrace_2080499
  have hstable : (prefixWord ++ tailWord_2080499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080499).length < 2 ^ (prefixWord ++ tailWord_2080499).sum := by decide
  have hdescent : baseEnd_2080499 < baseStart_2080499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080529 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 5, 5]
def baseStart_2080529 : Nat := 118140960795 + 2080529 * 2 ^ 59
def prefixEnd_2080529 : Nat := 4983230072969 + 3 ^ 40 * 2080529 * 2
def baseEnd_2080529 : Nat := 356103797539398551473109

theorem tailTrace_2080529 : CollatzResearch.WordTrace tailWord_2080529 prefixEnd_2080529 356103797539398551473109 := by
  unfold tailWord_2080529
  simp only [CollatzResearch.WordTrace]
  refine ⟨75883126679606233909356641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50588751119737489272904427 75883126679606233909356641)
  ·
    refine ⟨56912345009704675432017481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75883126679606233909356641 56912345009704675432017481)
    ·
      refine ⟨42684258757278506574013111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56912345009704675432017481 42684258757278506574013111)
      ·
        refine ⟨64026388135917759861019667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42684258757278506574013111 64026388135917759861019667)
        ·
          refine ⟨96039582203876639791529501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64026388135917759861019667 96039582203876639791529501)
          ·
            refine ⟨36014843326453739921823563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96039582203876639791529501 36014843326453739921823563)
            ·
              refine ⟨54022264989680609882735345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36014843326453739921823563 54022264989680609882735345)
              ·
                refine ⟨40516698742260457412051509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54022264989680609882735345 40516698742260457412051509)
                ·
                  refine ⟨3798440507086917882379829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40516698742260457412051509 3798440507086917882379829)
                  ·
                    refine ⟨356103797539398551473109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3798440507086917882379829 356103797539398551473109)
                    ·
                      rfl

theorem cell23_2080529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_2080529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080529 prefixEnd_2080529 := by exact prefixLift 2080529
  have htrace : WordTrace (prefixWord ++ tailWord_2080529) baseStart_2080529 baseEnd_2080529 := by
    simpa [prefixWord, tailWord_2080529, baseEnd_2080529] using wordTrace_append hprefix tailTrace_2080529
  have hstable : (prefixWord ++ tailWord_2080529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080529).length < 2 ^ (prefixWord ++ tailWord_2080529).sum := by decide
  have hdescent : baseEnd_2080529 < baseStart_2080529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080530 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2080530 : Nat := 118140960795 + 2080530 * 2 ^ 59
def prefixEnd_2080530 : Nat := 4983230072969 + 3 ^ 40 * 2080530 * 2
def baseEnd_2080530 : Nat := 1068311906098850150506823

theorem tailTrace_2080530 : CollatzResearch.WordTrace tailWord_2080530 prefixEnd_2080530 1068311906098850150506823 := by
  unfold tailWord_2080530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18970790788150652770035761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50588775435068407386762029 18970790788150652770035761)
  ·
    refine ⟨14228093091112989577526821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18970790788150652770035761 14228093091112989577526821)
    ·
      refine ⟨2667767454583685545786279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14228093091112989577526821 2667767454583685545786279)
      ·
        refine ⟨4001651181875528318679419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2667767454583685545786279 4001651181875528318679419)
        ·
          refine ⟨6002476772813292478019129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4001651181875528318679419 6002476772813292478019129)
          ·
            refine ⟨4501857579609969358514347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6002476772813292478019129 4501857579609969358514347)
            ·
              refine ⟨6752786369414954037771521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4501857579609969358514347 6752786369414954037771521)
              ·
                refine ⟨5064589777061215528328641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6752786369414954037771521 5064589777061215528328641)
                ·
                  refine ⟨3798442332795911646246481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5064589777061215528328641 3798442332795911646246481)
                  ·
                    refine ⟨2848831749596933734684861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3798442332795911646246481 2848831749596933734684861)
                    ·
                      refine ⟨1068311906098850150506823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2848831749596933734684861 1068311906098850150506823)
                      ·
                        rfl

theorem cell23_2080530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2080530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080530 prefixEnd_2080530 := by exact prefixLift 2080530
  have htrace : WordTrace (prefixWord ++ tailWord_2080530) baseStart_2080530 baseEnd_2080530 := by
    simpa [prefixWord, tailWord_2080530, baseEnd_2080530] using wordTrace_append hprefix tailTrace_2080530
  have hstable : (prefixWord ++ tailWord_2080530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080530).length < 2 ^ (prefixWord ++ tailWord_2080530).sum := by decide
  have hdescent : baseEnd_2080530 < baseStart_2080530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080546 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2080546 : Nat := 118140960795 + 2080546 * 2 ^ 59
def prefixEnd_2080546 : Nat := 4983230072969 + 3 ^ 40 * 2080546 * 2
def baseEnd_2080546 : Nat := 356106707263107362635583

theorem tailTrace_2080546 : CollatzResearch.WordTrace tailWord_2080546 prefixEnd_2080546 356106707263107362635583 := by
  unfold tailWord_2080546
  simp only [CollatzResearch.WordTrace]
  refine ⟨18970936680136161453181373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50589164480363097208483661 18970936680136161453181373)
  ·
    refine ⟨7114101255051060544943015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18970936680136161453181373 7114101255051060544943015)
    ·
      refine ⟨10671151882576590817414523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7114101255051060544943015 10671151882576590817414523)
      ·
        refine ⟨16006727823864886226121785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10671151882576590817414523 16006727823864886226121785)
        ·
          refine ⟨12005045867898664669591339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16006727823864886226121785 12005045867898664669591339)
          ·
            refine ⟨18007568801847997004387009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12005045867898664669591339 18007568801847997004387009)
            ·
              refine ⟨13505676601385997753290257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18007568801847997004387009 13505676601385997753290257)
              ·
                refine ⟨10129257451039498314967693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13505676601385997753290257 10129257451039498314967693)
                ·
                  refine ⟨3798471544139811868112885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10129257451039498314967693 3798471544139811868112885)
                  ·
                    refine ⟨356106707263107362635583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3798471544139811868112885 356106707263107362635583)
                    ·
                      rfl

theorem cell23_2080546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2080546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080546 prefixEnd_2080546 := by exact prefixLift 2080546
  have htrace : WordTrace (prefixWord ++ tailWord_2080546) baseStart_2080546 baseEnd_2080546 := by
    simpa [prefixWord, tailWord_2080546, baseEnd_2080546] using wordTrace_append hprefix tailTrace_2080546
  have hstable : (prefixWord ++ tailWord_2080546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080546).length < 2 ^ (prefixWord ++ tailWord_2080546).sum := by decide
  have hdescent : baseEnd_2080546 < baseStart_2080546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080570 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2]
def baseStart_2080570 : Nat := 118140960795 + 2080570 * 2 ^ 59
def prefixEnd_2080570 : Nat := 4983230072969 + 3 ^ 40 * 2080570 * 2
def baseEnd_2080570 : Nat := 1068332445325029994006639

theorem tailTrace_2080570 : CollatzResearch.WordTrace tailWord_2080570 prefixEnd_2080570 1068332445325029994006639 := by
  unfold tailWord_2080570
  simp only [CollatzResearch.WordTrace]
  refine ⟨18971155518114424477899791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50589748048305131941066109 18971155518114424477899791)
  ·
    refine ⟨28456733277171636716849687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18971155518114424477899791 28456733277171636716849687)
    ·
      refine ⟨42685099915757455075274531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28456733277171636716849687 42685099915757455075274531)
      ·
        refine ⟨64027649873636182612911797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42685099915757455075274531 64027649873636182612911797)
        ·
          refine ⟨6002592175653392119960481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64027649873636182612911797 6002592175653392119960481)
          ·
            refine ⟨4501944131740044089970361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6002592175653392119960481 4501944131740044089970361)
            ·
              refine ⟨3376458098805033067477771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4501944131740044089970361 3376458098805033067477771)
              ·
                refine ⟨5064687148207549601216657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376458098805033067477771 5064687148207549601216657)
                ·
                  refine ⟨3798515361155662200912493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5064687148207549601216657 3798515361155662200912493)
                  ·
                    refine ⟨1424443260433373325342185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3798515361155662200912493 1424443260433373325342185)
                    ·
                      refine ⟨1068332445325029994006639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424443260433373325342185 1068332445325029994006639)
                      ·
                        rfl

theorem cell23_2080570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2].length) (baseStart_2080570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080570 prefixEnd_2080570 := by exact prefixLift 2080570
  have htrace : WordTrace (prefixWord ++ tailWord_2080570) baseStart_2080570 baseEnd_2080570 := by
    simpa [prefixWord, tailWord_2080570, baseEnd_2080570] using wordTrace_append hprefix tailTrace_2080570
  have hstable : (prefixWord ++ tailWord_2080570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080570).length < 2 ^ (prefixWord ++ tailWord_2080570).sum := by decide
  have hdescent : baseEnd_2080570 < baseStart_2080570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080593 : List Nat := [1, 2, 2, 1, 5, 1, 1, 4, 2, 4]
def baseStart_2080593 : Nat := 118140960795 + 2080593 * 2 ^ 59
def prefixEnd_2080593 : Nat := 4983230072969 + 3 ^ 40 * 2080593 * 2
def baseEnd_2080593 : Nat := 356114751793361134673011

theorem tailTrace_2080593 : CollatzResearch.WordTrace tailWord_2080593 prefixEnd_2080593 356114751793361134673011 := by
  unfold tailWord_2080593
  simp only [CollatzResearch.WordTrace]
  refine ⟨75885460951374372839686433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50590307300916248559790955 75885460951374372839686433)
  ·
    refine ⟨56914095713530779629764825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75885460951374372839686433 56914095713530779629764825)
    ·
      refine ⟨42685571785148084722323619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56914095713530779629764825 42685571785148084722323619)
      ·
        refine ⟨64028357677722127083485429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42685571785148084722323619 64028357677722127083485429)
        ·
          refine ⟨6002658532286449414076759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64028357677722127083485429 6002658532286449414076759)
          ·
            refine ⟨9003987798429674121115139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6002658532286449414076759 9003987798429674121115139)
            ·
              refine ⟨13505981697644511181672709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9003987798429674121115139 13505981697644511181672709)
              ·
                refine ⟨2532371568308345846563633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13505981697644511181672709 2532371568308345846563633)
                ·
                  refine ⟨1899278676231259384922725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2532371568308345846563633 1899278676231259384922725)
                  ·
                    refine ⟨356114751793361134673011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1899278676231259384922725 356114751793361134673011)
                    ·
                      rfl

theorem cell23_2080593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_2080593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080593 prefixEnd_2080593 := by exact prefixLift 2080593
  have htrace : WordTrace (prefixWord ++ tailWord_2080593) baseStart_2080593 baseEnd_2080593 := by
    simpa [prefixWord, tailWord_2080593, baseEnd_2080593] using wordTrace_append hprefix tailTrace_2080593
  have hstable : (prefixWord ++ tailWord_2080593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080593).length < 2 ^ (prefixWord ++ tailWord_2080593).sum := by decide
  have hdescent : baseEnd_2080593 < baseStart_2080593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080594 : List Nat := [3, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_2080594 : Nat := 118140960795 + 2080594 * 2 ^ 59
def prefixEnd_2080594 : Nat := 4983230072969 + 3 ^ 40 * 2080594 * 2
def baseEnd_2080594 : Nat := 1068344768860737900106529

theorem tailTrace_2080594 : CollatzResearch.WordTrace tailWord_2080594 prefixEnd_2080594 1068344768860737900106529 := by
  unfold tailWord_2080594
  simp only [CollatzResearch.WordTrace]
  refine ⟨18971374356092687502618209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50590331616247166673648557 18971374356092687502618209)
  ·
    refine ⟨14228530767069515626963657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18971374356092687502618209 14228530767069515626963657)
    ·
      refine ⟨10671398075302136720222743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14228530767069515626963657 10671398075302136720222743)
      ·
        refine ⟨16007097112953205080334115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10671398075302136720222743 16007097112953205080334115)
        ·
          refine ⟨24010645669429807620501173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16007097112953205080334115 24010645669429807620501173)
          ·
            refine ⟨2250998031509044464421985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24010645669429807620501173 2250998031509044464421985)
            ·
              refine ⟨1688248523631783348316489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2250998031509044464421985 1688248523631783348316489)
              ·
                refine ⟨1266186392723837511237367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1688248523631783348316489 1266186392723837511237367)
                ·
                  refine ⟨1899279589085756266856051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266186392723837511237367 1899279589085756266856051)
                  ·
                    refine ⟨2848919383628634400284077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1899279589085756266856051 2848919383628634400284077)
                    ·
                      refine ⟨1068344768860737900106529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2848919383628634400284077 1068344768860737900106529)
                      ·
                        rfl

theorem cell23_2080594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_2080594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080594 prefixEnd_2080594 := by exact prefixLift 2080594
  have htrace : WordTrace (prefixWord ++ tailWord_2080594) baseStart_2080594 baseEnd_2080594 := by
    simpa [prefixWord, tailWord_2080594, baseEnd_2080594] using wordTrace_append hprefix tailTrace_2080594
  have hstable : (prefixWord ++ tailWord_2080594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080594).length < 2 ^ (prefixWord ++ tailWord_2080594).sum := by decide
  have hdescent : baseEnd_2080594 < baseStart_2080594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080610 : List Nat := [3, 3, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_2080610 : Nat := 118140960795 + 2080610 * 2 ^ 59
def prefixEnd_2080610 : Nat := 4983230072969 + 3 ^ 40 * 2080610 * 2
def baseEnd_2080610 : Nat := 356117661517069945835485

theorem tailTrace_2080610 : CollatzResearch.WordTrace tailWord_2080610 prefixEnd_2080610 356117661517069945835485 := by
  unfold tailWord_2080610
  simp only [CollatzResearch.WordTrace]
  refine ⟨18971520248078196185763821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50590720661541856495370189 18971520248078196185763821)
  ·
    refine ⟨7114320093029323569661433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18971520248078196185763821 7114320093029323569661433)
    ·
      refine ⟨5335740069771992677246075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7114320093029323569661433 5335740069771992677246075)
      ·
        refine ⟨8003610104657989015869113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5335740069771992677246075 8003610104657989015869113)
        ·
          refine ⟨6002707578493491761901835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8003610104657989015869113 6002707578493491761901835)
          ·
            refine ⟨9004061367740237642852753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6002707578493491761901835 9004061367740237642852753)
            ·
              refine ⟨6753046025805178232139565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9004061367740237642852753 6753046025805178232139565)
              ·
                refine ⟨2532392259676941837052337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6753046025805178232139565 2532392259676941837052337)
                ·
                  refine ⟨1899294194757706377789253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2532392259676941837052337 1899294194757706377789253)
                  ·
                    refine ⟨356117661517069945835485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1899294194757706377789253 356117661517069945835485)
                    ·
                      rfl

theorem cell23_2080610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_2080610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080610 prefixEnd_2080610 := by exact prefixLift 2080610
  have htrace : WordTrace (prefixWord ++ tailWord_2080610) baseStart_2080610 baseEnd_2080610 := by
    simpa [prefixWord, tailWord_2080610, baseEnd_2080610] using wordTrace_append hprefix tailTrace_2080610
  have hstable : (prefixWord ++ tailWord_2080610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080610).length < 2 ^ (prefixWord ++ tailWord_2080610).sum := by decide
  have hdescent : baseEnd_2080610 < baseStart_2080610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080619 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 4, 7]
def baseStart_2080619 : Nat := 118140960795 + 2080619 * 2 ^ 59
def prefixEnd_2080619 : Nat := 4983230072969 + 3 ^ 40 * 2080619 * 2
def baseEnd_2080619 : Nat := 356119201959033434097971

theorem tailTrace_2080619 : CollatzResearch.WordTrace tailWord_2080619 prefixEnd_2080619 356119201959033434097971 := by
  unfold tailWord_2080619
  simp only [CollatzResearch.WordTrace]
  refine ⟨75886409249280179280132911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50590939499520119520088607 75886409249280179280132911)
  ·
    refine ⟨113829613873920268920199367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75886409249280179280132911 113829613873920268920199367)
    ·
      refine ⟨170744420810880403380299051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113829613873920268920199367 170744420810880403380299051)
      ·
        refine ⟨256116631216320605070448577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170744420810880403380299051 256116631216320605070448577)
        ·
          refine ⟨192087473412240453802836433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256116631216320605070448577 192087473412240453802836433)
          ·
            refine ⟨144065605059180340352127325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192087473412240453802836433 144065605059180340352127325)
            ·
              refine ⟨54024601897192627632047747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144065605059180340352127325 54024601897192627632047747)
              ·
                refine ⟨81036902845788941448071621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54024601897192627632047747 81036902845788941448071621)
                ·
                  refine ⟨15194419283585426521513429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81036902845788941448071621 15194419283585426521513429)
                  ·
                    refine ⟨356119201959033434097971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15194419283585426521513429 356119201959033434097971)
                    ·
                      rfl

theorem cell23_2080619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 7].length) (baseStart_2080619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080619 prefixEnd_2080619 := by exact prefixLift 2080619
  have htrace : WordTrace (prefixWord ++ tailWord_2080619) baseStart_2080619 baseEnd_2080619 := by
    simpa [prefixWord, tailWord_2080619, baseEnd_2080619] using wordTrace_append hprefix tailTrace_2080619
  have hstable : (prefixWord ++ tailWord_2080619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080619).length < 2 ^ (prefixWord ++ tailWord_2080619).sum := by decide
  have hdescent : baseEnd_2080619 < baseStart_2080619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080633 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 4, 1, 3]
def baseStart_2080633 : Nat := 118140960795 + 2080633 * 2 ^ 59
def prefixEnd_2080633 : Nat := 4983230072969 + 3 ^ 40 * 2080633 * 2
def baseEnd_2080633 : Nat := 1068364794606263247518849

theorem tailTrace_2080633 : CollatzResearch.WordTrace tailWord_2080633 prefixEnd_2080633 1068364794606263247518849 := by
  unfold tailWord_2080633
  simp only [CollatzResearch.WordTrace]
  refine ⟨75886919871229459671142553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50591279914152973114095035 75886919871229459671142553)
  ·
    refine ⟨56915189903422094753356915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75886919871229459671142553 56915189903422094753356915)
    ·
      refine ⟨85372784855133142130035373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56915189903422094753356915 85372784855133142130035373)
      ·
        refine ⟨32014794320674928298763265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85372784855133142130035373 32014794320674928298763265)
        ·
          refine ⟨24011095740506196224072449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32014794320674928298763265 24011095740506196224072449)
          ·
            refine ⟨18008321805379647168054337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24011095740506196224072449 18008321805379647168054337)
            ·
              refine ⟨13506241354034735376040753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18008321805379647168054337 13506241354034735376040753)
              ·
                refine ⟨10129681015526051532030565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13506241354034735376040753 10129681015526051532030565)
                ·
                  refine ⟨1899315190411134662255731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10129681015526051532030565 1899315190411134662255731)
                  ·
                    refine ⟨2848972785616701993383597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1899315190411134662255731 2848972785616701993383597)
                    ·
                      refine ⟨1068364794606263247518849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2848972785616701993383597 1068364794606263247518849)
                      ·
                        rfl

theorem cell23_2080633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_2080633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080633 prefixEnd_2080633 := by exact prefixLift 2080633
  have htrace : WordTrace (prefixWord ++ tailWord_2080633) baseStart_2080633 baseEnd_2080633 := by
    simpa [prefixWord, tailWord_2080633, baseEnd_2080633] using wordTrace_append hprefix tailTrace_2080633
  have hstable : (prefixWord ++ tailWord_2080633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080633).length < 2 ^ (prefixWord ++ tailWord_2080633).sum := by decide
  have hdescent : baseEnd_2080633 < baseStart_2080633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080693 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_2080693 : Nat := 118140960795 + 2080693 * 2 ^ 59
def prefixEnd_2080693 : Nat := 4983230072969 + 3 ^ 40 * 2080693 * 2
def baseEnd_2080693 : Nat := 1068395603445533012768573

theorem tailTrace_2080693 : CollatzResearch.WordTrace tailWord_2080693 prefixEnd_2080693 1068395603445533012768573 := by
  unfold tailWord_2080693
  simp only [CollatzResearch.WordTrace]
  refine ⟨75889108251012089918326733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50592738834008059945551155 75889108251012089918326733)
  ·
    refine ⟨28458415594129533719372525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75889108251012089918326733 28458415594129533719372525)
    ·
      refine ⟨10671905847798575144764697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28458415594129533719372525 10671905847798575144764697)
      ·
        refine ⟨8003929385848931358573523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10671905847798575144764697 8003929385848931358573523)
        ·
          refine ⟨12005894078773397037860285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8003929385848931358573523 12005894078773397037860285)
          ·
            refine ⟨4502210279540023889197607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12005894078773397037860285 4502210279540023889197607)
            ·
              refine ⟨6753315419310035833796411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502210279540023889197607 6753315419310035833796411)
              ·
                refine ⟨10129973128965053750694617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6753315419310035833796411 10129973128965053750694617)
                ·
                  refine ⟨7597479846723790313020963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10129973128965053750694617 7597479846723790313020963)
                  ·
                    refine ⟨11396219770085685469531445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7597479846723790313020963 11396219770085685469531445)
                    ·
                      refine ⟨1068395603445533012768573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11396219770085685469531445 1068395603445533012768573)
                      ·
                        rfl

theorem cell23_2080693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_2080693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080693 prefixEnd_2080693 := by exact prefixLift 2080693
  have htrace : WordTrace (prefixWord ++ tailWord_2080693) baseStart_2080693 baseEnd_2080693 := by
    simpa [prefixWord, tailWord_2080693, baseEnd_2080693] using wordTrace_append hprefix tailTrace_2080693
  have hstable : (prefixWord ++ tailWord_2080693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080693).length < 2 ^ (prefixWord ++ tailWord_2080693).sum := by decide
  have hdescent : baseEnd_2080693 < baseStart_2080693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080763 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 4]
def baseStart_2080763 : Nat := 118140960795 + 2080763 * 2 ^ 59
def prefixEnd_2080763 : Nat := 4983230072969 + 3 ^ 40 * 2080763 * 2
def baseEnd_2080763 : Nat := 1068431547091347738893251

theorem tailTrace_2080763 : CollatzResearch.WordTrace tailWord_2080763 prefixEnd_2080763 1068431547091347738893251 := by
  unfold tailWord_2080763
  simp only [CollatzResearch.WordTrace]
  refine ⟨75891661360758491873374943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50594440907172327915583295 75891661360758491873374943)
  ·
    refine ⟨113837492041137737810062415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75891661360758491873374943 113837492041137737810062415)
    ·
      refine ⟨170756238061706606715093623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113837492041137737810062415 170756238061706606715093623)
      ·
        refine ⟨256134357092559910072640435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170756238061706606715093623 256134357092559910072640435)
        ·
          refine ⟨384201535638839865108960653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256134357092559910072640435 384201535638839865108960653)
          ·
            refine ⟨144075575864564949415860245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384201535638839865108960653 144075575864564949415860245)
            ·
              refine ⟨6753542618651482003868449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144075575864564949415860245 6753542618651482003868449)
              ·
                refine ⟨5065156963988611502901337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6753542618651482003868449 5065156963988611502901337)
                ·
                  refine ⟨3798867722991458627176003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5065156963988611502901337 3798867722991458627176003)
                  ·
                    refine ⟨5698301584487187940764005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3798867722991458627176003 5698301584487187940764005)
                    ·
                      refine ⟨1068431547091347738893251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5698301584487187940764005 1068431547091347738893251)
                      ·
                        rfl

theorem cell23_2080763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 4].length) (baseStart_2080763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080763 prefixEnd_2080763 := by exact prefixLift 2080763
  have htrace : WordTrace (prefixWord ++ tailWord_2080763) baseStart_2080763 baseEnd_2080763 := by
    simpa [prefixWord, tailWord_2080763, baseEnd_2080763] using wordTrace_append hprefix tailTrace_2080763
  have hstable : (prefixWord ++ tailWord_2080763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080763).length < 2 ^ (prefixWord ++ tailWord_2080763).sum := by decide
  have hdescent : baseEnd_2080763 < baseStart_2080763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080780 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 2, 4, 2]
def baseStart_2080780 : Nat := 118140960795 + 2080780 * 2 ^ 59
def prefixEnd_2080780 : Nat := 4983230072969 + 3 ^ 40 * 2080780 * 2
def baseEnd_2080780 : Nat := 1068440276262474172380673

theorem tailTrace_2080780 : CollatzResearch.WordTrace tailWord_2080780 prefixEnd_2080780 1068440276262474172380673 := by
  unfold tailWord_2080780
  simp only [CollatzResearch.WordTrace]
  refine ⟨37946140700848451888371897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50594854267797935851162529 37946140700848451888371897)
  ·
    refine ⟨28459605525636338916278923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37946140700848451888371897 28459605525636338916278923)
    ·
      refine ⟨42689408288454508374418385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28459605525636338916278923 42689408288454508374418385)
      ·
        refine ⟨32017056216340881280813789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42689408288454508374418385 32017056216340881280813789)
        ·
          refine ⟨12006396081127830480305171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32017056216340881280813789 12006396081127830480305171)
          ·
            refine ⟨18009594121691745720457757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12006396081127830480305171 18009594121691745720457757)
            ·
              refine ⟨6753597795634404645171659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18009594121691745720457757 6753597795634404645171659)
              ·
                refine ⟨10130396693451606967757489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6753597795634404645171659 10130396693451606967757489)
                ·
                  refine ⟨7597797520088705225818117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10130396693451606967757489 7597797520088705225818117)
                  ·
                    refine ⟨1424587035016632229840897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7597797520088705225818117 1424587035016632229840897)
                    ·
                      refine ⟨1068440276262474172380673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424587035016632229840897 1068440276262474172380673)
                      ·
                        rfl

theorem cell23_2080780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_2080780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080780 prefixEnd_2080780 := by exact prefixLift 2080780
  have htrace : WordTrace (prefixWord ++ tailWord_2080780) baseStart_2080780 baseEnd_2080780 := by
    simpa [prefixWord, tailWord_2080780, baseEnd_2080780] using wordTrace_append hprefix tailTrace_2080780
  have hstable : (prefixWord ++ tailWord_2080780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080780).length < 2 ^ (prefixWord ++ tailWord_2080780).sum := by decide
  have hdescent : baseEnd_2080780 < baseStart_2080780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080797 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_2080797 : Nat := 118140960795 + 2080797 * 2 ^ 59
def prefixEnd_2080797 : Nat := 4983230072969 + 3 ^ 40 * 2080797 * 2
def baseEnd_2080797 : Nat := 1068449005433600605868095

theorem tailTrace_2080797 : CollatzResearch.WordTrace tailWord_2080797 prefixEnd_2080797 1068449005433600605868095 := by
  unfold tailWord_2080797
  simp only [CollatzResearch.WordTrace]
  refine ⟨75892901442635315680112645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50595267628423543786741763 75892901442635315680112645)
  ·
    refine ⟨14229919020494121690021121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75892901442635315680112645 14229919020494121690021121)
    ·
      refine ⟨10672439265370591267515841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14229919020494121690021121 10672439265370591267515841)
      ·
        refine ⟨8004329449027943450636881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10672439265370591267515841 8004329449027943450636881)
        ·
          refine ⟨6003247086770957587977661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8004329449027943450636881 6003247086770957587977661)
          ·
            refine ⟨2251217657539109095491623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6003247086770957587977661 2251217657539109095491623)
            ·
              refine ⟨3376826486308663643237435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2251217657539109095491623 3376826486308663643237435)
              ·
                refine ⟨5065239729462995464856153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376826486308663643237435 5065239729462995464856153)
                ·
                  refine ⟨3798929797097246598642115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5065239729462995464856153 3798929797097246598642115)
                  ·
                    refine ⟨5698394695645869897963173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3798929797097246598642115 5698394695645869897963173)
                    ·
                      refine ⟨1068449005433600605868095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5698394695645869897963173 1068449005433600605868095)
                      ·
                        rfl

theorem cell23_2080797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_2080797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080797 prefixEnd_2080797 := by exact prefixLift 2080797
  have htrace : WordTrace (prefixWord ++ tailWord_2080797) baseStart_2080797 baseEnd_2080797 := by
    simpa [prefixWord, tailWord_2080797, baseEnd_2080797] using wordTrace_append hprefix tailTrace_2080797
  have hstable : (prefixWord ++ tailWord_2080797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080797).length < 2 ^ (prefixWord ++ tailWord_2080797).sum := by decide
  have hdescent : baseEnd_2080797 < baseStart_2080797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080840 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 6, 3, 2]
def baseStart_2080840 : Nat := 118140960795 + 2080840 * 2 ^ 59
def prefixEnd_2080840 : Nat := 4983230072969 + 3 ^ 40 * 2080840 * 2
def baseEnd_2080840 : Nat := 1068471085101743937630397

theorem tailTrace_2080840 : CollatzResearch.WordTrace tailWord_2080840 prefixEnd_2080840 1068471085101743937630397 := by
  unfold tailWord_2080840
  simp only [CollatzResearch.WordTrace]
  refine ⟨37947234890739767011963987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50596313187653022682618649 37947234890739767011963987)
  ·
    refine ⟨56920852336109650517945981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37947234890739767011963987 56920852336109650517945981)
    ·
      refine ⟨21345319626041118944229743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56920852336109650517945981 21345319626041118944229743)
      ·
        refine ⟨32017979439061678416344615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21345319626041118944229743 32017979439061678416344615)
        ·
          refine ⟨48026969158592517624516923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32017979439061678416344615 48026969158592517624516923)
          ·
            refine ⟨72040453737888776436775385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48026969158592517624516923 72040453737888776436775385)
            ·
              refine ⟨54030340303416582327581539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72040453737888776436775385 54030340303416582327581539)
              ·
                refine ⟨81045510455124873491372309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54030340303416582327581539 81045510455124873491372309)
                ·
                  refine ⟨3799008302583978444908077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81045510455124873491372309 3799008302583978444908077)
                  ·
                    refine ⟨1424628113468991916840529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3799008302583978444908077 1424628113468991916840529)
                    ·
                      refine ⟨1068471085101743937630397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424628113468991916840529 1068471085101743937630397)
                      ·
                        rfl

theorem cell23_2080840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_2080840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080840 prefixEnd_2080840 := by exact prefixLift 2080840
  have htrace : WordTrace (prefixWord ++ tailWord_2080840) baseStart_2080840 baseEnd_2080840 := by
    simpa [prefixWord, tailWord_2080840, baseEnd_2080840] using wordTrace_append hprefix tailTrace_2080840
  have hstable : (prefixWord ++ tailWord_2080840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080840).length < 2 ^ (prefixWord ++ tailWord_2080840).sum := by decide
  have hdescent : baseEnd_2080840 < baseStart_2080840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080864 : List Nat := [2, 1, 1, 3, 2, 3, 3, 3, 1, 1, 3]
def baseStart_2080864 : Nat := 118140960795 + 2080864 * 2 ^ 59
def prefixEnd_2080864 : Nat := 4983230072969 + 3 ^ 40 * 2080864 * 2
def baseEnd_2080864 : Nat := 1068483408637451843730287

theorem tailTrace_2080864 : CollatzResearch.WordTrace tailWord_2080864 prefixEnd_2080864 1068483408637451843730287 := by
  unfold tailWord_2080864
  simp only [CollatzResearch.WordTrace]
  refine ⟨37947672566696293061400823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50596896755595057415201097 37947672566696293061400823)
  ·
    refine ⟨56921508850044439592101235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37947672566696293061400823 56921508850044439592101235)
    ·
      refine ⟨85382263275066659388151853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56921508850044439592101235 85382263275066659388151853)
      ·
        refine ⟨32018348728149997270556945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85382263275066659388151853 32018348728149997270556945)
        ·
          refine ⟨24013761546112497952917709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32018348728149997270556945 24013761546112497952917709)
          ·
            refine ⟨9005160579792186732344141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24013761546112497952917709 9005160579792186732344141)
            ·
              refine ⟨3376935217422070024629053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9005160579792186732344141 3376935217422070024629053)
              ·
                refine ⟨1266350706533276259235895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3376935217422070024629053 1266350706533276259235895)
                ·
                  refine ⟨1899526059799914388853843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266350706533276259235895 1899526059799914388853843)
                  ·
                    refine ⟨2849289089699871583280765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1899526059799914388853843 2849289089699871583280765)
                    ·
                      refine ⟨1068483408637451843730287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2849289089699871583280765 1068483408637451843730287)
                      ·
                        rfl

theorem cell23_2080864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_2080864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080864 prefixEnd_2080864 := by exact prefixLift 2080864
  have htrace : WordTrace (prefixWord ++ tailWord_2080864) baseStart_2080864 baseEnd_2080864 := by
    simpa [prefixWord, tailWord_2080864, baseEnd_2080864] using wordTrace_append hprefix tailTrace_2080864
  have hstable : (prefixWord ++ tailWord_2080864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080864).length < 2 ^ (prefixWord ++ tailWord_2080864).sum := by decide
  have hdescent : baseEnd_2080864 < baseStart_2080864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080874 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_2080874 : Nat := 118140960795 + 2080874 * 2 ^ 59
def prefixEnd_2080874 : Nat := 4983230072969 + 3 ^ 40 * 2080874 * 2
def baseEnd_2080874 : Nat := 1068488543443996804605241

theorem tailTrace_2080874 : CollatzResearch.WordTrace tailWord_2080874 prefixEnd_2080874 1068488543443996804605241 := by
  unfold tailWord_2080874
  simp only [CollatzResearch.WordTrace]
  refine ⟨18973927465839089457666419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50597139908904238553777117 18973927465839089457666419)
  ·
    refine ⟨28460891198758634186499629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18973927465839089457666419 28460891198758634186499629)
    ·
      refine ⟨10672834199534487819937361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28460891198758634186499629 10672834199534487819937361)
      ·
        refine ⟨8004625649650865864953021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10672834199534487819937361 8004625649650865864953021)
        ·
          refine ⟨3001734618619074699357383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8004625649650865864953021 3001734618619074699357383)
          ·
            refine ⟨4502601927928612049036075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001734618619074699357383 4502601927928612049036075)
            ·
              refine ⟨6753902891892918073554113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502601927928612049036075 6753902891892918073554113)
              ·
                refine ⟨5065427168919688555165585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6753902891892918073554113 5065427168919688555165585)
                ·
                  refine ⟨3799070376689766416374189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5065427168919688555165585 3799070376689766416374189)
                  ·
                    refine ⟨1424651391258662406140321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3799070376689766416374189 1424651391258662406140321)
                    ·
                      refine ⟨1068488543443996804605241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424651391258662406140321 1068488543443996804605241)
                      ·
                        rfl

theorem cell23_2080874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_2080874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080874 prefixEnd_2080874 := by exact prefixLift 2080874
  have htrace : WordTrace (prefixWord ++ tailWord_2080874) baseStart_2080874 baseEnd_2080874 := by
    simpa [prefixWord, tailWord_2080874, baseEnd_2080874] using wordTrace_append hprefix tailTrace_2080874
  have hstable : (prefixWord ++ tailWord_2080874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080874).length < 2 ^ (prefixWord ++ tailWord_2080874).sum := by decide
  have hdescent : baseEnd_2080874 < baseStart_2080874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080880 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 4, 4]
def baseStart_2080880 : Nat := 118140960795 + 2080880 * 2 ^ 59
def prefixEnd_2080880 : Nat := 4983230072969 + 3 ^ 40 * 2080880 * 2
def baseEnd_2080880 : Nat := 356163874775974593710071

theorem tailTrace_2080880 : CollatzResearch.WordTrace tailWord_2080880 prefixEnd_2080880 356163874775974593710071 := by
  unfold tailWord_2080880
  simp only [CollatzResearch.WordTrace]
  refine ⟨37947964350667310427692047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50597285800889747236922729 37947964350667310427692047)
  ·
    refine ⟨56921946526000965641538071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37947964350667310427692047 56921946526000965641538071)
    ·
      refine ⟨85382919789001448462307107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56921946526000965641538071 85382919789001448462307107)
      ·
        refine ⟨128074379683502172693460661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85382919789001448462307107 128074379683502172693460661)
        ·
          refine ⟨12006973095328328690011937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128074379683502172693460661 12006973095328328690011937)
          ·
            refine ⟨9005229821496246517508953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12006973095328328690011937 9005229821496246517508953)
            ·
              refine ⟨6753922366122184888131715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9005229821496246517508953 6753922366122184888131715)
              ·
                refine ⟨10130883549183277332197573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6753922366122184888131715 10130883549183277332197573)
                ·
                  refine ⟨1899540665471864499787045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10130883549183277332197573 1899540665471864499787045)
                  ·
                    refine ⟨356163874775974593710071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1899540665471864499787045 356163874775974593710071)
                    ·
                      rfl

theorem cell23_2080880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 4, 4].length) (baseStart_2080880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080880 prefixEnd_2080880 := by exact prefixLift 2080880
  have htrace : WordTrace (prefixWord ++ tailWord_2080880) baseStart_2080880 baseEnd_2080880 := by
    simpa [prefixWord, tailWord_2080880, baseEnd_2080880] using wordTrace_append hprefix tailTrace_2080880
  have hstable : (prefixWord ++ tailWord_2080880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080880).length < 2 ^ (prefixWord ++ tailWord_2080880).sum := by decide
  have hdescent : baseEnd_2080880 < baseStart_2080880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080893 : List Nat := [1, 4, 1, 1, 3, 2, 1, 10]
def baseStart_2080893 : Nat := 118140960795 + 2080893 * 2 ^ 59
def prefixEnd_2080893 : Nat := 4983230072969 + 3 ^ 40 * 2080893 * 2
def baseEnd_2080893 : Nat := 39574011095423415935839

theorem tailTrace_2080893 : CollatzResearch.WordTrace tailWord_2080893 prefixEnd_2080893 39574011095423415935839 := by
  unfold tailWord_2080893
  simp only [CollatzResearch.WordTrace]
  refine ⟨75896402850287524075607333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50597601900191682717071555 75896402850287524075607333)
  ·
    refine ⟨14230575534428910764176375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75896402850287524075607333 14230575534428910764176375)
    ·
      refine ⟨21345863301643366146264563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14230575534428910764176375 21345863301643366146264563)
      ·
        refine ⟨32018794952465049219396845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21345863301643366146264563 32018794952465049219396845)
        ·
          refine ⟨12007048107174393457273817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32018794952465049219396845 12007048107174393457273817)
          ·
            refine ⟨9005286080380795092955363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12007048107174393457273817 9005286080380795092955363)
            ·
              refine ⟨13507929120571192639433045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9005286080380795092955363 13507929120571192639433045)
              ·
                refine ⟨39574011095423415935839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13507929120571192639433045 39574011095423415935839)
                ·
                  rfl

theorem cell23_2080893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 10].length) (baseStart_2080893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080893 prefixEnd_2080893 := by exact prefixLift 2080893
  have htrace : WordTrace (prefixWord ++ tailWord_2080893) baseStart_2080893 baseEnd_2080893 := by
    simpa [prefixWord, tailWord_2080893, baseEnd_2080893] using wordTrace_append hprefix tailTrace_2080893
  have hstable : (prefixWord ++ tailWord_2080893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080893).length < 2 ^ (prefixWord ++ tailWord_2080893).sum := by decide
  have hdescent : baseEnd_2080893 < baseStart_2080893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080900 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_2080900 : Nat := 118140960795 + 2080900 * 2 ^ 59
def prefixEnd_2080900 : Nat := 4983230072969 + 3 ^ 40 * 2080900 * 2
def baseEnd_2080900 : Nat := 1068501893941013702880121

theorem tailTrace_2080900 : CollatzResearch.WordTrace tailWord_2080900 prefixEnd_2080900 1068501893941013702880121 := by
  unfold tailWord_2080900
  simp only [CollatzResearch.WordTrace]
  refine ⟨37948329080631082135556077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50597772107508109514074769 37948329080631082135556077)
  ·
    refine ⟨14230623405236655800833529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37948329080631082135556077 14230623405236655800833529)
    ·
      refine ⟨10672967553927491850625147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14230623405236655800833529 10672967553927491850625147)
      ·
        refine ⟨16009451330891237775937721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10672967553927491850625147 16009451330891237775937721)
        ·
          refine ⟨12007088498168428331953291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16009451330891237775937721 12007088498168428331953291)
          ·
            refine ⟨18010632747252642497929937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12007088498168428331953291 18010632747252642497929937)
            ·
              refine ⟨13507974560439481873447453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18010632747252642497929937 13507974560439481873447453)
              ·
                refine ⟨5065490460164805702542795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13507974560439481873447453 5065490460164805702542795)
                ·
                  refine ⟨7598235690247208553814193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065490460164805702542795 7598235690247208553814193)
                  ·
                    refine ⟨5698676767685406415360645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7598235690247208553814193 5698676767685406415360645)
                    ·
                      refine ⟨1068501893941013702880121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5698676767685406415360645 1068501893941013702880121)
                      ·
                        rfl

theorem cell23_2080900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_2080900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080900 prefixEnd_2080900 := by exact prefixLift 2080900
  have htrace : WordTrace (prefixWord ++ tailWord_2080900) baseStart_2080900 baseEnd_2080900 := by
    simpa [prefixWord, tailWord_2080900, baseEnd_2080900] using wordTrace_append hprefix tailTrace_2080900
  have hstable : (prefixWord ++ tailWord_2080900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080900).length < 2 ^ (prefixWord ++ tailWord_2080900).sum := by decide
  have hdescent : baseEnd_2080900 < baseStart_2080900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080904 : List Nat := [2, 1, 3, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2080904 : Nat := 118140960795 + 2080904 * 2 ^ 59
def prefixEnd_2080904 : Nat := 4983230072969 + 3 ^ 40 * 2080904 * 2
def baseEnd_2080904 : Nat := 1068503947863631687230103

theorem tailTrace_2080904 : CollatzResearch.WordTrace tailWord_2080904 prefixEnd_2080904 1068503947863631687230103 := by
  unfold tailWord_2080904
  simp only [CollatzResearch.WordTrace]
  refine ⟨37948402026623836477128883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50597869368831781969505177 37948402026623836477128883)
  ·
    refine ⟨56922603039935754715693325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37948402026623836477128883 56922603039935754715693325)
    ·
      refine ⟨21345976139975908018384997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56922603039935754715693325 21345976139975908018384997)
      ·
        refine ⟨4002370526245482753447187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21345976139975908018384997 4002370526245482753447187)
        ·
          refine ⟨6003555789368224130170781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4002370526245482753447187 6003555789368224130170781)
          ·
            refine ⟨2251333421013084048814043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6003555789368224130170781 2251333421013084048814043)
            ·
              refine ⟨3377000131519626073221065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2251333421013084048814043 3377000131519626073221065)
              ·
                refine ⟨2532750098639719554915799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3377000131519626073221065 2532750098639719554915799)
                ·
                  refine ⟨3799125147959579332373699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532750098639719554915799 3799125147959579332373699)
                  ·
                    refine ⟨5698687721939368998560549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3799125147959579332373699 5698687721939368998560549)
                    ·
                      refine ⟨1068503947863631687230103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5698687721939368998560549 1068503947863631687230103)
                      ·
                        rfl

theorem cell23_2080904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2080904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080904 prefixEnd_2080904 := by exact prefixLift 2080904
  have htrace : WordTrace (prefixWord ++ tailWord_2080904) baseStart_2080904 baseEnd_2080904 := by
    simpa [prefixWord, tailWord_2080904, baseEnd_2080904] using wordTrace_append hprefix tailTrace_2080904
  have hstable : (prefixWord ++ tailWord_2080904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080904).length < 2 ^ (prefixWord ++ tailWord_2080904).sum := by decide
  have hdescent : baseEnd_2080904 < baseStart_2080904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080924 : List Nat := [2, 2, 3, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_2080924 : Nat := 118140960795 + 2080924 * 2 ^ 59
def prefixEnd_2080924 : Nat := 4983230072969 + 3 ^ 40 * 2080924 * 2
def baseEnd_2080924 : Nat := 1068514217476721608980011

theorem tailTrace_2080924 : CollatzResearch.WordTrace tailWord_2080924 prefixEnd_2080924 1068514217476721608980011 := by
  unfold tailWord_2080924
  simp only [CollatzResearch.WordTrace]
  refine ⟨37948766756587608184992913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50598355675450144246657217 37948766756587608184992913)
  ·
    refine ⟨28461575067440706138744685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37948766756587608184992913 28461575067440706138744685)
    ·
      refine ⟨10673090650290264802029257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28461575067440706138744685 10673090650290264802029257)
      ·
        refine ⟨8004817987717698601521943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10673090650290264802029257 8004817987717698601521943)
        ·
          refine ⟨12007226981576547902282915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8004817987717698601521943 12007226981576547902282915)
          ·
            refine ⟨18010840472364821853424373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12007226981576547902282915 18010840472364821853424373)
            ·
              refine ⟨1688516294284202048758535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18010840472364821853424373 1688516294284202048758535)
              ·
                refine ⟨2532774441426303073137803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688516294284202048758535 2532774441426303073137803)
                ·
                  refine ⟨3799161662139454609706705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532774441426303073137803 3799161662139454609706705)
                  ·
                    refine ⟨2849371246604590957280029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3799161662139454609706705 2849371246604590957280029)
                    ·
                      refine ⟨1068514217476721608980011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2849371246604590957280029 1068514217476721608980011)
                      ·
                        rfl

theorem cell23_2080924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_2080924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080924 prefixEnd_2080924 := by exact prefixLift 2080924
  have htrace : WordTrace (prefixWord ++ tailWord_2080924) baseStart_2080924 baseEnd_2080924 := by
    simpa [prefixWord, tailWord_2080924, baseEnd_2080924] using wordTrace_append hprefix tailTrace_2080924
  have hstable : (prefixWord ++ tailWord_2080924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080924).length < 2 ^ (prefixWord ++ tailWord_2080924).sum := by decide
  have hdescent : baseEnd_2080924 < baseStart_2080924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080964 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_2080964 : Nat := 118140960795 + 2080964 * 2 ^ 59
def prefixEnd_2080964 : Nat := 4983230072969 + 3 ^ 40 * 2080964 * 2
def baseEnd_2080964 : Nat := 1068534756702901452479827

theorem tailTrace_2080964 : CollatzResearch.WordTrace tailWord_2080964 prefixEnd_2080964 1068534756702901452479827 := by
  unfold tailWord_2080964
  simp only [CollatzResearch.WordTrace]
  refine ⟨37949496216515151600720973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50599328288686868800961297 37949496216515151600720973)
  ·
    refine ⟨14231061081193181850270365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37949496216515151600720973 14231061081193181850270365)
    ·
      refine ⟨5336647905447443193851387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14231061081193181850270365 5336647905447443193851387)
      ·
        refine ⟨8004971858171164790777081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5336647905447443193851387 8004971858171164790777081)
        ·
          refine ⟨6003728893628373593082811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8004971858171164790777081 6003728893628373593082811)
          ·
            refine ⟨9005593340442560389624217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6003728893628373593082811 9005593340442560389624217)
            ·
              refine ⟨6754195005331920292218163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9005593340442560389624217 6754195005331920292218163)
              ·
                refine ⟨10131292507997880438327245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6754195005331920292218163 10131292507997880438327245)
                ·
                  refine ⟨3799234690499205164372717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10131292507997880438327245 3799234690499205164372717)
                  ·
                    refine ⟨1424713008937201936639769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3799234690499205164372717 1424713008937201936639769)
                    ·
                      refine ⟨1068534756702901452479827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424713008937201936639769 1068534756702901452479827)
                      ·
                        rfl

theorem cell23_2080964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_2080964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080964 prefixEnd_2080964 := by exact prefixLift 2080964
  have htrace : WordTrace (prefixWord ++ tailWord_2080964) baseStart_2080964 baseEnd_2080964 := by
    simpa [prefixWord, tailWord_2080964, baseEnd_2080964] using wordTrace_append hprefix tailTrace_2080964
  have hstable : (prefixWord ++ tailWord_2080964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080964).length < 2 ^ (prefixWord ++ tailWord_2080964).sum := by decide
  have hdescent : baseEnd_2080964 < baseStart_2080964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080977 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 1, 4, 2]
def baseStart_2080977 : Nat := 118140960795 + 2080977 * 2 ^ 59
def prefixEnd_2080977 : Nat := 4983230072969 + 3 ^ 40 * 2080977 * 2
def baseEnd_2080977 : Nat := 1068541431951409901617267

theorem tailTrace_2080977 : CollatzResearch.WordTrace tailWord_2080977 prefixEnd_2080977 1068541431951409901617267 := by
  unfold tailWord_2080977
  simp only [CollatzResearch.WordTrace]
  refine ⟨75899466581983206421665185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50599644387988804281110123 75899466581983206421665185)
  ·
    refine ⟨56924599936487404816248889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75899466581983206421665185 56924599936487404816248889)
    ·
      refine ⟨42693449952365553612186667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56924599936487404816248889 42693449952365553612186667)
      ·
        refine ⟨64040174928548330418280001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42693449952365553612186667 64040174928548330418280001)
        ·
          refine ⟨48030131196411247813710001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64040174928548330418280001 48030131196411247813710001)
          ·
            refine ⟨36022598397308435860282501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48030131196411247813710001 36022598397308435860282501)
            ·
              refine ⟨6754237199495331723802969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36022598397308435860282501 6754237199495331723802969)
              ·
                refine ⟨5065677899621498792852227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6754237199495331723802969 5065677899621498792852227)
                ·
                  refine ⟨7598516849432248189278341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065677899621498792852227 7598516849432248189278341)
                  ·
                    refine ⟨1424721909268546535489689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7598516849432248189278341 1424721909268546535489689)
                    ·
                      refine ⟨1068541431951409901617267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424721909268546535489689 1068541431951409901617267)
                      ·
                        rfl

theorem cell23_2080977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 4, 2].length) (baseStart_2080977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080977 prefixEnd_2080977 := by exact prefixLift 2080977
  have htrace : WordTrace (prefixWord ++ tailWord_2080977) baseStart_2080977 baseEnd_2080977 := by
    simpa [prefixWord, tailWord_2080977, baseEnd_2080977] using wordTrace_append hprefix tailTrace_2080977
  have hstable : (prefixWord ++ tailWord_2080977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080977).length < 2 ^ (prefixWord ++ tailWord_2080977).sum := by decide
  have hdescent : baseEnd_2080977 < baseStart_2080977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080981 : List Nat := [1, 3, 2, 4, 2, 1, 1, 3, 1, 3, 2]
def baseStart_2080981 : Nat := 118140960795 + 2080981 * 2 ^ 59
def prefixEnd_2080981 : Nat := 4983230072969 + 3 ^ 40 * 2080981 * 2
def baseEnd_2080981 : Nat := 1068543485874027885967249

theorem tailTrace_2080981 : CollatzResearch.WordTrace tailWord_2080981 prefixEnd_2080981 1068543485874027885967249 := by
  unfold tailWord_2080981
  simp only [CollatzResearch.WordTrace]
  refine ⟨75899612473968715104810797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50599741649312476736540531 75899612473968715104810797)
  ·
    refine ⟨28462354677738268164304049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75899612473968715104810797 28462354677738268164304049)
    ·
      refine ⟨21346766008303701123228037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28462354677738268164304049 21346766008303701123228037)
      ·
        refine ⟨4002518626556943960605257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21346766008303701123228037 4002518626556943960605257)
        ·
          refine ⟨3001888969917707970453943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4002518626556943960605257 3001888969917707970453943)
          ·
            refine ⟨4502833454876561955680915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001888969917707970453943 4502833454876561955680915)
            ·
              refine ⟨6754250182314842933521373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502833454876561955680915 6754250182314842933521373)
              ·
                refine ⟨2532843818368066100070515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6754250182314842933521373 2532843818368066100070515)
                ·
                  refine ⟨3799265727552099150105773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532843818368066100070515 3799265727552099150105773)
                  ·
                    refine ⟨1424724647832037181289665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3799265727552099150105773 1424724647832037181289665)
                    ·
                      refine ⟨1068543485874027885967249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424724647832037181289665 1068543485874027885967249)
                      ·
                        rfl

theorem cell23_2080981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_2080981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080981 prefixEnd_2080981 := by exact prefixLift 2080981
  have htrace : WordTrace (prefixWord ++ tailWord_2080981) baseStart_2080981 baseEnd_2080981 := by
    simpa [prefixWord, tailWord_2080981, baseEnd_2080981] using wordTrace_append hprefix tailTrace_2080981
  have hstable : (prefixWord ++ tailWord_2080981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080981).length < 2 ^ (prefixWord ++ tailWord_2080981).sum := by decide
  have hdescent : baseEnd_2080981 < baseStart_2080981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2080983 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 11]
def baseStart_2080983 : Nat := 118140960795 + 2080983 * 2 ^ 59
def prefixEnd_2080983 : Nat := 4983230072969 + 3 ^ 40 * 2080983 * 2
def baseEnd_2080983 : Nat := 118727168092815208682471

theorem tailTrace_2080983 : CollatzResearch.WordTrace tailWord_2080983 prefixEnd_2080983 118727168092815208682471 := by
  unfold tailWord_2080983
  simp only [CollatzResearch.WordTrace]
  refine ⟨75899685419961469446383603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50599790279974312964255735 75899685419961469446383603)
  ·
    refine ⟨113849528129942204169575405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75899685419961469446383603 113849528129942204169575405)
    ·
      refine ⟨42693573048728326563590777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113849528129942204169575405 42693573048728326563590777)
      ·
        refine ⟨32020179786546244922693083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42693573048728326563590777 32020179786546244922693083)
        ·
          refine ⟨48030269679819367384039625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32020179786546244922693083 48030269679819367384039625)
          ·
            refine ⟨36022702259864525538029719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48030269679819367384039625 36022702259864525538029719)
            ·
              refine ⟨54034053389796788307044579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36022702259864525538029719 54034053389796788307044579)
              ·
                refine ⟨81051080084695182460566869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54034053389796788307044579 81051080084695182460566869)
                ·
                  refine ⟨118727168092815208682471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 81051080084695182460566869 118727168092815208682471)
                  ·
                    rfl

theorem cell23_2080983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 11].length) (baseStart_2080983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2080983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2080983 prefixEnd_2080983 := by exact prefixLift 2080983
  have htrace : WordTrace (prefixWord ++ tailWord_2080983) baseStart_2080983 baseEnd_2080983 := by
    simpa [prefixWord, tailWord_2080983, baseEnd_2080983] using wordTrace_append hprefix tailTrace_2080983
  have hstable : (prefixWord ++ tailWord_2080983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2080983).length < 2 ^ (prefixWord ++ tailWord_2080983).sum := by decide
  have hdescent : baseEnd_2080983 < baseStart_2080983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2080983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081000 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 7]
def baseStart_2081000 : Nat := 118140960795 + 2081000 * 2 ^ 59
def prefixEnd_2081000 : Nat := 4983230072969 + 3 ^ 40 * 2081000 * 2
def baseEnd_2081000 : Nat := 118728138000718145736629

theorem tailTrace_2081000 : CollatzResearch.WordTrace tailWord_2081000 prefixEnd_2081000 118728138000718145736629 := by
  unfold tailWord_2081000
  simp only [CollatzResearch.WordTrace]
  refine ⟨37950152730449940674876227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50600203640599920899834969 37950152730449940674876227)
  ·
    refine ⟨56925229095674911012314341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37950152730449940674876227 56925229095674911012314341)
    ·
      refine ⟨10673480455439045814808939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56925229095674911012314341 10673480455439045814808939)
      ·
        refine ⟨16010220683158568722213409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10673480455439045814808939 16010220683158568722213409)
        ·
          refine ⟨12007665512368926541660057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16010220683158568722213409 12007665512368926541660057)
          ·
            refine ⟨9005749134276694906245043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12007665512368926541660057 9005749134276694906245043)
            ·
              refine ⟨13508623701415042359367565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9005749134276694906245043 13508623701415042359367565)
              ·
                refine ⟨5065733888030640884762837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13508623701415042359367565 5065733888030640884762837)
                ·
                  refine ⟨118728138000718145736629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5065733888030640884762837 118728138000718145736629)
                  ·
                    rfl

theorem cell23_2081000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 7].length) (baseStart_2081000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081000 prefixEnd_2081000 := by exact prefixLift 2081000
  have htrace : WordTrace (prefixWord ++ tailWord_2081000) baseStart_2081000 baseEnd_2081000 := by
    simpa [prefixWord, tailWord_2081000, baseEnd_2081000] using wordTrace_append hprefix tailTrace_2081000
  have hstable : (prefixWord ++ tailWord_2081000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081000).length < 2 ^ (prefixWord ++ tailWord_2081000).sum := by decide
  have hdescent : baseEnd_2081000 < baseStart_2081000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081011 : List Nat := [1, 1, 1, 2, 2, 4, 5, 1, 2, 2, 2]
def baseStart_2081011 : Nat := 118140960795 + 2081011 * 2 ^ 59
def prefixEnd_2081011 : Nat := 4983230072969 + 3 ^ 40 * 2081011 * 2
def baseEnd_2081011 : Nat := 1068558890293662768592111

theorem tailTrace_2081011 : CollatzResearch.WordTrace tailWord_2081011 prefixEnd_2081011 1068558890293662768592111 := by
  unfold tailWord_2081011
  simp only [CollatzResearch.WordTrace]
  refine ⟨75900706663860030228402887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50600471109240020152268591 75900706663860030228402887)
  ·
    refine ⟨113851059995790045342604331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75900706663860030228402887 113851059995790045342604331)
    ·
      refine ⟨170776589993685068013906497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113851059995790045342604331 170776589993685068013906497)
      ·
        refine ⟨128082442495263801010429873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170776589993685068013906497 128082442495263801010429873)
        ·
          refine ⟨96061831871447850757822405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128082442495263801010429873 96061831871447850757822405)
          ·
            refine ⟨18011593475896472017091701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96061831871447850757822405 18011593475896472017091701)
            ·
              refine ⟨1688586888365294251602347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18011593475896472017091701 1688586888365294251602347)
              ·
                refine ⟨2532880332547941377403521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688586888365294251602347 2532880332547941377403521)
                ·
                  refine ⟨1899660249410956033052641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2532880332547941377403521 1899660249410956033052641)
                  ·
                    refine ⟨1424745187058217024789481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1899660249410956033052641 1424745187058217024789481)
                    ·
                      refine ⟨1068558890293662768592111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424745187058217024789481 1068558890293662768592111)
                      ·
                        rfl

theorem cell23_2081011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 2, 2, 2].length) (baseStart_2081011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081011 prefixEnd_2081011 := by exact prefixLift 2081011
  have htrace : WordTrace (prefixWord ++ tailWord_2081011) baseStart_2081011 baseEnd_2081011 := by
    simpa [prefixWord, tailWord_2081011, baseEnd_2081011] using wordTrace_append hprefix tailTrace_2081011
  have hstable : (prefixWord ++ tailWord_2081011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081011).length < 2 ^ (prefixWord ++ tailWord_2081011).sum := by decide
  have hdescent : baseEnd_2081011 < baseStart_2081011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081047 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 2, 5]
def baseStart_2081047 : Nat := 118140960795 + 2081047 * 2 ^ 59
def prefixEnd_2081047 : Nat := 4983230072969 + 3 ^ 40 * 2081047 * 2
def baseEnd_2081047 : Nat := 356192458532408209247315

theorem tailTrace_2081047 : CollatzResearch.WordTrace tailWord_2081047 prefixEnd_2081047 356192458532408209247315 := by
  unfold tailWord_2081047
  simp only [CollatzResearch.WordTrace]
  refine ⟨75902019691729608376713395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50601346461153072251142263 75902019691729608376713395)
  ·
    refine ⟨113853029537594412565070093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75902019691729608376713395 113853029537594412565070093)
    ·
      refine ⟨42694886076597904711901285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113853029537594412565070093 42694886076597904711901285)
      ·
        refine ⟨8005291139362107133481491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42694886076597904711901285 8005291139362107133481491)
        ·
          refine ⟨12007936709043160700222237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8005291139362107133481491 12007936709043160700222237)
          ·
            refine ⟨4502976265891185262583339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12007936709043160700222237 4502976265891185262583339)
            ·
              refine ⟨6754464398836777893875009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502976265891185262583339 6754464398836777893875009)
              ·
                refine ⟨5065848299127583420406257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6754464398836777893875009 5065848299127583420406257)
                ·
                  refine ⟨3799386224345687565304693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5065848299127583420406257 3799386224345687565304693)
                  ·
                    refine ⟨356192458532408209247315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3799386224345687565304693 356192458532408209247315)
                    ·
                      rfl

theorem cell23_2081047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_2081047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081047 prefixEnd_2081047 := by exact prefixLift 2081047
  have htrace : WordTrace (prefixWord ++ tailWord_2081047) baseStart_2081047 baseEnd_2081047 := by
    simpa [prefixWord, tailWord_2081047, baseEnd_2081047] using wordTrace_append hprefix tailTrace_2081047
  have hstable : (prefixWord ++ tailWord_2081047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081047).length < 2 ^ (prefixWord ++ tailWord_2081047).sum := by decide
  have hdescent : baseEnd_2081047 < baseStart_2081047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081077 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 5, 4]
def baseStart_2081077 : Nat := 118140960795 + 2081077 * 2 ^ 59
def prefixEnd_2081077 : Nat := 4983230072969 + 3 ^ 40 * 2081077 * 2
def baseEnd_2081077 : Nat := 356197593338953170122269

theorem tailTrace_2081077 : CollatzResearch.WordTrace tailWord_2081077 prefixEnd_2081077 356197593338953170122269 := by
  unfold tailWord_2081077
  simp only [CollatzResearch.WordTrace]
  refine ⟨75903113881620923500305485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50602075921080615666870323 75903113881620923500305485)
  ·
    refine ⟨28463667705607846312614557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75903113881620923500305485 28463667705607846312614557)
    ·
      refine ⟨10673875389602942367230459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28463667705607846312614557 10673875389602942367230459)
      ·
        refine ⟨16010813084404413550845689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10673875389602942367230459 16010813084404413550845689)
        ·
          refine ⟨12008109813303310163134267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16010813084404413550845689 12008109813303310163134267)
          ·
            refine ⟨18012164719954965244701401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12008109813303310163134267 18012164719954965244701401)
            ·
              refine ⟨13509123539966223933526051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18012164719954965244701401 13509123539966223933526051)
              ·
                refine ⟨20263685309949335900289077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13509123539966223933526051 20263685309949335900289077)
                ·
                  refine ⟨1899720497807750240652101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20263685309949335900289077 1899720497807750240652101)
                  ·
                    refine ⟨356197593338953170122269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1899720497807750240652101 356197593338953170122269)
                    ·
                      rfl

theorem cell23_2081077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_2081077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081077 prefixEnd_2081077 := by exact prefixLift 2081077
  have htrace : WordTrace (prefixWord ++ tailWord_2081077) baseStart_2081077 baseEnd_2081077 := by
    simpa [prefixWord, tailWord_2081077, baseEnd_2081077] using wordTrace_append hprefix tailTrace_2081077
  have hstable : (prefixWord ++ tailWord_2081077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081077).length < 2 ^ (prefixWord ++ tailWord_2081077).sum := by decide
  have hdescent : baseEnd_2081077 < baseStart_2081077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081080 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_2081080 : Nat := 118140960795 + 2081080 * 2 ^ 59
def prefixEnd_2081080 : Nat := 4983230072969 + 3 ^ 40 * 2081080 * 2
def baseEnd_2081080 : Nat := 1068594320458822998629293

theorem tailTrace_2081080 : CollatzResearch.WordTrace tailWord_2081080 prefixEnd_2081080 1068594320458822998629293 := by
  unfold tailWord_2081080
  simp only [CollatzResearch.WordTrace]
  refine ⟨37951611650305027506332347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50602148867073370008443129 37951611650305027506332347)
  ·
    refine ⟨56927417475457541259498521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37951611650305027506332347 56927417475457541259498521)
    ·
      refine ⟨42695563106593155944623891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56927417475457541259498521 42695563106593155944623891)
      ·
        refine ⟨64043344659889733916935837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42695563106593155944623891 64043344659889733916935837)
        ·
          refine ⟨24016254247458650218850939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64043344659889733916935837 24016254247458650218850939)
          ·
            refine ⟨36024381371187975328276409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24016254247458650218850939 36024381371187975328276409)
            ·
              refine ⟨27018286028390981496207307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36024381371187975328276409 27018286028390981496207307)
              ·
                refine ⟨40527429042586472244310961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27018286028390981496207307 40527429042586472244310961)
                ·
                  refine ⟨30395571781939854183233221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40527429042586472244310961 30395571781939854183233221)
                  ·
                    refine ⟨5699169709113722659356229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30395571781939854183233221 5699169709113722659356229)
                    ·
                      refine ⟨1068594320458822998629293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5699169709113722659356229 1068594320458822998629293)
                      ·
                        rfl

theorem cell23_2081080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_2081080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081080 prefixEnd_2081080 := by exact prefixLift 2081080
  have htrace : WordTrace (prefixWord ++ tailWord_2081080) baseStart_2081080 baseEnd_2081080 := by
    simpa [prefixWord, tailWord_2081080, baseEnd_2081080] using wordTrace_append hprefix tailTrace_2081080
  have hstable : (prefixWord ++ tailWord_2081080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081080).length < 2 ^ (prefixWord ++ tailWord_2081080).sum := by decide
  have hdescent : baseEnd_2081080 < baseStart_2081080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081137 : List Nat := [1, 2, 2, 2, 1, 2, 1, 6, 1, 5]
def baseStart_2081137 : Nat := 118140960795 + 2081137 * 2 ^ 59
def prefixEnd_2081137 : Nat := 4983230072969 + 3 ^ 40 * 2081137 * 2
def baseEnd_2081137 : Nat := 356207862952043091872177

theorem tailTrace_2081137 : CollatzResearch.WordTrace tailWord_2081137 prefixEnd_2081137 356207862952043091872177 := by
  unfold tailWord_2081137
  simp only [CollatzResearch.WordTrace]
  refine ⟨75905302261403553747489665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50603534840935702498326443 75905302261403553747489665)
  ·
    refine ⟨56928976696052665310617249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75905302261403553747489665 56928976696052665310617249)
    ·
      refine ⟨42696732522039498982962937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56928976696052665310617249 42696732522039498982962937)
      ·
        refine ⟨32022549391529624237222203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42696732522039498982962937 32022549391529624237222203)
        ·
          refine ⟨48033824087294436355833305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32022549391529624237222203 48033824087294436355833305)
          ·
            refine ⟨36025368065470827266874979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48033824087294436355833305 36025368065470827266874979)
            ·
              refine ⟨54038052098206240900312469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36025368065470827266874979 54038052098206240900312469)
              ·
                refine ⟨2533033692103417542202147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54038052098206240900312469 2533033692103417542202147)
                ·
                  refine ⟨3799550538155126313303221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533033692103417542202147 3799550538155126313303221)
                  ·
                    refine ⟨356207862952043091872177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3799550538155126313303221 356207862952043091872177)
                    ·
                      rfl

theorem cell23_2081137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_2081137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081137 prefixEnd_2081137 := by exact prefixLift 2081137
  have htrace : WordTrace (prefixWord ++ tailWord_2081137) baseStart_2081137 baseEnd_2081137 := by
    simpa [prefixWord, tailWord_2081137, baseEnd_2081137] using wordTrace_append hprefix tailTrace_2081137
  have hstable : (prefixWord ++ tailWord_2081137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081137).length < 2 ^ (prefixWord ++ tailWord_2081137).sum := by decide
  have hdescent : baseEnd_2081137 < baseStart_2081137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081177 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 5]
def baseStart_2081177 : Nat := 118140960795 + 2081177 * 2 ^ 59
def prefixEnd_2081177 : Nat := 4983230072969 + 3 ^ 40 * 2081177 * 2
def baseEnd_2081177 : Nat := 1068644128082309119116347

theorem tailTrace_2081177 : CollatzResearch.WordTrace tailWord_2081177 prefixEnd_2081177 1068644128082309119116347 := by
  unfold tailWord_2081177
  simp only [CollatzResearch.WordTrace]
  refine ⟨75906761181258640578945785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50604507454172427052630523 75906761181258640578945785)
  ·
    refine ⟨56930070885943980434209339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75906761181258640578945785 56930070885943980434209339)
    ·
      refine ⟨85395106328915970651314009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56930070885943980434209339 85395106328915970651314009)
      ·
        refine ⟨64046329746686977988485507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85395106328915970651314009 64046329746686977988485507)
        ·
          refine ⟨96069494620030466982728261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64046329746686977988485507 96069494620030466982728261)
          ·
            refine ⟨18013030241255712559261549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96069494620030466982728261 18013030241255712559261549)
            ·
              refine ⟨6754886340470892209723081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18013030241255712559261549 6754886340470892209723081)
              ·
                refine ⟨5066164755353169157292311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6754886340470892209723081 5066164755353169157292311)
                ·
                  refine ⟨7599247133029753735938467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5066164755353169157292311 7599247133029753735938467)
                  ·
                    refine ⟨11398870699544630603907701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7599247133029753735938467 11398870699544630603907701)
                    ·
                      refine ⟨1068644128082309119116347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11398870699544630603907701 1068644128082309119116347)
                      ·
                        rfl

theorem cell23_2081177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_2081177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081177 prefixEnd_2081177 := by exact prefixLift 2081177
  have htrace : WordTrace (prefixWord ++ tailWord_2081177) baseStart_2081177 baseEnd_2081177 := by
    simpa [prefixWord, tailWord_2081177, baseEnd_2081177] using wordTrace_append hprefix tailTrace_2081177
  have hstable : (prefixWord ++ tailWord_2081177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081177).length < 2 ^ (prefixWord ++ tailWord_2081177).sum := by decide
  have hdescent : baseEnd_2081177 < baseStart_2081177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081184 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 1, 6]
def baseStart_2081184 : Nat := 118140960795 + 2081184 * 2 ^ 59
def prefixEnd_2081184 : Nat := 4983230072969 + 3 ^ 40 * 2081184 * 2
def baseEnd_2081184 : Nat := 356215907482296863909605

theorem tailTrace_2081184 : CollatzResearch.WordTrace tailWord_2081184 prefixEnd_2081184 356215907482296863909605 := by
  unfold tailWord_2081184
  simp only [CollatzResearch.WordTrace]
  refine ⟨37953508246116640387225303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50604677661488853849633737 37953508246116640387225303)
  ·
    refine ⟨56930262369174960580837955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37953508246116640387225303 56930262369174960580837955)
    ·
      refine ⟨85395393553762440871256933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56930262369174960580837955 85395393553762440871256933)
      ·
        refine ⟨16011636291330457663360675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85395393553762440871256933 16011636291330457663360675)
        ·
          refine ⟨24017454436995686495041013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16011636291330457663360675 24017454436995686495041013)
          ·
            refine ⟨2251636353468345608910095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24017454436995686495041013 2251636353468345608910095)
            ·
              refine ⟨3377454530202518413365143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2251636353468345608910095 3377454530202518413365143)
              ·
                refine ⟨5066181795303777620047715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3377454530202518413365143 5066181795303777620047715)
                ·
                  refine ⟨7599272692955666430071573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5066181795303777620047715 7599272692955666430071573)
                  ·
                    refine ⟨356215907482296863909605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7599272692955666430071573 356215907482296863909605)
                    ·
                      rfl

theorem cell23_2081184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 6].length) (baseStart_2081184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081184 prefixEnd_2081184 := by exact prefixLift 2081184
  have htrace : WordTrace (prefixWord ++ tailWord_2081184) baseStart_2081184 baseEnd_2081184 := by
    simpa [prefixWord, tailWord_2081184, baseEnd_2081184] using wordTrace_append hprefix tailTrace_2081184
  have hstable : (prefixWord ++ tailWord_2081184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081184).length < 2 ^ (prefixWord ++ tailWord_2081184).sum := by decide
  have hdescent : baseEnd_2081184 < baseStart_2081184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081187 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 6]
def baseStart_2081187 : Nat := 118140960795 + 2081187 * 2 ^ 59
def prefixEnd_2081187 : Nat := 4983230072969 + 3 ^ 40 * 2081187 * 2
def baseEnd_2081187 : Nat := 1068649262888854079991301

theorem tailTrace_2081187 : CollatzResearch.WordTrace tailWord_2081187 prefixEnd_2081187 1068649262888854079991301 := by
  unfold tailWord_2081187
  simp only [CollatzResearch.WordTrace]
  refine ⟨75907125911222412286809815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50604750607481608191206543 75907125911222412286809815)
  ·
    refine ⟨113860688866833618430214723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75907125911222412286809815 113860688866833618430214723)
    ·
      refine ⟨170791033300250427645322085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113860688866833618430214723 170791033300250427645322085)
      ·
        refine ⟨32023318743796955183497891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170791033300250427645322085 32023318743796955183497891)
        ·
          refine ⟨48034978115695432775246837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32023318743796955183497891 48034978115695432775246837)
          ·
            refine ⟨4503279198346446822679391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48034978115695432775246837 4503279198346446822679391)
            ·
              refine ⟨6754918797519670234019087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503279198346446822679391 6754918797519670234019087)
              ·
                refine ⟨10132378196279505351028631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6754918797519670234019087 10132378196279505351028631)
                ·
                  refine ⟨15198567294419258026542947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10132378196279505351028631 15198567294419258026542947)
                  ·
                    refine ⟨22797850941628887039814421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15198567294419258026542947 22797850941628887039814421)
                    ·
                      refine ⟨1068649262888854079991301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22797850941628887039814421 1068649262888854079991301)
                      ·
                        rfl

theorem cell23_2081187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_2081187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081187 prefixEnd_2081187 := by exact prefixLift 2081187
  have htrace : WordTrace (prefixWord ++ tailWord_2081187) baseStart_2081187 baseEnd_2081187 := by
    simpa [prefixWord, tailWord_2081187, baseEnd_2081187] using wordTrace_append hprefix tailTrace_2081187
  have hstable : (prefixWord ++ tailWord_2081187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081187).length < 2 ^ (prefixWord ++ tailWord_2081187).sum := by decide
  have hdescent : baseEnd_2081187 < baseStart_2081187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081191 : List Nat := [1, 1, 6, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_2081191 : Nat := 118140960795 + 2081191 * 2 ^ 59
def prefixEnd_2081191 : Nat := 4983230072969 + 3 ^ 40 * 2081191 * 2
def baseEnd_2081191 : Nat := 1068651316811472064341283

theorem tailTrace_2081191 : CollatzResearch.WordTrace tailWord_2081191 prefixEnd_2081191 1068651316811472064341283 := by
  unfold tailWord_2081191
  simp only [CollatzResearch.WordTrace]
  refine ⟨75907271803207920969955427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50604847868805280646636951 75907271803207920969955427)
  ·
    refine ⟨113860907704811881454933141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75907271803207920969955427 113860907704811881454933141)
    ·
      refine ⟨5337230048663056943199991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113860907704811881454933141 5337230048663056943199991)
      ·
        refine ⟨8005845072994585414799987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5337230048663056943199991 8005845072994585414799987)
        ·
          refine ⟨12008767609491878122199981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8005845072994585414799987 12008767609491878122199981)
          ·
            refine ⟨4503287853559454295824993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12008767609491878122199981 4503287853559454295824993)
            ·
              refine ⟨3377465890169590721868745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4503287853559454295824993 3377465890169590721868745)
              ·
                refine ⟨2533099417627193041401559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3377465890169590721868745 2533099417627193041401559)
                ·
                  refine ⟨3799649126440789562102339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533099417627193041401559 3799649126440789562102339)
                  ·
                    refine ⟨5699473689661184343153509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3799649126440789562102339 5699473689661184343153509)
                    ·
                      refine ⟨1068651316811472064341283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5699473689661184343153509 1068651316811472064341283)
                      ·
                        rfl

theorem cell23_2081191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_2081191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081191 prefixEnd_2081191 := by exact prefixLift 2081191
  have htrace : WordTrace (prefixWord ++ tailWord_2081191) baseStart_2081191 baseEnd_2081191 := by
    simpa [prefixWord, tailWord_2081191, baseEnd_2081191] using wordTrace_append hprefix tailTrace_2081191
  have hstable : (prefixWord ++ tailWord_2081191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081191).length < 2 ^ (prefixWord ++ tailWord_2081191).sum := by decide
  have hdescent : baseEnd_2081191 < baseStart_2081191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081241 : List Nat := [1, 2, 1, 2, 4, 1, 3, 3, 2, 1, 3]
def baseStart_2081241 : Nat := 118140960795 + 2081241 * 2 ^ 59
def prefixEnd_2081241 : Nat := 4983230072969 + 3 ^ 40 * 2081241 * 2
def baseEnd_2081241 : Nat := 1068676990844196868716053

theorem tailTrace_2081241 : CollatzResearch.WordTrace tailWord_2081241 prefixEnd_2081241 1068676990844196868716053 := by
  unfold tailWord_2081241
  simp only [CollatzResearch.WordTrace]
  refine ⟨75909095453026779509275577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50606063635351186339517051 75909095453026779509275577)
  ·
    refine ⟨56931821589770084631956683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75909095453026779509275577 56931821589770084631956683)
    ·
      refine ⟨85397732384655126947935025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56931821589770084631956683 85397732384655126947935025)
      ·
        refine ⟨64048299288491345210951269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85397732384655126947935025 64048299288491345210951269)
        ·
          refine ⟨12009056116592127227053363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64048299288491345210951269 12009056116592127227053363)
          ·
            refine ⟨18013584174888190840580045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12009056116592127227053363 18013584174888190840580045)
            ·
              refine ⟨6755094065583071565217517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18013584174888190840580045 6755094065583071565217517)
              ·
                refine ⟨2533160274593651836956569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6755094065583071565217517 2533160274593651836956569)
                ·
                  refine ⟨1899870205945238877717427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2533160274593651836956569 1899870205945238877717427)
                  ·
                    refine ⟨2849805308917858316576141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1899870205945238877717427 2849805308917858316576141)
                    ·
                      refine ⟨1068676990844196868716053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2849805308917858316576141 1068676990844196868716053)
                      ·
                        rfl

theorem cell23_2081241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_2081241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081241 prefixEnd_2081241 := by exact prefixLift 2081241
  have htrace : WordTrace (prefixWord ++ tailWord_2081241) baseStart_2081241 baseEnd_2081241 := by
    simpa [prefixWord, tailWord_2081241, baseEnd_2081241] using wordTrace_append hprefix tailTrace_2081241
  have hstable : (prefixWord ++ tailWord_2081241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081241).length < 2 ^ (prefixWord ++ tailWord_2081241).sum := by decide
  have hdescent : baseEnd_2081241 < baseStart_2081241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081267 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 5]
def baseStart_2081267 : Nat := 118140960795 + 2081267 * 2 ^ 59
def prefixEnd_2081267 : Nat := 4983230072969 + 3 ^ 40 * 2081267 * 2
def baseEnd_2081267 : Nat := 1068690341341213766990933

theorem tailTrace_2081267 : CollatzResearch.WordTrace tailWord_2081267 prefixEnd_2081267 1068690341341213766990933 := by
  unfold tailWord_2081267
  simp only [CollatzResearch.WordTrace]
  refine ⟨75910043750932585949722055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50606695833955057299814703 75910043750932585949722055)
  ·
    refine ⟨113865065626398878924583083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75910043750932585949722055 113865065626398878924583083)
    ·
      refine ⟨170797598439598318386874625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113865065626398878924583083 170797598439598318386874625)
      ·
        refine ⟨128098198829698738790155969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170797598439598318386874625 128098198829698738790155969)
        ·
          refine ⟨96073649122274054092616977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128098198829698738790155969 96073649122274054092616977)
          ·
            refine ⟨72055236841705540569462733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96073649122274054092616977 72055236841705540569462733)
            ·
              refine ⟨27020713815639577713548525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72055236841705540569462733 27020713815639577713548525)
              ·
                refine ⟨10132767680864841642580697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27020713815639577713548525 10132767680864841642580697)
                ·
                  refine ⟨7599575760648631231935523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10132767680864841642580697 7599575760648631231935523)
                  ·
                    refine ⟨11399363640972946847903285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7599575760648631231935523 11399363640972946847903285)
                    ·
                      refine ⟨1068690341341213766990933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11399363640972946847903285 1068690341341213766990933)
                      ·
                        rfl

theorem cell23_2081267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_2081267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081267 prefixEnd_2081267 := by exact prefixLift 2081267
  have htrace : WordTrace (prefixWord ++ tailWord_2081267) baseStart_2081267 baseEnd_2081267 := by
    simpa [prefixWord, tailWord_2081267, baseEnd_2081267] using wordTrace_append hprefix tailTrace_2081267
  have hstable : (prefixWord ++ tailWord_2081267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081267).length < 2 ^ (prefixWord ++ tailWord_2081267).sum := by decide
  have hdescent : baseEnd_2081267 < baseStart_2081267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081294 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_2081294 : Nat := 118140960795 + 2081294 * 2 ^ 59
def prefixEnd_2081294 : Nat := 4983230072969 + 3 ^ 40 * 2081294 * 2
def baseEnd_2081294 : Nat := 1068704205318885161353309

theorem tailTrace_2081294 : CollatzResearch.WordTrace tailWord_2081294 prefixEnd_2081294 1068704205318885161353309 := by
  unfold tailWord_2081294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9488878565229346195119367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50607352347889846373969957 9488878565229346195119367)
  ·
    refine ⟨14233317847844019292679051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9488878565229346195119367 14233317847844019292679051)
    ·
      refine ⟨21349976771766028939018577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14233317847844019292679051 21349976771766028939018577)
      ·
        refine ⟨16012482578824521704263933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21349976771766028939018577 16012482578824521704263933)
        ·
          refine ⟨6004680967059195639098975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16012482578824521704263933 6004680967059195639098975)
          ·
            refine ⟨9007021450588793458648463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6004680967059195639098975 9007021450588793458648463)
            ·
              refine ⟨13510532175883190187972695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9007021450588793458648463 13510532175883190187972695)
              ·
                refine ⟨20265798263824785281959043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13510532175883190187972695 20265798263824785281959043)
                ·
                  refine ⟨30398697395737177922938565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20265798263824785281959043 30398697395737177922938565)
                  ·
                    refine ⟨5699755761700720860550981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30398697395737177922938565 5699755761700720860550981)
                    ·
                      refine ⟨1068704205318885161353309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5699755761700720860550981 1068704205318885161353309)
                      ·
                        rfl

theorem cell23_2081294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_2081294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081294 prefixEnd_2081294 := by exact prefixLift 2081294
  have htrace : WordTrace (prefixWord ++ tailWord_2081294) baseStart_2081294 baseEnd_2081294 := by
    simpa [prefixWord, tailWord_2081294, baseEnd_2081294] using wordTrace_append hprefix tailTrace_2081294
  have hstable : (prefixWord ++ tailWord_2081294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081294).length < 2 ^ (prefixWord ++ tailWord_2081294).sum := by decide
  have hdescent : baseEnd_2081294 < baseStart_2081294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081304 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 7]
def baseStart_2081304 : Nat := 118140960795 + 2081304 * 2 ^ 59
def prefixEnd_2081304 : Nat := 4983230072969 + 3 ^ 40 * 2081304 * 2
def baseEnd_2081304 : Nat := 118745482236158902469807

theorem tailTrace_2081304 : CollatzResearch.WordTrace tailWord_2081304 prefixEnd_2081304 118745482236158902469807 := by
  unfold tailWord_2081304
  simp only [CollatzResearch.WordTrace]
  refine ⟨37955696625899270634409483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50607595501199027512545977 37955696625899270634409483)
  ·
    refine ⟨56933544938848905951614225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37955696625899270634409483 56933544938848905951614225)
    ·
      refine ⟨42700158704136679463710669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56933544938848905951614225 42700158704136679463710669)
      ·
        refine ⟨16012559514051254798891501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42700158704136679463710669 16012559514051254798891501)
        ·
          refine ⟨6004709817769220549584313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16012559514051254798891501 6004709817769220549584313)
          ·
            refine ⟨4503532363326915412188235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6004709817769220549584313 4503532363326915412188235)
            ·
              refine ⟨6755298544990373118282353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503532363326915412188235 6755298544990373118282353)
              ·
                refine ⟨5066473908742779838711765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6755298544990373118282353 5066473908742779838711765)
                ·
                  refine ⟨118745482236158902469807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5066473908742779838711765 118745482236158902469807)
                  ·
                    rfl

theorem cell23_2081304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 7].length) (baseStart_2081304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081304 prefixEnd_2081304 := by exact prefixLift 2081304
  have htrace : WordTrace (prefixWord ++ tailWord_2081304) baseStart_2081304 baseEnd_2081304 := by
    simpa [prefixWord, tailWord_2081304, baseEnd_2081304] using wordTrace_append hprefix tailTrace_2081304
  have hstable : (prefixWord ++ tailWord_2081304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081304).length < 2 ^ (prefixWord ++ tailWord_2081304).sum := by decide
  have hdescent : baseEnd_2081304 < baseStart_2081304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081314 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_2081314 : Nat := 118140960795 + 2081314 * 2 ^ 59
def prefixEnd_2081314 : Nat := 4983230072969 + 3 ^ 40 * 2081314 * 2
def baseEnd_2081314 : Nat := 1068714474931975083103217

theorem tailTrace_2081314 : CollatzResearch.WordTrace tailWord_2081314 prefixEnd_2081314 1068714474931975083103217 := by
  unfold tailWord_2081314
  simp only [CollatzResearch.WordTrace]
  refine ⟨18977939495440578244170749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50607838654508208651121997 18977939495440578244170749)
  ·
    refine ⟨7116727310790216841564031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18977939495440578244170749 7116727310790216841564031)
    ·
      refine ⟨10675090966185325262346047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7116727310790216841564031 10675090966185325262346047)
      ·
        refine ⟨16012636449277987893519071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10675090966185325262346047 16012636449277987893519071)
        ·
          refine ⟨24018954673916981840278607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16012636449277987893519071 24018954673916981840278607)
          ·
            refine ⟨36028432010875472760417911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24018954673916981840278607 36028432010875472760417911)
            ·
              refine ⟨54042648016313209140626867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36028432010875472760417911 54042648016313209140626867)
              ·
                refine ⟨81063972024469813710940301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54042648016313209140626867 81063972024469813710940301)
                ·
                  refine ⟨30398989509176180141602613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81063972024469813710940301 30398989509176180141602613)
                  ·
                    refine ⟨2849905266485266888275245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30398989509176180141602613 2849905266485266888275245)
                    ·
                      refine ⟨1068714474931975083103217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2849905266485266888275245 1068714474931975083103217)
                      ·
                        rfl

theorem cell23_2081314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_2081314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081314 prefixEnd_2081314 := by exact prefixLift 2081314
  have htrace : WordTrace (prefixWord ++ tailWord_2081314) baseStart_2081314 baseEnd_2081314 := by
    simpa [prefixWord, tailWord_2081314, baseEnd_2081314] using wordTrace_append hprefix tailTrace_2081314
  have hstable : (prefixWord ++ tailWord_2081314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081314).length < 2 ^ (prefixWord ++ tailWord_2081314).sum := by decide
  have hdescent : baseEnd_2081314 < baseStart_2081314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081319 : List Nat := [1, 1, 7, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_2081319 : Nat := 118140960795 + 2081319 * 2 ^ 59
def prefixEnd_2081319 : Nat := 4983230072969 + 3 ^ 40 * 2081319 * 2
def baseEnd_2081319 : Nat := 1068717042335247563540695

theorem tailTrace_2081319 : CollatzResearch.WordTrace tailWord_2081319 prefixEnd_2081319 1068717042335247563540695 := by
  unfold tailWord_2081319
  simp only [CollatzResearch.WordTrace]
  refine ⟨75911940346744198830615011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50607960231162799220410007 75911940346744198830615011)
  ·
    refine ⟨113867910520116298245922517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75911940346744198830615011 113867910520116298245922517)
    ·
      refine ⟨2668779152815225740138809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 113867910520116298245922517 2668779152815225740138809)
      ·
        refine ⟨2001584364611419305104107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2668779152815225740138809 2001584364611419305104107)
        ·
          refine ⟨3002376546917128957656161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001584364611419305104107 3002376546917128957656161)
          ·
            refine ⟨2251782410187846718242121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3002376546917128957656161 2251782410187846718242121)
            ·
              refine ⟨1688836807640885038681591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2251782410187846718242121 1688836807640885038681591)
              ·
                refine ⟨2533255211461327558022387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688836807640885038681591 2533255211461327558022387)
                ·
                  refine ⟨3799882817191991337033581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533255211461327558022387 3799882817191991337033581)
                  ·
                    refine ⟨1424956056446996751387593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3799882817191991337033581 1424956056446996751387593)
                    ·
                      refine ⟨1068717042335247563540695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424956056446996751387593 1068717042335247563540695)
                      ·
                        rfl

theorem cell23_2081319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_2081319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081319 prefixEnd_2081319 := by exact prefixLift 2081319
  have htrace : WordTrace (prefixWord ++ tailWord_2081319) baseStart_2081319 baseEnd_2081319 := by
    simpa [prefixWord, tailWord_2081319, baseEnd_2081319] using wordTrace_append hprefix tailTrace_2081319
  have hstable : (prefixWord ++ tailWord_2081319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081319).length < 2 ^ (prefixWord ++ tailWord_2081319).sum := by decide
  have hdescent : baseEnd_2081319 < baseStart_2081319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081332 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_2081332 : Nat := 118140960795 + 2081332 * 2 ^ 59
def prefixEnd_2081332 : Nat := 4983230072969 + 3 ^ 40 * 2081332 * 2
def baseEnd_2081332 : Nat := 1068723717583756012678135

theorem tailTrace_2081332 : CollatzResearch.WordTrace tailWord_2081332 prefixEnd_2081332 1068723717583756012678135 := by
  unfold tailWord_2081332
  simp only [CollatzResearch.WordTrace]
  refine ⟨37956207247848551025419125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50608276330464734700558833 37956207247848551025419125)
  ·
    refine ⟨3558394429485801658633043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37956207247848551025419125 3558394429485801658633043)
    ·
      refine ⟨5337591644228702487949565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3558394429485801658633043 5337591644228702487949565)
      ·
        refine ⟨2001596866585763432981087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5337591644228702487949565 2001596866585763432981087)
        ·
          refine ⟨3002395299878645149471631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001596866585763432981087 3002395299878645149471631)
          ·
            refine ⟨4503592949817967724207447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002395299878645149471631 4503592949817967724207447)
            ·
              refine ⟨6755389424726951586311171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503592949817967724207447 6755389424726951586311171)
              ·
                refine ⟨10133084137090427379466757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6755389424726951586311171 10133084137090427379466757)
                ·
                  refine ⟨1899953275704455133650017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10133084137090427379466757 1899953275704455133650017)
                  ·
                    refine ⟨1424964956778341350237513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1899953275704455133650017 1424964956778341350237513)
                    ·
                      refine ⟨1068723717583756012678135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1424964956778341350237513 1068723717583756012678135)
                      ·
                        rfl

theorem cell23_2081332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_2081332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081332 prefixEnd_2081332 := by exact prefixLift 2081332
  have htrace : WordTrace (prefixWord ++ tailWord_2081332) baseStart_2081332 baseEnd_2081332 := by
    simpa [prefixWord, tailWord_2081332, baseEnd_2081332] using wordTrace_append hprefix tailTrace_2081332
  have hstable : (prefixWord ++ tailWord_2081332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081332).length < 2 ^ (prefixWord ++ tailWord_2081332).sum := by decide
  have hdescent : baseEnd_2081332 < baseStart_2081332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081354 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_2081354 : Nat := 118140960795 + 2081354 * 2 ^ 59
def prefixEnd_2081354 : Nat := 4983230072969 + 3 ^ 40 * 2081354 * 2
def baseEnd_2081354 : Nat := 1068735014158154926603033

theorem tailTrace_2081354 : CollatzResearch.WordTrace tailWord_2081354 prefixEnd_2081354 1068735014158154926603033 := by
  unfold tailWord_2081354
  simp only [CollatzResearch.WordTrace]
  refine ⟨18978304225404349952034779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50608811267744933205426077 18978304225404349952034779)
  ·
    refine ⟨28467456338106524928052169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18978304225404349952034779 28467456338106524928052169)
    ·
      refine ⟨21350592253579893696039127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28467456338106524928052169 21350592253579893696039127)
      ·
        refine ⟨32025888380369840544058691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21350592253579893696039127 32025888380369840544058691)
        ·
          refine ⟨48038832570554760816088037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32025888380369840544058691 48038832570554760816088037)
          ·
            refine ⟨9007281106979017653016507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48038832570554760816088037 9007281106979017653016507)
            ·
              refine ⟨13510921660468526479524761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9007281106979017653016507 13510921660468526479524761)
              ·
                refine ⟨10133191245351394859643571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13510921660468526479524761 10133191245351394859643571)
                ·
                  refine ⟨15199786868027092289465357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10133191245351394859643571 15199786868027092289465357)
                  ·
                    refine ⟨5699920075510159608549509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15199786868027092289465357 5699920075510159608549509)
                    ·
                      refine ⟨1068735014158154926603033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5699920075510159608549509 1068735014158154926603033)
                      ·
                        rfl

theorem cell23_2081354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_2081354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081354 prefixEnd_2081354 := by exact prefixLift 2081354
  have htrace : WordTrace (prefixWord ++ tailWord_2081354) baseStart_2081354 baseEnd_2081354 := by
    simpa [prefixWord, tailWord_2081354, baseEnd_2081354] using wordTrace_append hprefix tailTrace_2081354
  have hstable : (prefixWord ++ tailWord_2081354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081354).length < 2 ^ (prefixWord ++ tailWord_2081354).sum := by decide
  have hdescent : baseEnd_2081354 < baseStart_2081354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081411 : List Nat := [1, 1, 1, 3, 3, 1, 6, 1, 6]
def baseStart_2081411 : Nat := 118140960795 + 2081411 * 2 ^ 59
def prefixEnd_2081411 : Nat := 4983230072969 + 3 ^ 40 * 2081411 * 2
def baseEnd_2081411 : Nat := 118751586950606800398919

theorem tailTrace_2081411 : CollatzResearch.WordTrace tailWord_2081411 prefixEnd_2081411 118751586950606800398919 := by
  unfold tailWord_2081411
  simp only [CollatzResearch.WordTrace]
  refine ⟨75915295862410898542964087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50610197241607265695309391 75915295862410898542964087)
  ·
    refine ⟨113872943793616347814446131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75915295862410898542964087 113872943793616347814446131)
    ·
      refine ⟨170809415690424521721669197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113872943793616347814446131 170809415690424521721669197)
      ·
        refine ⟨64053530883909195645625949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170809415690424521721669197 64053530883909195645625949)
        ·
          refine ⟨24020074081465948367109731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64053530883909195645625949 24020074081465948367109731)
          ·
            refine ⟨36030111122198922550664597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24020074081465948367109731 36030111122198922550664597)
            ·
              refine ⟨1688911458853074494562403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36030111122198922550664597 1688911458853074494562403)
              ·
                refine ⟨2533367188279611741843605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688911458853074494562403 2533367188279611741843605)
                ·
                  refine ⟨118751586950606800398919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2533367188279611741843605 118751586950606800398919)
                  ·
                    rfl

theorem cell23_2081411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 6].length) (baseStart_2081411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081411 prefixEnd_2081411 := by exact prefixLift 2081411
  have htrace : WordTrace (prefixWord ++ tailWord_2081411) baseStart_2081411 baseEnd_2081411 := by
    simpa [prefixWord, tailWord_2081411, baseEnd_2081411] using wordTrace_append hprefix tailTrace_2081411
  have hstable : (prefixWord ++ tailWord_2081411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081411).length < 2 ^ (prefixWord ++ tailWord_2081411).sum := by decide
  have hdescent : baseEnd_2081411 < baseStart_2081411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081455 : List Nat := [1, 1, 2, 1, 2, 6, 1, 4, 1, 1, 3]
def baseStart_2081455 : Nat := 118140960795 + 2081455 * 2 ^ 59
def prefixEnd_2081455 : Nat := 4983230072969 + 3 ^ 40 * 2081455 * 2
def baseEnd_2081455 : Nat := 1068786875704259031440069

theorem tailTrace_2081455 : CollatzResearch.WordTrace tailWord_2081455 prefixEnd_2081455 1068786875704259031440069 := by
  unfold tailWord_2081455
  simp only [CollatzResearch.WordTrace]
  refine ⟨75916900674251494057565819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50611267116167662705043879 75916900674251494057565819)
  ·
    refine ⟨113875351011377241086348729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75916900674251494057565819 113875351011377241086348729)
    ·
      refine ⟨85406513258532930814761547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113875351011377241086348729 85406513258532930814761547)
      ·
        refine ⟨128109769887799396222142321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85406513258532930814761547 128109769887799396222142321)
        ·
          refine ⟨96082327415849547166606741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128109769887799396222142321 96082327415849547166606741)
          ·
            refine ⟨4503859097617947523434691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96082327415849547166606741 4503859097617947523434691)
            ·
              refine ⟨6755788646426921285152037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503859097617947523434691 6755788646426921285152037)
              ·
                refine ⟨1266710371205047740966007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6755788646426921285152037 1266710371205047740966007)
                ·
                  refine ⟨1900065556807571611449011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266710371205047740966007 1900065556807571611449011)
                  ·
                    refine ⟨2850098335211357417173517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1900065556807571611449011 2850098335211357417173517)
                    ·
                      refine ⟨1068786875704259031440069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2850098335211357417173517 1068786875704259031440069)
                      ·
                        rfl

theorem cell23_2081455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 1, 1, 3].length) (baseStart_2081455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081455 prefixEnd_2081455 := by exact prefixLift 2081455
  have htrace : WordTrace (prefixWord ++ tailWord_2081455) baseStart_2081455 baseEnd_2081455 := by
    simpa [prefixWord, tailWord_2081455, baseEnd_2081455] using wordTrace_append hprefix tailTrace_2081455
  have hstable : (prefixWord ++ tailWord_2081455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081455).length < 2 ^ (prefixWord ++ tailWord_2081455).sum := by decide
  have hdescent : baseEnd_2081455 < baseStart_2081455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081471 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 1, 6]
def baseStart_2081471 : Nat := 118140960795 + 2081471 * 2 ^ 59
def prefixEnd_2081471 : Nat := 4983230072969 + 3 ^ 40 * 2081471 * 2
def baseEnd_2081471 : Nat := 356265030464910322946665

theorem tailTrace_2081471 : CollatzResearch.WordTrace tailWord_2081471 prefixEnd_2081471 356265030464910322946665 := by
  unfold tailWord_2081471
  simp only [CollatzResearch.WordTrace]
  refine ⟨75917484242193528790148267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50611656161462352526765511 75917484242193528790148267)
  ·
    refine ⟨113876226363290293185222401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75917484242193528790148267 113876226363290293185222401)
    ·
      refine ⟨85407169772467719888916801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113876226363290293185222401 85407169772467719888916801)
      ·
        refine ⟨64055377329350789916687601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85407169772467719888916801 64055377329350789916687601)
        ·
          refine ⟨48041532997013092437515701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64055377329350789916687601 48041532997013092437515701)
          ·
            refine ⟨4503893718469977416017097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48041532997013092437515701 4503893718469977416017097)
            ·
              refine ⟨3377920288852483062012823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4503893718469977416017097 3377920288852483062012823)
              ·
                refine ⟨5066880433278724593019235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3377920288852483062012823 5066880433278724593019235)
                ·
                  refine ⟨7600320649918086889528853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5066880433278724593019235 7600320649918086889528853)
                  ·
                    refine ⟨356265030464910322946665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7600320649918086889528853 356265030464910322946665)
                    ·
                      rfl

theorem cell23_2081471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 6].length) (baseStart_2081471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081471 prefixEnd_2081471 := by exact prefixLift 2081471
  have htrace : WordTrace (prefixWord ++ tailWord_2081471) baseStart_2081471 baseEnd_2081471 := by
    simpa [prefixWord, tailWord_2081471, baseEnd_2081471] using wordTrace_append hprefix tailTrace_2081471
  have hstable : (prefixWord ++ tailWord_2081471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081471).length < 2 ^ (prefixWord ++ tailWord_2081471).sum := by decide
  have hdescent : baseEnd_2081471 < baseStart_2081471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081492 : List Nat := [2, 4, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_2081492 : Nat := 118140960795 + 2081492 * 2 ^ 59
def prefixEnd_2081492 : Nat := 4983230072969 + 3 ^ 40 * 2081492 * 2
def baseEnd_2081492 : Nat := 356268624829491795559133

theorem tailTrace_2081492 : CollatzResearch.WordTrace tailWord_2081492 prefixEnd_2081492 356268624829491795559133 := by
  unfold tailWord_2081492
  simp only [CollatzResearch.WordTrace]
  refine ⟨37959125087558724688331365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50612166783411632917775153 37959125087558724688331365)
  ·
    refine ⟨7117335953917260879062131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37959125087558724688331365 7117335953917260879062131)
    ·
      refine ⟨10676003930875891318593197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7117335953917260879062131 10676003930875891318593197)
      ·
        refine ⟨4003501474078459244472449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10676003930875891318593197 4003501474078459244472449)
        ·
          refine ⟨3002626105558844433354337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4003501474078459244472449 3002626105558844433354337)
          ·
            refine ⟨2251969579169133325015753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3002626105558844433354337 2251969579169133325015753)
            ·
              refine ⟨1688977184376849993761815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2251969579169133325015753 1688977184376849993761815)
              ·
                refine ⟨2533465776565274990642723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688977184376849993761815 2533465776565274990642723)
                ·
                  refine ⟨3800198664847912485964085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533465776565274990642723 3800198664847912485964085)
                  ·
                    refine ⟨356268624829491795559133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3800198664847912485964085 356268624829491795559133)
                    ·
                      rfl

theorem cell23_2081492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_2081492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081492 prefixEnd_2081492 := by exact prefixLift 2081492
  have htrace : WordTrace (prefixWord ++ tailWord_2081492) baseStart_2081492 baseEnd_2081492 := by
    simpa [prefixWord, tailWord_2081492, baseEnd_2081492] using wordTrace_append hprefix tailTrace_2081492
  have hstable : (prefixWord ++ tailWord_2081492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081492).length < 2 ^ (prefixWord ++ tailWord_2081492).sum := by decide
  have hdescent : baseEnd_2081492 < baseStart_2081492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081495 : List Nat := [1, 1, 3, 2, 1, 6, 2, 1, 1, 1, 4]
def baseStart_2081495 : Nat := 118140960795 + 2081495 * 2 ^ 59
def prefixEnd_2081495 : Nat := 4983230072969 + 3 ^ 40 * 2081495 * 2
def baseEnd_2081495 : Nat := 1068807414930438874939885

theorem tailTrace_2081495 : CollatzResearch.WordTrace tailWord_2081495 prefixEnd_2081495 1068807414930438874939885 := by
  unfold tailWord_2081495
  simp only [CollatzResearch.WordTrace]
  refine ⟨75918359594106580889021939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50612239729404387259347959 75918359594106580889021939)
  ·
    refine ⟨113877539391159871333532909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75918359594106580889021939 113877539391159871333532909)
    ·
      refine ⟨42704077271684951750074841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113877539391159871333532909 42704077271684951750074841)
      ·
        refine ⟨32028057953763713812556131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42704077271684951750074841 32028057953763713812556131)
        ·
          refine ⟨48042086930645570718834197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32028057953763713812556131 48042086930645570718834197)
          ·
            refine ⟨2251972824874011127445353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48042086930645570718834197 2251972824874011127445353)
            ·
              refine ⟨1688979618655508345584015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2251972824874011127445353 1688979618655508345584015)
              ·
                refine ⟨2533469427983262518376023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688979618655508345584015 2533469427983262518376023)
                ·
                  refine ⟨3800204141974893777564035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533469427983262518376023 3800204141974893777564035)
                  ·
                    refine ⟨5700306212962340666346053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3800204141974893777564035 5700306212962340666346053)
                    ·
                      refine ⟨1068807414930438874939885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5700306212962340666346053 1068807414930438874939885)
                      ·
                        rfl

theorem cell23_2081495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_2081495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081495 prefixEnd_2081495 := by exact prefixLift 2081495
  have htrace : WordTrace (prefixWord ++ tailWord_2081495) baseStart_2081495 baseEnd_2081495 := by
    simpa [prefixWord, tailWord_2081495, baseEnd_2081495] using wordTrace_append hprefix tailTrace_2081495
  have hstable : (prefixWord ++ tailWord_2081495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081495).length < 2 ^ (prefixWord ++ tailWord_2081495).sum := by decide
  have hdescent : baseEnd_2081495 < baseStart_2081495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081498 : List Nat := [3, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3]
def baseStart_2081498 : Nat := 118140960795 + 2081498 * 2 ^ 59
def prefixEnd_2081498 : Nat := 4983230072969 + 3 ^ 40 * 2081498 * 2
def baseEnd_2081498 : Nat := 1068808955372402363202371

theorem tailTrace_2081498 : CollatzResearch.WordTrace tailWord_2081498 prefixEnd_2081498 1068808955372402363202371 := by
  unfold tailWord_2081498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18979617253273928100345287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50612312675397141600920765 18979617253273928100345287)
  ·
    refine ⟨28469425879910892150517931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18979617253273928100345287 28469425879910892150517931)
    ·
      refine ⟨42704138819866338225776897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28469425879910892150517931 42704138819866338225776897)
      ·
        refine ⟨32028104114899753669332673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42704138819866338225776897 32028104114899753669332673)
        ·
          refine ⟨24021078086174815251999505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32028104114899753669332673 24021078086174815251999505)
          ·
            refine ⟨18015808564631111438999629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24021078086174815251999505 18015808564631111438999629)
            ·
              refine ⟨6755928211736666789624861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18015808564631111438999629 6755928211736666789624861)
              ·
                refine ⟨2533473079401250046109323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6755928211736666789624861 2533473079401250046109323)
                ·
                  refine ⟨3800209619101875069163985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533473079401250046109323 3800209619101875069163985)
                  ·
                    refine ⟨2850157214326406301872989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3800209619101875069163985 2850157214326406301872989)
                    ·
                      refine ⟨1068808955372402363202371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2850157214326406301872989 1068808955372402363202371)
                      ·
                        rfl

theorem cell23_2081498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_2081498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081498 prefixEnd_2081498 := by exact prefixLift 2081498
  have htrace : WordTrace (prefixWord ++ tailWord_2081498) baseStart_2081498 baseEnd_2081498 := by
    simpa [prefixWord, tailWord_2081498, baseEnd_2081498] using wordTrace_append hprefix tailTrace_2081498
  have hstable : (prefixWord ++ tailWord_2081498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081498).length < 2 ^ (prefixWord ++ tailWord_2081498).sum := by decide
  have hdescent : baseEnd_2081498 < baseStart_2081498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081504 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 6]
def baseStart_2081504 : Nat := 118140960795 + 2081504 * 2 ^ 59
def prefixEnd_2081504 : Nat := 4983230072969 + 3 ^ 40 * 2081504 * 2
def baseEnd_2081504 : Nat := 1068812036256329339727343

theorem tailTrace_2081504 : CollatzResearch.WordTrace tailWord_2081504 prefixEnd_2081504 1068812036256329339727343 := by
  unfold tailWord_2081504
  simp only [CollatzResearch.WordTrace]
  refine ⟨37959343925536987713049783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50612458567382650284066377 37959343925536987713049783)
  ·
    refine ⟨56939015888305481569574675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37959343925536987713049783 56939015888305481569574675)
    ·
      refine ⟨85408523832458222354362013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56939015888305481569574675 85408523832458222354362013)
      ·
        refine ⟨32028196437171833382885755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85408523832458222354362013 32028196437171833382885755)
        ·
          refine ⟨48042294655757750074328633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32028196437171833382885755 48042294655757750074328633)
          ·
            refine ⟨36031720991818312555746475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48042294655757750074328633 36031720991818312555746475)
            ·
              refine ⟨54047581487727468833619713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36031720991818312555746475 54047581487727468833619713)
              ·
                refine ⟨40535686115795601625214785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54047581487727468833619713 40535686115795601625214785)
                ·
                  refine ⟨30401764586846701218911089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40535686115795601625214785 30401764586846701218911089)
                  ·
                    refine ⟨22801323440135025914183317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30401764586846701218911089 22801323440135025914183317)
                    ·
                      refine ⟨1068812036256329339727343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22801323440135025914183317 1068812036256329339727343)
                      ·
                        rfl

theorem cell23_2081504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_2081504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081504 prefixEnd_2081504 := by exact prefixLift 2081504
  have htrace : WordTrace (prefixWord ++ tailWord_2081504) baseStart_2081504 baseEnd_2081504 := by
    simpa [prefixWord, tailWord_2081504, baseEnd_2081504] using wordTrace_append hprefix tailTrace_2081504
  have hstable : (prefixWord ++ tailWord_2081504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081504).length < 2 ^ (prefixWord ++ tailWord_2081504).sum := by decide
  have hdescent : baseEnd_2081504 < baseStart_2081504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081505 : List Nat := [1, 2, 3, 1, 4, 3, 1, 2, 2, 4]
def baseStart_2081505 : Nat := 118140960795 + 2081505 * 2 ^ 59
def prefixEnd_2081505 : Nat := 4983230072969 + 3 ^ 40 * 2081505 * 2
def baseEnd_2081505 : Nat := 356270849912327945271613

theorem tailTrace_2081505 : CollatzResearch.WordTrace tailWord_2081505 prefixEnd_2081505 356270849912327945271613 := by
  unfold tailWord_2081505
  simp only [CollatzResearch.WordTrace]
  refine ⟨75918724324070352596885969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50612482882713568397923979 75918724324070352596885969)
  ·
    refine ⟨56939043243052764447664477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75918724324070352596885969 56939043243052764447664477)
    ·
      refine ⟨21352141216144786667874179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56939043243052764447664477 21352141216144786667874179)
      ·
        refine ⟨32028211824217180001811269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21352141216144786667874179 32028211824217180001811269)
        ·
          refine ⟨6005289717040721250339613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32028211824217180001811269 6005289717040721250339613)
          ·
            refine ⟨2251983643890270468877355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6005289717040721250339613 2251983643890270468877355)
            ·
              refine ⟨3377975465835405703316033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2251983643890270468877355 3377975465835405703316033)
              ·
                refine ⟨2533481599376554277487025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3377975465835405703316033 2533481599376554277487025)
                ·
                  refine ⟨1900111199532415708115269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2533481599376554277487025 1900111199532415708115269)
                  ·
                    refine ⟨356270849912327945271613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1900111199532415708115269 356270849912327945271613)
                    ·
                      rfl

theorem cell23_2081505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_2081505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081505 prefixEnd_2081505 := by exact prefixLift 2081505
  have htrace : WordTrace (prefixWord ++ tailWord_2081505) baseStart_2081505 baseEnd_2081505 := by
    simpa [prefixWord, tailWord_2081505, baseEnd_2081505] using wordTrace_append hprefix tailTrace_2081505
  have hstable : (prefixWord ++ tailWord_2081505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081505).length < 2 ^ (prefixWord ++ tailWord_2081505).sum := by decide
  have hdescent : baseEnd_2081505 < baseStart_2081505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081512 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_2081512 : Nat := 118140960795 + 2081512 * 2 ^ 59
def prefixEnd_2081512 : Nat := 4983230072969 + 3 ^ 40 * 2081512 * 2
def baseEnd_2081512 : Nat := 1068816144101565308427307

theorem tailTrace_2081512 : CollatzResearch.WordTrace tailWord_2081512 prefixEnd_2081512 1068816144101565308427307 := by
  unfold tailWord_2081512
  simp only [CollatzResearch.WordTrace]
  refine ⟨37959489817522496396195395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50612653090029995194927193 37959489817522496396195395)
  ·
    refine ⟨56939234726283744594293093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37959489817522496396195395 56939234726283744594293093)
    ·
      refine ⟨10676106511178202111429955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56939234726283744594293093 10676106511178202111429955)
      ·
        refine ⟨16014159766767303167144933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10676106511178202111429955 16014159766767303167144933)
        ·
          refine ⟨3002654956268869343839675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16014159766767303167144933 3002654956268869343839675)
          ·
            refine ⟨4503982434403304015759513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002654956268869343839675 4503982434403304015759513)
            ·
              refine ⟨3377986825802478011819635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4503982434403304015759513 3377986825802478011819635)
              ·
                refine ⟨5066980238703717017729453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3377986825802478011819635 5066980238703717017729453)
                ·
                  refine ⟨1900117589513893881648545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5066980238703717017729453 1900117589513893881648545)
                  ·
                    refine ⟨1425088192135420411236409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1900117589513893881648545 1425088192135420411236409)
                    ·
                      refine ⟨1068816144101565308427307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1425088192135420411236409 1068816144101565308427307)
                      ·
                        rfl

theorem cell23_2081512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_2081512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081512 prefixEnd_2081512 := by exact prefixLift 2081512
  have htrace : WordTrace (prefixWord ++ tailWord_2081512) baseStart_2081512 baseEnd_2081512 := by
    simpa [prefixWord, tailWord_2081512, baseEnd_2081512] using wordTrace_append hprefix tailTrace_2081512
  have hstable : (prefixWord ++ tailWord_2081512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081512).length < 2 ^ (prefixWord ++ tailWord_2081512).sum := by decide
  have hdescent : baseEnd_2081512 < baseStart_2081512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081571 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 3]
def baseStart_2081571 : Nat := 118140960795 + 2081571 * 2 ^ 59
def prefixEnd_2081571 : Nat := 4983230072969 + 3 ^ 40 * 2081571 * 2
def baseEnd_2081571 : Nat := 1068846439460180577589535

theorem tailTrace_2081571 : CollatzResearch.WordTrace tailWord_2081571 prefixEnd_2081571 1068846439460180577589535 := by
  unfold tailWord_2081571
  simp only [CollatzResearch.WordTrace]
  refine ⟨75921131541831245868788567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50614087694554163912525711 75921131541831245868788567)
  ·
    refine ⟨113881697312746868803182851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75921131541831245868788567 113881697312746868803182851)
    ·
      refine ⟨170822545969120303204774277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113881697312746868803182851 170822545969120303204774277)
      ·
        refine ⟨32029227369210056850895177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170822545969120303204774277 32029227369210056850895177)
        ·
          refine ⟨24021920526907542638171383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32029227369210056850895177 24021920526907542638171383)
          ·
            refine ⟨36032880790361313957257075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24021920526907542638171383 36032880790361313957257075)
            ·
              refine ⟨54049321185541970935885613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36032880790361313957257075 54049321185541970935885613)
              ·
                refine ⟨20268495444578239100957105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54049321185541970935885613 20268495444578239100957105)
                ·
                  refine ⟨15201371583433679325717829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20268495444578239100957105 15201371583433679325717829)
                  ·
                    refine ⟨2850257171893814873572093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15201371583433679325717829 2850257171893814873572093)
                    ·
                      refine ⟨1068846439460180577589535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2850257171893814873572093 1068846439460180577589535)
                      ·
                        rfl

theorem cell23_2081571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_2081571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081571 prefixEnd_2081571 := by exact prefixLift 2081571
  have htrace : WordTrace (prefixWord ++ tailWord_2081571) baseStart_2081571 baseEnd_2081571 := by
    simpa [prefixWord, tailWord_2081571, baseEnd_2081571] using wordTrace_append hprefix tailTrace_2081571
  have hstable : (prefixWord ++ tailWord_2081571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081571).length < 2 ^ (prefixWord ++ tailWord_2081571).sum := by decide
  have hdescent : baseEnd_2081571 < baseStart_2081571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081608 : List Nat := [2, 1, 3, 1, 1, 3, 2, 5, 5]
def baseStart_2081608 : Nat := 118140960795 + 2081608 * 2 ^ 59
def prefixEnd_2081608 : Nat := 4983230072969 + 3 ^ 40 * 2081608 * 2
def baseEnd_2081608 : Nat := 118762826471599659202985

theorem tailTrace_2081608 : CollatzResearch.WordTrace tailWord_2081608 prefixEnd_2081608 118762826471599659202985 := by
  unfold tailWord_2081608
  simp only [CollatzResearch.WordTrace]
  refine ⟨37961240521348600593942739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50614987361798134125256985 37961240521348600593942739)
  ·
    refine ⟨56941860782022900890914109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37961240521348600593942739 56941860782022900890914109)
    ·
      refine ⟨21353197793258587834092791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56941860782022900890914109 21353197793258587834092791)
      ·
        refine ⟨32029796689887881751139187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21353197793258587834092791 32029796689887881751139187)
        ·
          refine ⟨48044695034831822626708781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32029796689887881751139187 48044695034831822626708781)
          ·
            refine ⟨18016760638061933485015793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48044695034831822626708781 18016760638061933485015793)
            ·
              refine ⟨13512570478546450113761845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18016760638061933485015793 13512570478546450113761845)
              ·
                refine ⟨1266803482363729698165173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13512570478546450113761845 1266803482363729698165173)
                ·
                  refine ⟨118762826471599659202985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1266803482363729698165173 118762826471599659202985)
                  ·
                    rfl

theorem cell23_2081608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 5].length) (baseStart_2081608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081608 prefixEnd_2081608 := by exact prefixLift 2081608
  have htrace : WordTrace (prefixWord ++ tailWord_2081608) baseStart_2081608 baseEnd_2081608 := by
    simpa [prefixWord, tailWord_2081608, baseEnd_2081608] using wordTrace_append hprefix tailTrace_2081608
  have hstable : (prefixWord ++ tailWord_2081608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081608).length < 2 ^ (prefixWord ++ tailWord_2081608).sum := by decide
  have hdescent : baseEnd_2081608 < baseStart_2081608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081618 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_2081618 : Nat := 118140960795 + 2081618 * 2 ^ 59
def prefixEnd_2081618 : Nat := 4983230072969 + 3 ^ 40 * 2081618 * 2
def baseEnd_2081618 : Nat := 1068870573050941893701819

theorem tailTrace_2081618 : CollatzResearch.WordTrace tailWord_2081618 prefixEnd_2081618 1068870573050941893701819 := by
  unfold tailWord_2081618
  simp only [CollatzResearch.WordTrace]
  refine ⟨18980711443165243223937377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50615230515107315263833005 18980711443165243223937377)
  ·
    refine ⟨14235533582373932417953033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18980711443165243223937377 14235533582373932417953033)
    ·
      refine ⟨10676650186780449313464775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14235533582373932417953033 10676650186780449313464775)
      ·
        refine ⟨16014975280170673970197163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10676650186780449313464775 16014975280170673970197163)
        ·
          refine ⟨24022462920256010955295745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16014975280170673970197163 24022462920256010955295745)
          ·
            refine ⟨18016847190192008216471809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24022462920256010955295745 18016847190192008216471809)
            ·
              refine ⟨13512635392644006162353857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18016847190192008216471809 13512635392644006162353857)
              ·
                refine ⟨10134476544483004621765393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13512635392644006162353857 10134476544483004621765393)
                ·
                  refine ⟨7600857408362253466324045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10134476544483004621765393 7600857408362253466324045)
                  ·
                    refine ⟨2850321528135845049871517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7600857408362253466324045 2850321528135845049871517)
                    ·
                      refine ⟨1068870573050941893701819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2850321528135845049871517 1068870573050941893701819)
                      ·
                        rfl

theorem cell23_2081618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_2081618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081618 prefixEnd_2081618 := by exact prefixLift 2081618
  have htrace : WordTrace (prefixWord ++ tailWord_2081618) baseStart_2081618 baseEnd_2081618 := by
    simpa [prefixWord, tailWord_2081618, baseEnd_2081618] using wordTrace_append hprefix tailTrace_2081618
  have hstable : (prefixWord ++ tailWord_2081618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081618).length < 2 ^ (prefixWord ++ tailWord_2081618).sum := by decide
  have hdescent : baseEnd_2081618 < baseStart_2081618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081625 : List Nat := [1, 2, 1, 2, 2, 4, 4, 2, 5]
def baseStart_2081625 : Nat := 118140960795 + 2081625 * 2 ^ 59
def prefixEnd_2081625 : Nat := 4983230072969 + 3 ^ 40 * 2081625 * 2
def baseEnd_2081625 : Nat := 118763796379502596257143

theorem tailTrace_2081625 : CollatzResearch.WordTrace tailWord_2081625 prefixEnd_2081625 118763796379502596257143 := by
  unfold tailWord_2081625
  simp only [CollatzResearch.WordTrace]
  refine ⟨75923101083635613091254329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50615400722423742060836219 75923101083635613091254329)
  ·
    refine ⟨56942325812726709818440747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75923101083635613091254329 56942325812726709818440747)
    ·
      refine ⟨85413488719090064727661121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56942325812726709818440747 85413488719090064727661121)
      ·
        refine ⟨64060116539317548545745841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85413488719090064727661121 64060116539317548545745841)
        ·
          refine ⟨48045087404488161409309381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64060116539317548545745841 48045087404488161409309381)
          ·
            refine ⟨9008453888341530264245509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48045087404488161409309381 9008453888341530264245509)
            ·
              refine ⟨1689085104064036924546033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9008453888341530264245509 1689085104064036924546033)
              ·
                refine ⟨1266813828048027693409525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1689085104064036924546033 1266813828048027693409525)
                ·
                  refine ⟨118763796379502596257143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1266813828048027693409525 118763796379502596257143)
                  ·
                    rfl

theorem cell23_2081625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 5].length) (baseStart_2081625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081625 prefixEnd_2081625 := by exact prefixLift 2081625
  have htrace : WordTrace (prefixWord ++ tailWord_2081625) baseStart_2081625 baseEnd_2081625 := by
    simpa [prefixWord, tailWord_2081625, baseEnd_2081625] using wordTrace_append hprefix tailTrace_2081625
  have hstable : (prefixWord ++ tailWord_2081625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081625).length < 2 ^ (prefixWord ++ tailWord_2081625).sum := by decide
  have hdescent : baseEnd_2081625 < baseStart_2081625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081631 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 5]
def baseStart_2081631 : Nat := 118140960795 + 2081631 * 2 ^ 59
def prefixEnd_2081631 : Nat := 4983230072969 + 3 ^ 40 * 2081631 * 2
def baseEnd_2081631 : Nat := 1068877248299450342839259

theorem tailTrace_2081631 : CollatzResearch.WordTrace tailWord_2081631 prefixEnd_2081631 1068877248299450342839259 := by
  unfold tailWord_2081631
  simp only [CollatzResearch.WordTrace]
  refine ⟨75923319921613876115972747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50615546614409250743981831 75923319921613876115972747)
  ·
    refine ⟨113884979882420814173959121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75923319921613876115972747 113884979882420814173959121)
    ·
      refine ⟨85413734911815610630469341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113884979882420814173959121 85413734911815610630469341)
      ·
        refine ⟨32030150591930853986426003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85413734911815610630469341 32030150591930853986426003)
        ·
          refine ⟨48045225887896280979639005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32030150591930853986426003 48045225887896280979639005)
          ·
            refine ⟨18016959707961105367364627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48045225887896280979639005 18016959707961105367364627)
            ·
              refine ⟨27025439561941658051046941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18016959707961105367364627 27025439561941658051046941)
              ·
                refine ⟨10134539835728121769142603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27025439561941658051046941 10134539835728121769142603)
                ·
                  refine ⟨15201809753592182653713905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10134539835728121769142603 15201809753592182653713905)
                  ·
                    refine ⟨11401357315194136990285429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15201809753592182653713905 11401357315194136990285429)
                    ·
                      refine ⟨1068877248299450342839259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11401357315194136990285429 1068877248299450342839259)
                      ·
                        rfl

theorem cell23_2081631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_2081631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081631 prefixEnd_2081631 := by exact prefixLift 2081631
  have htrace : WordTrace (prefixWord ++ tailWord_2081631) baseStart_2081631 baseEnd_2081631 := by
    simpa [prefixWord, tailWord_2081631, baseEnd_2081631] using wordTrace_append hprefix tailTrace_2081631
  have hstable : (prefixWord ++ tailWord_2081631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081631).length < 2 ^ (prefixWord ++ tailWord_2081631).sum := by decide
  have hdescent : baseEnd_2081631 < baseStart_2081631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081658 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2]
def baseStart_2081658 : Nat := 118140960795 + 2081658 * 2 ^ 59
def prefixEnd_2081658 : Nat := 4983230072969 + 3 ^ 40 * 2081658 * 2
def baseEnd_2081658 : Nat := 1068891112277121737201635

theorem tailTrace_2081658 : CollatzResearch.WordTrace tailWord_2081658 prefixEnd_2081658 1068891112277121737201635 := by
  unfold tailWord_2081658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18981076173129014931801407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50616203128344039818137085 18981076173129014931801407)
  ·
    refine ⟨28471614259693522397702111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18981076173129014931801407 28471614259693522397702111)
    ·
      refine ⟨42707421389540283596553167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28471614259693522397702111 42707421389540283596553167)
      ·
        refine ⟨64061132084310425394829751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42707421389540283596553167 64061132084310425394829751)
        ·
          refine ⟨96091698126465638092244627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64061132084310425394829751 96091698126465638092244627)
          ·
            refine ⟨144137547189698457138366941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96091698126465638092244627 144137547189698457138366941)
            ·
              refine ⟨54051580196136921426887603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144137547189698457138366941 54051580196136921426887603)
              ·
                refine ⟨81077370294205382140331405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54051580196136921426887603 81077370294205382140331405)
                ·
                  refine ⟨30404013860327018302624277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81077370294205382140331405 30404013860327018302624277)
                  ·
                    refine ⟨1425188149702828982935513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30404013860327018302624277 1425188149702828982935513)
                    ·
                      refine ⟨1068891112277121737201635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1425188149702828982935513 1068891112277121737201635)
                      ·
                        rfl

theorem cell23_2081658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2].length) (baseStart_2081658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081658 prefixEnd_2081658 := by exact prefixLift 2081658
  have htrace : WordTrace (prefixWord ++ tailWord_2081658) baseStart_2081658 baseEnd_2081658 := by
    simpa [prefixWord, tailWord_2081658, baseEnd_2081658] using wordTrace_append hprefix tailTrace_2081658
  have hstable : (prefixWord ++ tailWord_2081658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081658).length < 2 ^ (prefixWord ++ tailWord_2081658).sum := by decide
  have hdescent : baseEnd_2081658 < baseStart_2081658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081668 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_2081668 : Nat := 118140960795 + 2081668 * 2 ^ 59
def prefixEnd_2081668 : Nat := 4983230072969 + 3 ^ 40 * 2081668 * 2
def baseEnd_2081668 : Nat := 356298749027888899358863

theorem tailTrace_2081668 : CollatzResearch.WordTrace tailWord_2081668 prefixEnd_2081668 356298749027888899358863 := by
  unfold tailWord_2081668
  simp only [CollatzResearch.WordTrace]
  refine ⟨37962334711239915717534829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50616446281653220956713105 37962334711239915717534829)
  ·
    refine ⟨14235875516714968394075561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37962334711239915717534829 14235875516714968394075561)
    ·
      refine ⟨10676906637536226295556671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14235875516714968394075561 10676906637536226295556671)
      ·
        refine ⟨16015359956304339443335007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10676906637536226295556671 16015359956304339443335007)
        ·
          refine ⟨24023039934456509165002511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16015359956304339443335007 24023039934456509165002511)
          ·
            refine ⟨36034559901684763747503767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24023039934456509165002511 36034559901684763747503767)
            ·
              refine ⟨54051839852527145621255651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36034559901684763747503767 54051839852527145621255651)
              ·
                refine ⟨81077759778790718431883477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54051839852527145621255651 81077759778790718431883477)
                ·
                  refine ⟨1900259994815407463247269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 81077759778790718431883477 1900259994815407463247269)
                  ·
                    refine ⟨356298749027888899358863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1900259994815407463247269 356298749027888899358863)
                    ·
                      rfl

theorem cell23_2081668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_2081668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081668 prefixEnd_2081668 := by exact prefixLift 2081668
  have htrace : WordTrace (prefixWord ++ tailWord_2081668) baseStart_2081668 baseEnd_2081668 := by
    simpa [prefixWord, tailWord_2081668, baseEnd_2081668] using wordTrace_append hprefix tailTrace_2081668
  have hstable : (prefixWord ++ tailWord_2081668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081668).length < 2 ^ (prefixWord ++ tailWord_2081668).sum := by decide
  have hdescent : baseEnd_2081668 < baseStart_2081668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081685 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 3, 4]
def baseStart_2081685 : Nat := 118140960795 + 2081685 * 2 ^ 59
def prefixEnd_2081685 : Nat := 4983230072969 + 3 ^ 40 * 2081685 * 2
def baseEnd_2081685 : Nat := 356301658751597710521337

theorem tailTrace_2081685 : CollatzResearch.WordTrace tailWord_2081685 prefixEnd_2081685 356301658751597710521337 := by
  unfold tailWord_2081685
  simp only [CollatzResearch.WordTrace]
  refine ⟨75925289463418243338438509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50616859642278828892292339 75925289463418243338438509)
  ·
    refine ⟨28471983548781841251914441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75925289463418243338438509 28471983548781841251914441)
    ·
      refine ⟨21353987661586380938935831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28471983548781841251914441 21353987661586380938935831)
      ·
        refine ⟨32030981492379571408403747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21353987661586380938935831 32030981492379571408403747)
        ·
          refine ⟨48046472238569357112605621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32030981492379571408403747 48046472238569357112605621)
          ·
            refine ⟨4504356772365877229306777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48046472238569357112605621 4504356772365877229306777)
            ·
              refine ⟨3378267579274407921980083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4504356772365877229306777 3378267579274407921980083)
              ·
                refine ⟨5067401368911611882970125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378267579274407921980083 5067401368911611882970125)
                ·
                  refine ⟨1900275513341854456113797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5067401368911611882970125 1900275513341854456113797)
                  ·
                    refine ⟨356301658751597710521337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1900275513341854456113797 356301658751597710521337)
                    ·
                      rfl

theorem cell23_2081685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_2081685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081685 prefixEnd_2081685 := by exact prefixLift 2081685
  have htrace : WordTrace (prefixWord ++ tailWord_2081685) baseStart_2081685 baseEnd_2081685 := by
    simpa [prefixWord, tailWord_2081685, baseEnd_2081685] using wordTrace_append hprefix tailTrace_2081685
  have hstable : (prefixWord ++ tailWord_2081685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081685).length < 2 ^ (prefixWord ++ tailWord_2081685).sum := by decide
  have hdescent : baseEnd_2081685 < baseStart_2081685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081735 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 4, 3, 2]
def baseStart_2081735 : Nat := 118140960795 + 2081735 * 2 ^ 59
def prefixEnd_2081735 : Nat := 4983230072969 + 3 ^ 40 * 2081735 * 2
def baseEnd_2081735 : Nat := 1068930650287517935938781

theorem tailTrace_2081735 : CollatzResearch.WordTrace tailWord_2081735 prefixEnd_2081735 1068930650287517935938781 := by
  unfold tailWord_2081735
  simp only [CollatzResearch.WordTrace]
  refine ⟨75927113113237101877758659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50618075408824734585172439 75927113113237101877758659)
  ·
    refine ⟨113890669669855652816637989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75927113113237101877758659 113890669669855652816637989)
    ·
      refine ⟨21354500563097934903119623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113890669669855652816637989 21354500563097934903119623)
      ·
        refine ⟨32031750844646902354679435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21354500563097934903119623 32031750844646902354679435)
        ·
          refine ⟨48047626266970353532019153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32031750844646902354679435 48047626266970353532019153)
          ·
            refine ⟨36035719700227765149014365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48047626266970353532019153 36035719700227765149014365)
            ·
              refine ⟨13513394887585411930880387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36035719700227765149014365 13513394887585411930880387)
              ·
                refine ⟨20270092331378117896320581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13513394887585411930880387 20270092331378117896320581)
                ·
                  refine ⟨3800642312133397105560109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20270092331378117896320581 3800642312133397105560109)
                  ·
                    refine ⟨1425240867050023914585041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3800642312133397105560109 1425240867050023914585041)
                    ·
                      refine ⟨1068930650287517935938781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1425240867050023914585041 1068930650287517935938781)
                      ·
                        rfl

theorem cell23_2081735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_2081735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081735 prefixEnd_2081735 := by exact prefixLift 2081735
  have htrace : WordTrace (prefixWord ++ tailWord_2081735) baseStart_2081735 baseEnd_2081735 := by
    simpa [prefixWord, tailWord_2081735, baseEnd_2081735] using wordTrace_append hprefix tailTrace_2081735
  have hstable : (prefixWord ++ tailWord_2081735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081735).length < 2 ^ (prefixWord ++ tailWord_2081735).sum := by decide
  have hdescent : baseEnd_2081735 < baseStart_2081735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081742 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_2081742 : Nat := 118140960795 + 2081742 * 2 ^ 59
def prefixEnd_2081742 : Nat := 4983230072969 + 3 ^ 40 * 2081742 * 2
def baseEnd_2081742 : Nat := 1068934244652099408551249

theorem tailTrace_2081742 : CollatzResearch.WordTrace tailWord_2081742 prefixEnd_2081742 1068934244652099408551249 := by
  unfold tailWord_2081742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9490921053026467759157935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50618245616141161382175653 9490921053026467759157935)
  ·
    refine ⟨14236381579539701638736903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9490921053026467759157935 14236381579539701638736903)
    ·
      refine ⟨21354572369309552458105355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14236381579539701638736903 21354572369309552458105355)
      ·
        refine ⟨32031858553964328687158033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21354572369309552458105355 32031858553964328687158033)
        ·
          refine ⟨24023893915473246515368525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32031858553964328687158033 24023893915473246515368525)
          ·
            refine ⟨9008960218302467443263197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24023893915473246515368525 9008960218302467443263197)
            ·
              refine ⟨3378360081863425291223699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9008960218302467443263197 3378360081863425291223699)
              ·
                refine ⟨5067540122795137936835549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378360081863425291223699 5067540122795137936835549)
                ·
                  refine ⟨1900327546048176726313331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5067540122795137936835549 1900327546048176726313331)
                  ·
                    refine ⟨2850491319072265089469997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1900327546048176726313331 2850491319072265089469997)
                    ·
                      refine ⟨1068934244652099408551249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2850491319072265089469997 1068934244652099408551249)
                      ·
                        rfl

theorem cell23_2081742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_2081742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081742 prefixEnd_2081742 := by exact prefixLift 2081742
  have htrace : WordTrace (prefixWord ++ tailWord_2081742) baseStart_2081742 baseEnd_2081742 := by
    simpa [prefixWord, tailWord_2081742, baseEnd_2081742] using wordTrace_append hprefix tailTrace_2081742
  have hstable : (prefixWord ++ tailWord_2081742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081742).length < 2 ^ (prefixWord ++ tailWord_2081742).sum := by decide
  have hdescent : baseEnd_2081742 < baseStart_2081742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081749 : List Nat := [1, 3, 2, 3, 4, 1, 2, 1, 6]
def baseStart_2081749 : Nat := 118140960795 + 2081749 * 2 ^ 59
def prefixEnd_2081749 : Nat := 4983230072969 + 3 ^ 40 * 2081749 * 2
def baseEnd_2081749 : Nat := 118770871001853431240413

theorem tailTrace_2081749 : CollatzResearch.WordTrace tailWord_2081749 prefixEnd_2081749 118770871001853431240413 := by
  unfold tailWord_2081749
  simp only [CollatzResearch.WordTrace]
  refine ⟨75927623735186382268768301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50618415823457588179178867 75927623735186382268768301)
  ·
    refine ⟨28472858900694893350788113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75927623735186382268768301 28472858900694893350788113)
    ·
      refine ⟨21354644175521170013091085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28472858900694893350788113 21354644175521170013091085)
      ·
        refine ⟨8007991565820438754909157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21354644175521170013091085 8007991565820438754909157)
        ·
          refine ⟨1501498418591332266545467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8007991565820438754909157 1501498418591332266545467)
          ·
            refine ⟨2252247627886998399818201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501498418591332266545467 2252247627886998399818201)
            ·
              refine ⟨1689185720915248799863651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2252247627886998399818201 1689185720915248799863651)
              ·
                refine ⟨2533778581372873199795477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689185720915248799863651 2533778581372873199795477)
                ·
                  refine ⟨118770871001853431240413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2533778581372873199795477 118770871001853431240413)
                  ·
                    rfl

theorem cell23_2081749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 6].length) (baseStart_2081749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081749 prefixEnd_2081749 := by exact prefixLift 2081749
  have htrace : WordTrace (prefixWord ++ tailWord_2081749) baseStart_2081749 baseEnd_2081749 := by
    simpa [prefixWord, tailWord_2081749, baseEnd_2081749] using wordTrace_append hprefix tailTrace_2081749
  have hstable : (prefixWord ++ tailWord_2081749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081749).length < 2 ^ (prefixWord ++ tailWord_2081749).sum := by decide
  have hdescent : baseEnd_2081749 < baseStart_2081749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081762 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2081762 : Nat := 118140960795 + 2081762 * 2 ^ 59
def prefixEnd_2081762 : Nat := 4983230072969 + 3 ^ 40 * 2081762 * 2
def baseEnd_2081762 : Nat := 356314838088396443433719

theorem tailTrace_2081762 : CollatzResearch.WordTrace tailWord_2081762 prefixEnd_2081762 356314838088396443433719 := by
  unfold tailWord_2081762
  simp only [CollatzResearch.WordTrace]
  refine ⟨18982024471034821372247885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50618731922759523659327693 18982024471034821372247885)
  ·
    refine ⟨7118259176638058014592957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18982024471034821372247885 7118259176638058014592957)
    ·
      refine ⟨2669347191239271755472359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7118259176638058014592957 2669347191239271755472359)
      ·
        refine ⟨4004020786858907633208539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2669347191239271755472359 4004020786858907633208539)
        ·
          refine ⟨6006031180288361449812809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4004020786858907633208539 6006031180288361449812809)
          ·
            refine ⟨4504523385216271087359607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6006031180288361449812809 4504523385216271087359607)
            ·
              refine ⟨6756785077824406631039411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4504523385216271087359607 6756785077824406631039411)
              ·
                refine ⟨10135177616736609946559117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6756785077824406631039411 10135177616736609946559117)
                ·
                  refine ⟨3800691606276228729959669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10135177616736609946559117 3800691606276228729959669)
                  ·
                    refine ⟨356314838088396443433719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3800691606276228729959669 356314838088396443433719)
                    ·
                      rfl

theorem cell23_2081762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2081762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081762 prefixEnd_2081762 := by exact prefixLift 2081762
  have htrace : WordTrace (prefixWord ++ tailWord_2081762) baseStart_2081762 baseEnd_2081762 := by
    simpa [prefixWord, tailWord_2081762, baseEnd_2081762] using wordTrace_append hprefix tailTrace_2081762
  have hstable : (prefixWord ++ tailWord_2081762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081762).length < 2 ^ (prefixWord ++ tailWord_2081762).sum := by decide
  have hdescent : baseEnd_2081762 < baseStart_2081762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081768 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_2081768 : Nat := 118140960795 + 2081768 * 2 ^ 59
def prefixEnd_2081768 : Nat := 4983230072969 + 3 ^ 40 * 2081768 * 2
def baseEnd_2081768 : Nat := 1068947595149116306826129

theorem tailTrace_2081768 : CollatzResearch.WordTrace tailWord_2081768 prefixEnd_2081768 1068947595149116306826129 := by
  unfold tailWord_2081768
  simp only [CollatzResearch.WordTrace]
  refine ⟨37964158361058774256854979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50618877814745032342473305 37964158361058774256854979)
  ·
    refine ⟨56946237541588161385282469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37964158361058774256854979 56946237541588161385282469)
    ·
      refine ⟨10677419539047780259740463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56946237541588161385282469 10677419539047780259740463)
      ·
        refine ⟨16016129308571670389610695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10677419539047780259740463 16016129308571670389610695)
        ·
          refine ⟨24024193962857505584416043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16016129308571670389610695 24024193962857505584416043)
          ·
            refine ⟨36036290944286258376624065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24024193962857505584416043 36036290944286258376624065)
            ·
              refine ⟨27027218208214693782468049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36036290944286258376624065 27027218208214693782468049)
              ·
                refine ⟨20270413656161020336851037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27027218208214693782468049 20270413656161020336851037)
                ·
                  refine ⟨7601405121060382626319139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20270413656161020336851037 7601405121060382626319139)
                  ·
                    refine ⟨11402107681590573939478709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7601405121060382626319139 11402107681590573939478709)
                    ·
                      refine ⟨1068947595149116306826129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11402107681590573939478709 1068947595149116306826129)
                      ·
                        rfl

theorem cell23_2081768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_2081768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081768 prefixEnd_2081768 := by exact prefixLift 2081768
  have htrace : WordTrace (prefixWord ++ tailWord_2081768) baseStart_2081768 baseEnd_2081768 := by
    simpa [prefixWord, tailWord_2081768, baseEnd_2081768] using wordTrace_append hprefix tailTrace_2081768
  have hstable : (prefixWord ++ tailWord_2081768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081768).length < 2 ^ (prefixWord ++ tailWord_2081768).sum := by decide
  have hdescent : baseEnd_2081768 < baseStart_2081768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081818 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 2, 7]
def baseStart_2081818 : Nat := 118140960795 + 2081818 * 2 ^ 59
def prefixEnd_2081818 : Nat := 4983230072969 + 3 ^ 40 * 2081818 * 2
def baseEnd_2081818 : Nat := 356324423060613703733633

theorem tailTrace_2081818 : CollatzResearch.WordTrace tailWord_2081818 prefixEnd_2081818 356324423060613703733633 := by
  unfold tailWord_2081818
  simp only [CollatzResearch.WordTrace]
  refine ⟨18982535092984101763257527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50620093581290938035353405 18982535092984101763257527)
  ·
    refine ⟨28473802639476152644886291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18982535092984101763257527 28473802639476152644886291)
    ·
      refine ⟨42710703959214228967329437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28473802639476152644886291 42710703959214228967329437)
      ·
        refine ⟨16016513984705335862748539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42710703959214228967329437 16016513984705335862748539)
        ·
          refine ⟨24024770977058003794122809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16016513984705335862748539 24024770977058003794122809)
          ·
            refine ⟨18018578232793502845592107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24024770977058003794122809 18018578232793502845592107)
            ·
              refine ⟨27027867349190254268388161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18018578232793502845592107 27027867349190254268388161)
              ·
                refine ⟨20270900511892690701291121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27027867349190254268388161 20270900511892690701291121)
                ·
                  refine ⟨15203175383919518025968341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20270900511892690701291121 15203175383919518025968341)
                  ·
                    refine ⟨356324423060613703733633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15203175383919518025968341 356324423060613703733633)
                    ·
                      rfl

theorem cell23_2081818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_2081818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081818 prefixEnd_2081818 := by exact prefixLift 2081818
  have htrace : WordTrace (prefixWord ++ tailWord_2081818) baseStart_2081818 baseEnd_2081818 := by
    simpa [prefixWord, tailWord_2081818, baseEnd_2081818] using wordTrace_append hprefix tailTrace_2081818
  have hstable : (prefixWord ++ tailWord_2081818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081818).length < 2 ^ (prefixWord ++ tailWord_2081818).sum := by decide
  have hdescent : baseEnd_2081818 < baseStart_2081818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081849 : List Nat := [1, 2, 1, 5, 2, 1, 3, 2, 2, 1, 3]
def baseStart_2081849 : Nat := 118140960795 + 2081849 * 2 ^ 59
def prefixEnd_2081849 : Nat := 4983230072969 + 3 ^ 40 * 2081849 * 2
def baseEnd_2081849 : Nat := 1068989187082130489913257

theorem tailTrace_2081849 : CollatzResearch.WordTrace tailWord_2081849 prefixEnd_2081849 1068989187082130489913257 := by
  unfold tailWord_2081849
  simp only [CollatzResearch.WordTrace]
  refine ⟨75931271034824099347408601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50620847356549399564939067 75931271034824099347408601)
  ·
    refine ⟨56948453276118074510556451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75931271034824099347408601 56948453276118074510556451)
    ·
      refine ⟨85422679914177111765834677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56948453276118074510556451 85422679914177111765834677)
      ·
        refine ⟨8008376241954104228047001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85422679914177111765834677 8008376241954104228047001)
        ·
          refine ⟨6006282181465578171035251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8008376241954104228047001 6006282181465578171035251)
          ·
            refine ⟨9009423272198367256552877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6006282181465578171035251 9009423272198367256552877)
            ·
              refine ⟨3378533727074387721207329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9009423272198367256552877 3378533727074387721207329)
              ·
                refine ⟨2533900295305790790905497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3378533727074387721207329 2533900295305790790905497)
                ·
                  refine ⟨1900425221479343093179123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2533900295305790790905497 1900425221479343093179123)
                  ·
                    refine ⟨2850637832219014639768685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1900425221479343093179123 2850637832219014639768685)
                    ·
                      refine ⟨1068989187082130489913257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2850637832219014639768685 1068989187082130489913257)
                      ·
                        rfl

theorem cell23_2081849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_2081849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081849 prefixEnd_2081849 := by exact prefixLift 2081849
  have htrace : WordTrace (prefixWord ++ tailWord_2081849) baseStart_2081849 baseEnd_2081849 := by
    simpa [prefixWord, tailWord_2081849, baseEnd_2081849] using wordTrace_append hprefix tailTrace_2081849
  have hstable : (prefixWord ++ tailWord_2081849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081849).length < 2 ^ (prefixWord ++ tailWord_2081849).sum := by decide
  have hdescent : baseEnd_2081849 < baseStart_2081849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081905 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 2, 3, 3]
def baseStart_2081905 : Nat := 118140960795 + 2081905 * 2 ^ 59
def prefixEnd_2081905 : Nat := 4983230072969 + 3 ^ 40 * 2081905 * 2
def baseEnd_2081905 : Nat := 1069017941998782270812999

theorem tailTrace_2081905 : CollatzResearch.WordTrace tailWord_2081905 prefixEnd_2081905 1069017941998782270812999 := by
  unfold tailWord_2081905
  simp only [CollatzResearch.WordTrace]
  refine ⟨75933313522621220911447169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50622209015080813940964779 75933313522621220911447169)
  ·
    refine ⟨56949985141965915683585377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75933313522621220911447169 56949985141965915683585377)
    ·
      refine ⟨42712488856474436762689033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56949985141965915683585377 42712488856474436762689033)
      ·
        refine ⟨32034366642355827572016775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42712488856474436762689033 32034366642355827572016775)
        ·
          refine ⟨48051549963533741358025163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32034366642355827572016775 48051549963533741358025163)
          ·
            refine ⟨72077324945300612037037745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48051549963533741358025163 72077324945300612037037745)
            ·
              refine ⟨54057993708975459027778309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72077324945300612037037745 54057993708975459027778309)
              ·
                refine ⟨10135873820432898567708433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54057993708975459027778309 10135873820432898567708433)
                ·
                  refine ⟨7601905365324673925781325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10135873820432898567708433 7601905365324673925781325)
                  ·
                    refine ⟨2850714511996752722167997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7601905365324673925781325 2850714511996752722167997)
                    ·
                      refine ⟨1069017941998782270812999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2850714511996752722167997 1069017941998782270812999)
                      ·
                        rfl

theorem cell23_2081905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_2081905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081905 prefixEnd_2081905 := by exact prefixLift 2081905
  have htrace : WordTrace (prefixWord ++ tailWord_2081905) baseStart_2081905 baseEnd_2081905 := by
    simpa [prefixWord, tailWord_2081905, baseEnd_2081905] using wordTrace_append hprefix tailTrace_2081905
  have hstable : (prefixWord ++ tailWord_2081905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081905).length < 2 ^ (prefixWord ++ tailWord_2081905).sum := by decide
  have hdescent : baseEnd_2081905 < baseStart_2081905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2081995 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 3]
def baseStart_2081995 : Nat := 118140960795 + 2081995 * 2 ^ 59
def prefixEnd_2081995 : Nat := 4983230072969 + 3 ^ 40 * 2081995 * 2
def baseEnd_2081995 : Nat := 1069064155257686918687585

theorem tailTrace_2081995 : CollatzResearch.WordTrace tailWord_2081995 prefixEnd_2081995 1069064155257686918687585 := by
  unfold tailWord_2081995
  simp only [CollatzResearch.WordTrace]
  refine ⟨75936596092295166282223439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50624397394863444188148959 75936596092295166282223439)
  ·
    refine ⟨113904894138442749423335159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75936596092295166282223439 113904894138442749423335159)
    ·
      refine ⟨170857341207664124135002739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113904894138442749423335159 170857341207664124135002739)
      ·
        refine ⟨256286011811496186202504109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170857341207664124135002739 256286011811496186202504109)
        ·
          refine ⟨96107254429311069825939041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256286011811496186202504109 96107254429311069825939041)
          ·
            refine ⟨72080440821983302369454281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96107254429311069825939041 72080440821983302369454281)
            ·
              refine ⟨54060330616487476777090711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72080440821983302369454281 54060330616487476777090711)
              ·
                refine ⟨81090495924731215165636067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54060330616487476777090711 81090495924731215165636067)
                ·
                  refine ⟨121635743887096822748454101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81090495924731215165636067 121635743887096822748454101)
                  ·
                    refine ⟨2850837747353831783166893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 121635743887096822748454101 2850837747353831783166893)
                    ·
                      refine ⟨1069064155257686918687585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2850837747353831783166893 1069064155257686918687585)
                      ·
                        rfl

theorem cell23_2081995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 3].length) (baseStart_2081995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2081995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2081995 prefixEnd_2081995 := by exact prefixLift 2081995
  have htrace : WordTrace (prefixWord ++ tailWord_2081995) baseStart_2081995 baseEnd_2081995 := by
    simpa [prefixWord, tailWord_2081995, baseEnd_2081995] using wordTrace_append hprefix tailTrace_2081995
  have hstable : (prefixWord ++ tailWord_2081995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2081995).length < 2 ^ (prefixWord ++ tailWord_2081995).sum := by decide
  have hdescent : baseEnd_2081995 < baseStart_2081995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2081995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082046 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_2082046 : Nat := 118140960795 + 2082046 * 2 ^ 59
def prefixEnd_2082046 : Nat := 4983230072969 + 3 ^ 40 * 2082046 * 2
def baseEnd_2082046 : Nat := 1069090342771066219149851

theorem tailTrace_2082046 : CollatzResearch.WordTrace tailWord_2082046 prefixEnd_2082046 1069090342771066219149851 := by
  unfold tailWord_2082046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9492307026888800249041249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50625637476740267994886661 9492307026888800249041249)
  ·
    refine ⟨7119230270166600186780937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9492307026888800249041249 7119230270166600186780937)
    ·
      refine ⟨5339422702624950140085703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7119230270166600186780937 5339422702624950140085703)
      ·
        refine ⟨8009134053937425210128555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5339422702624950140085703 8009134053937425210128555)
        ·
          refine ⟨12013701080906137815192833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8009134053937425210128555 12013701080906137815192833)
          ·
            refine ⟨9010275810679603361394625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12013701080906137815192833 9010275810679603361394625)
            ·
              refine ⟨6757706858009702521045969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9010275810679603361394625 6757706858009702521045969)
              ·
                refine ⟨5068280143507276890784477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6757706858009702521045969 5068280143507276890784477)
                ·
                  refine ⟨1900605053815228834044179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5068280143507276890784477 1900605053815228834044179)
                  ·
                    refine ⟨2850907580722843251066269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1900605053815228834044179 2850907580722843251066269)
                    ·
                      refine ⟨1069090342771066219149851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2850907580722843251066269 1069090342771066219149851)
                      ·
                        rfl

theorem cell23_2082046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_2082046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082046 prefixEnd_2082046 := by exact prefixLift 2082046
  have htrace : WordTrace (prefixWord ++ tailWord_2082046) baseStart_2082046 baseEnd_2082046 := by
    simpa [prefixWord, tailWord_2082046, baseEnd_2082046] using wordTrace_append hprefix tailTrace_2082046
  have hstable : (prefixWord ++ tailWord_2082046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082046).length < 2 ^ (prefixWord ++ tailWord_2082046).sum := by decide
  have hdescent : baseEnd_2082046 < baseStart_2082046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082049 : List Nat := [1, 2, 4, 1, 1, 4, 2, 2, 1, 5]
def baseStart_2082049 : Nat := 118140960795 + 2082049 * 2 ^ 59
def prefixEnd_2082049 : Nat := 4983230072969 + 3 ^ 40 * 2082049 * 2
def baseEnd_2082049 : Nat := 356363961071009902470779

theorem tailTrace_2082049 : CollatzResearch.WordTrace tailWord_2082049 prefixEnd_2082049 356363961071009902470779 := by
  unfold tailWord_2082049
  simp only [CollatzResearch.WordTrace]
  refine ⟨75938565634099533504689201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50625710422733022336459467 75938565634099533504689201)
  ·
    refine ⟨56953924225574650128516901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75938565634099533504689201 56953924225574650128516901)
    ·
      refine ⟨10678860792295246899096919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56953924225574650128516901 10678860792295246899096919)
      ·
        refine ⟨16018291188442870348645379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10678860792295246899096919 16018291188442870348645379)
        ·
          refine ⟨24027436782664305522968069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16018291188442870348645379 24027436782664305522968069)
          ·
            refine ⟨4505144396749557285556513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24027436782664305522968069 4505144396749557285556513)
            ·
              refine ⟨3378858297562167964167385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4505144396749557285556513 3378858297562167964167385)
              ·
                refine ⟨2534143723171625973125539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3378858297562167964167385 2534143723171625973125539)
                ·
                  refine ⟨3801215584757438959688309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534143723171625973125539 3801215584757438959688309)
                  ·
                    refine ⟨356363961071009902470779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3801215584757438959688309 356363961071009902470779)
                    ·
                      rfl

theorem cell23_2082049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_2082049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082049 prefixEnd_2082049 := by exact prefixLift 2082049
  have htrace : WordTrace (prefixWord ++ tailWord_2082049) baseStart_2082049 baseEnd_2082049 := by
    simpa [prefixWord, tailWord_2082049, baseEnd_2082049] using wordTrace_append hprefix tailTrace_2082049
  have hstable : (prefixWord ++ tailWord_2082049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082049).length < 2 ^ (prefixWord ++ tailWord_2082049).sum := by decide
  have hdescent : baseEnd_2082049 < baseStart_2082049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082072 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_2082072 : Nat := 118140960795 + 2082072 * 2 ^ 59
def prefixEnd_2082072 : Nat := 4983230072969 + 3 ^ 40 * 2082072 * 2
def baseEnd_2082072 : Nat := 1069103693268083117424731

theorem tailTrace_2082072 : CollatzResearch.WordTrace tailWord_2082072 prefixEnd_2082072 1069103693268083117424731 := by
  unfold tailWord_2082072
  simp only [CollatzResearch.WordTrace]
  refine ⟨37969702256508104216388235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50626269675344138955184313 37969702256508104216388235)
  ·
    refine ⟨56954553384762156324582353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37969702256508104216388235 56954553384762156324582353)
    ·
      refine ⟨42715915038571617243436765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56954553384762156324582353 42715915038571617243436765)
      ·
        refine ⟨16018468139464356466288787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42715915038571617243436765 16018468139464356466288787)
        ·
          refine ⟨24027702209196534699433181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16018468139464356466288787 24027702209196534699433181)
          ·
            refine ⟨9010388328448700512287443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24027702209196534699433181 9010388328448700512287443)
            ·
              refine ⟨13515582492673050768431165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9010388328448700512287443 13515582492673050768431165)
              ·
                refine ⟨5068343434752394038161687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13515582492673050768431165 5068343434752394038161687)
                ·
                  refine ⟨7602515152128591057242531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5068343434752394038161687 7602515152128591057242531)
                  ·
                    refine ⟨11403772728192886585863797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7602515152128591057242531 11403772728192886585863797)
                    ·
                      refine ⟨1069103693268083117424731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11403772728192886585863797 1069103693268083117424731)
                      ·
                        rfl

theorem cell23_2082072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_2082072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082072 prefixEnd_2082072 := by exact prefixLift 2082072
  have htrace : WordTrace (prefixWord ++ tailWord_2082072) baseStart_2082072 baseEnd_2082072 := by
    simpa [prefixWord, tailWord_2082072, baseEnd_2082072] using wordTrace_append hprefix tailTrace_2082072
  have hstable : (prefixWord ++ tailWord_2082072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082072).length < 2 ^ (prefixWord ++ tailWord_2082072).sum := by decide
  have hdescent : baseEnd_2082072 < baseStart_2082072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082080 : List Nat := [2, 1, 1, 5, 3, 1, 3, 2, 1, 1, 3]
def baseStart_2082080 : Nat := 118140960795 + 2082080 * 2 ^ 59
def prefixEnd_2082080 : Nat := 4983230072969 + 3 ^ 40 * 2082080 * 2
def baseEnd_2082080 : Nat := 1069107801113319086124695

theorem tailTrace_2082080 : CollatzResearch.WordTrace tailWord_2082080 prefixEnd_2082080 1069107801113319086124695 := by
  unfold tailWord_2082080
  simp only [CollatzResearch.WordTrace]
  refine ⟨37969848148493612899533847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50626464197991483866045129 37969848148493612899533847)
  ·
    refine ⟨56954772222740419349300771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37969848148493612899533847 56954772222740419349300771)
    ·
      refine ⟨85432158334110629023951157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56954772222740419349300771 85432158334110629023951157)
      ·
        refine ⟨8009264843822871470995421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85432158334110629023951157 8009264843822871470995421)
        ·
          refine ⟨3003474316433576801623283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8009264843822871470995421 3003474316433576801623283)
          ·
            refine ⟨4505211474650365202434925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003474316433576801623283 4505211474650365202434925)
            ·
              refine ⟨1689454302993886950913097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4505211474650365202434925 1689454302993886950913097)
              ·
                refine ⟨1267090727245415213184823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1689454302993886950913097 1267090727245415213184823)
                ·
                  refine ⟨1900636090868122819777235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267090727245415213184823 1900636090868122819777235)
                  ·
                    refine ⟨2850954136302184229665853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1900636090868122819777235 2850954136302184229665853)
                    ·
                      refine ⟨1069107801113319086124695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2850954136302184229665853 1069107801113319086124695)
                      ·
                        rfl

theorem cell23_2082080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_2082080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082080 prefixEnd_2082080 := by exact prefixLift 2082080
  have htrace : WordTrace (prefixWord ++ tailWord_2082080) baseStart_2082080 baseEnd_2082080 := by
    simpa [prefixWord, tailWord_2082080, baseEnd_2082080] using wordTrace_append hprefix tailTrace_2082080
  have hstable : (prefixWord ++ tailWord_2082080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082080).length < 2 ^ (prefixWord ++ tailWord_2082080).sum := by decide
  have hdescent : baseEnd_2082080 < baseStart_2082080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082095 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 6]
def baseStart_2082095 : Nat := 118140960795 + 2082095 * 2 ^ 59
def prefixEnd_2082095 : Nat := 4983230072969 + 3 ^ 40 * 2082095 * 2
def baseEnd_2082095 : Nat := 1069115503323136527437125

theorem tailTrace_2082095 : CollatzResearch.WordTrace tailWord_2082095 prefixEnd_2082095 1069115503323136527437125 := by
  unfold tailWord_2082095
  simp only [CollatzResearch.WordTrace]
  refine ⟨75940243391932883360863739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50626828927955255573909159 75940243391932883360863739)
  ·
    refine ⟨113910365087899325041295609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75940243391932883360863739 113910365087899325041295609)
    ·
      refine ⟨85432773815924493780971707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113910365087899325041295609 85432773815924493780971707)
      ·
        refine ⟨128149160723886740671457561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85432773815924493780971707 128149160723886740671457561)
        ·
          refine ⟨96111870542915055503593171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128149160723886740671457561 96111870542915055503593171)
          ·
            refine ⟨144167805814372583255389757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96111870542915055503593171 144167805814372583255389757)
            ·
              refine ⟨54062927180389718720771159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144167805814372583255389757 54062927180389718720771159)
              ·
                refine ⟨81094390770584578081156739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54062927180389718720771159 81094390770584578081156739)
                ·
                  refine ⟨121641586155876867121735109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81094390770584578081156739 121641586155876867121735109)
                  ·
                    refine ⟨22807797404226912585325333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121641586155876867121735109 22807797404226912585325333)
                    ·
                      refine ⟨1069115503323136527437125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22807797404226912585325333 1069115503323136527437125)
                      ·
                        rfl

theorem cell23_2082095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_2082095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082095 prefixEnd_2082095 := by exact prefixLift 2082095
  have htrace : WordTrace (prefixWord ++ tailWord_2082095) baseStart_2082095 baseEnd_2082095 := by
    simpa [prefixWord, tailWord_2082095, baseEnd_2082095] using wordTrace_append hprefix tailTrace_2082095
  have hstable : (prefixWord ++ tailWord_2082095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082095).length < 2 ^ (prefixWord ++ tailWord_2082095).sum := by decide
  have hdescent : baseEnd_2082095 < baseStart_2082095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082116 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2082116 : Nat := 118140960795 + 2082116 * 2 ^ 59
def prefixEnd_2082116 : Nat := 4983230072969 + 3 ^ 40 * 2082116 * 2
def baseEnd_2082116 : Nat := 1069126286416880945274529

theorem tailTrace_2082116 : CollatzResearch.WordTrace tailWord_2082116 prefixEnd_2082116 1069126286416880945274529 := by
  unfold tailWord_2082116
  simp only [CollatzResearch.WordTrace]
  refine ⟨37970504662428401973689101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50627339549904535964918801 37970504662428401973689101)
  ·
    refine ⟨14238939248410650740133413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37970504662428401973689101 14238939248410650740133413)
    ·
      refine ⟨2669801109076997013775015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14238939248410650740133413 2669801109076997013775015)
      ·
        refine ⟨4004701663615495520662523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2669801109076997013775015 4004701663615495520662523)
        ·
          refine ⟨6007052495423243280993785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4004701663615495520662523 6007052495423243280993785)
          ·
            refine ⟨4505289371567432460745339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6007052495423243280993785 4505289371567432460745339)
            ·
              refine ⟨6757934057351148691118009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505289371567432460745339 6757934057351148691118009)
              ·
                refine ⟨5068450543013361518338507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6757934057351148691118009 5068450543013361518338507)
                ·
                  refine ⟨7602675814520042277507761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5068450543013361518338507 7602675814520042277507761)
                  ·
                    refine ⟨5702006860890031708130821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7602675814520042277507761 5702006860890031708130821)
                    ·
                      refine ⟨1069126286416880945274529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5702006860890031708130821 1069126286416880945274529)
                      ·
                        rfl

theorem cell23_2082116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2082116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082116 prefixEnd_2082116 := by exact prefixLift 2082116
  have htrace : WordTrace (prefixWord ++ tailWord_2082116) baseStart_2082116 baseEnd_2082116 := by
    simpa [prefixWord, tailWord_2082116, baseEnd_2082116] using wordTrace_append hprefix tailTrace_2082116
  have hstable : (prefixWord ++ tailWord_2082116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082116).length < 2 ^ (prefixWord ++ tailWord_2082116).sum := by decide
  have hdescent : baseEnd_2082116 < baseStart_2082116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082119 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_2082119 : Nat := 118140960795 + 2082119 * 2 ^ 59
def prefixEnd_2082119 : Nat := 4983230072969 + 3 ^ 40 * 2082119 * 2
def baseEnd_2082119 : Nat := 1069127826858844433537015

theorem tailTrace_2082119 : CollatzResearch.WordTrace tailWord_2082119 prefixEnd_2082119 1069127826858844433537015 := by
  unfold tailWord_2082119
  simp only [CollatzResearch.WordTrace]
  refine ⟨75941118743845935459737411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50627412495897290306491607 75941118743845935459737411)
  ·
    refine ⟨113911678115768903189606117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75941118743845935459737411 113911678115768903189606117)
    ·
      refine ⟨21358439646706669348051147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113911678115768903189606117 21358439646706669348051147)
      ·
        refine ⟨32037659470060004022076721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21358439646706669348051147 32037659470060004022076721)
        ·
          refine ⟨24028244602545003016557541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32037659470060004022076721 24028244602545003016557541)
          ·
            refine ⟨4505295862977188065604539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24028244602545003016557541 4505295862977188065604539)
            ·
              refine ⟨6757943794465782098406809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505295862977188065604539 6757943794465782098406809)
              ·
                refine ⟨5068457845849336573805107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6757943794465782098406809 5068457845849336573805107)
                ·
                  refine ⟨7602686768774004860707661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5068457845849336573805107 7602686768774004860707661)
                  ·
                    refine ⟨2851007538290251822765373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7602686768774004860707661 2851007538290251822765373)
                    ·
                      refine ⟨1069127826858844433537015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2851007538290251822765373 1069127826858844433537015)
                      ·
                        rfl

theorem cell23_2082119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_2082119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082119 prefixEnd_2082119 := by exact prefixLift 2082119
  have htrace : WordTrace (prefixWord ++ tailWord_2082119) baseStart_2082119 baseEnd_2082119 := by
    simpa [prefixWord, tailWord_2082119, baseEnd_2082119] using wordTrace_append hprefix tailTrace_2082119
  have hstable : (prefixWord ++ tailWord_2082119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082119).length < 2 ^ (prefixWord ++ tailWord_2082119).sum := by decide
  have hdescent : baseEnd_2082119 < baseStart_2082119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082136 : List Nat := [2, 1, 2, 2, 1, 1, 6, 2, 2, 1, 3]
def baseStart_2082136 : Nat := 118140960795 + 2082136 * 2 ^ 59
def prefixEnd_2082136 : Nat := 4983230072969 + 3 ^ 40 * 2082136 * 2
def baseEnd_2082136 : Nat := 1069136556029970867024437

theorem tailTrace_2082136 : CollatzResearch.WordTrace tailWord_2082136 prefixEnd_2082136 1069136556029970867024437 := by
  unfold tailWord_2082136
  simp only [CollatzResearch.WordTrace]
  refine ⟨37970869392392173681553131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50627825856522898242070841 37970869392392173681553131)
  ·
    refine ⟨56956304088588260522329697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37970869392392173681553131 56956304088588260522329697)
    ·
      refine ⟨42717228066441195391747273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56956304088588260522329697 42717228066441195391747273)
      ·
        refine ⟨32037921049830896543810455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42717228066441195391747273 32037921049830896543810455)
        ·
          refine ⟨48056881574746344815715683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32037921049830896543810455 48056881574746344815715683)
          ·
            refine ⟨72085322362119517223573525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48056881574746344815715683 72085322362119517223573525)
            ·
              refine ⟨3378999485724352369855009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72085322362119517223573525 3378999485724352369855009)
              ·
                refine ⟨2534249614293264277391257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3378999485724352369855009 2534249614293264277391257)
                ·
                  refine ⟨1900687210719948208043443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2534249614293264277391257 1900687210719948208043443)
                  ·
                    refine ⟨2851030816079922312065165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1900687210719948208043443 2851030816079922312065165)
                    ·
                      refine ⟨1069136556029970867024437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2851030816079922312065165 1069136556029970867024437)
                      ·
                        rfl

theorem cell23_2082136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_2082136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082136 prefixEnd_2082136 := by exact prefixLift 2082136
  have htrace : WordTrace (prefixWord ++ tailWord_2082136) baseStart_2082136 baseEnd_2082136 := by
    simpa [prefixWord, tailWord_2082136, baseEnd_2082136] using wordTrace_append hprefix tailTrace_2082136
  have hstable : (prefixWord ++ tailWord_2082136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082136).length < 2 ^ (prefixWord ++ tailWord_2082136).sum := by decide
  have hdescent : baseEnd_2082136 < baseStart_2082136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082146 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_2082146 : Nat := 118140960795 + 2082146 * 2 ^ 59
def prefixEnd_2082146 : Nat := 4983230072969 + 3 ^ 40 * 2082146 * 2
def baseEnd_2082146 : Nat := 1069141690836515827899391

theorem tailTrace_2082146 : CollatzResearch.WordTrace tailWord_2082146 prefixEnd_2082146 1069141690836515827899391 := by
  unfold tailWord_2082146
  simp only [CollatzResearch.WordTrace]
  refine ⟨18985525878687029767742573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50628069009832079380646861 18985525878687029767742573)
  ·
    refine ⟨7119572204507636162903465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18985525878687029767742573 7119572204507636162903465)
    ·
      refine ⟨5339679153380727122177599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7119572204507636162903465 5339679153380727122177599)
      ·
        refine ⟨8009518730071090683266399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5339679153380727122177599 8009518730071090683266399)
        ·
          refine ⟨12014278095106636024899599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8009518730071090683266399 12014278095106636024899599)
          ·
            refine ⟨18021417142659954037349399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12014278095106636024899599 18021417142659954037349399)
            ·
              refine ⟨27032125713989931056024099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18021417142659954037349399 27032125713989931056024099)
              ·
                refine ⟨40548188570984896584036149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27032125713989931056024099 40548188570984896584036149)
                ·
                  refine ⟨3801392678529834054753389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40548188570984896584036149 3801392678529834054753389)
                  ·
                    refine ⟨1425522254448687770532521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3801392678529834054753389 1425522254448687770532521)
                    ·
                      refine ⟨1069141690836515827899391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1425522254448687770532521 1069141690836515827899391)
                      ·
                        rfl

theorem cell23_2082146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_2082146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082146 prefixEnd_2082146 := by exact prefixLift 2082146
  have htrace : WordTrace (prefixWord ++ tailWord_2082146) baseStart_2082146 baseEnd_2082146 := by
    simpa [prefixWord, tailWord_2082146, baseEnd_2082146] using wordTrace_append hprefix tailTrace_2082146
  have hstable : (prefixWord ++ tailWord_2082146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082146).length < 2 ^ (prefixWord ++ tailWord_2082146).sum := by decide
  have hdescent : baseEnd_2082146 < baseStart_2082146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082172 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_2082172 : Nat := 118140960795 + 2082172 * 2 ^ 59
def prefixEnd_2082172 : Nat := 4983230072969 + 3 ^ 40 * 2082172 * 2
def baseEnd_2082172 : Nat := 1069155041333532726174271

theorem tailTrace_2082172 : CollatzResearch.WordTrace tailWord_2082172 prefixEnd_2082172 1069155041333532726174271 := by
  unfold tailWord_2082172
  simp only [CollatzResearch.WordTrace]
  refine ⟨37971525906326962755708385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50628701208435950340944513 37971525906326962755708385)
  ·
    refine ⟨28478644429745222066781289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37971525906326962755708385 28478644429745222066781289)
    ·
      refine ⟨21358983322308916550085967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28478644429745222066781289 21358983322308916550085967)
      ·
        refine ⟨32038474983463374825128951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21358983322308916550085967 32038474983463374825128951)
        ·
          refine ⟨48057712475195062237693427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32038474983463374825128951 48057712475195062237693427)
          ·
            refine ⟨72086568712792593356540141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48057712475195062237693427 72086568712792593356540141)
            ·
              refine ⟨27032463267297222508702553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72086568712792593356540141 27032463267297222508702553)
              ·
                refine ⟨20274347450472916881526915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27032463267297222508702553 20274347450472916881526915)
                ·
                  refine ⟨30411521175709375322290373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20274347450472916881526915 30411521175709375322290373)
                  ·
                    refine ⟨5702160220445507872929445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30411521175709375322290373 5702160220445507872929445)
                    ·
                      refine ⟨1069155041333532726174271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5702160220445507872929445 1069155041333532726174271)
                      ·
                        rfl

theorem cell23_2082172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_2082172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082172 prefixEnd_2082172 := by exact prefixLift 2082172
  have htrace : WordTrace (prefixWord ++ tailWord_2082172) baseStart_2082172 baseEnd_2082172 := by
    simpa [prefixWord, tailWord_2082172, baseEnd_2082172] using wordTrace_append hprefix tailTrace_2082172
  have hstable : (prefixWord ++ tailWord_2082172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082172).length < 2 ^ (prefixWord ++ tailWord_2082172).sum := by decide
  have hdescent : baseEnd_2082172 < baseStart_2082172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082174 : List Nat := [4, 2, 3, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2082174 : Nat := 118140960795 + 2082174 * 2 ^ 59
def prefixEnd_2082174 : Nat := 4983230072969 + 3 ^ 40 * 2082174 * 2
def baseEnd_2082174 : Nat := 1069156068294841718349263

theorem tailTrace_2082174 : CollatzResearch.WordTrace tailWord_2082174 prefixEnd_2082174 1069156068294841718349263 := by
  unfold tailWord_2082174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9492890594830834981623697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50628749839097786568659717 9492890594830834981623697)
  ·
    refine ⟨7119667946123126236217773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9492890594830834981623697 7119667946123126236217773)
    ·
      refine ⟨2669875479796172338581665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7119667946123126236217773 2669875479796172338581665)
      ·
        refine ⟨2002406609847129253936249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2669875479796172338581665 2002406609847129253936249)
        ·
          refine ⟨1501804957385346940452187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2002406609847129253936249 1501804957385346940452187)
          ·
            refine ⟨2252707436078020410678281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501804957385346940452187 2252707436078020410678281)
            ·
              refine ⟨1689530577058515308008711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2252707436078020410678281 1689530577058515308008711)
              ·
                refine ⟨2534295865587772962013067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689530577058515308008711 2534295865587772962013067)
                ·
                  refine ⟨3801443798381659443019601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534295865587772962013067 3801443798381659443019601)
                  ·
                    refine ⟨2851082848786244582264701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3801443798381659443019601 2851082848786244582264701)
                    ·
                      refine ⟨1069156068294841718349263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2851082848786244582264701 1069156068294841718349263)
                      ·
                        rfl

theorem cell23_2082174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2082174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082174 prefixEnd_2082174 := by exact prefixLift 2082174
  have htrace : WordTrace (prefixWord ++ tailWord_2082174) baseStart_2082174 baseEnd_2082174 := by
    simpa [prefixWord, tailWord_2082174, baseEnd_2082174] using wordTrace_append hprefix tailTrace_2082174
  have hstable : (prefixWord ++ tailWord_2082174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082174).length < 2 ^ (prefixWord ++ tailWord_2082174).sum := by decide
  have hdescent : baseEnd_2082174 < baseStart_2082174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082180 : List Nat := [2, 3, 2, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_2082180 : Nat := 118140960795 + 2082180 * 2 ^ 59
def prefixEnd_2082180 : Nat := 4983230072969 + 3 ^ 40 * 2082180 * 2
def baseEnd_2082180 : Nat := 1069159149178768694874235

theorem tailTrace_2082180 : CollatzResearch.WordTrace tailWord_2082180 prefixEnd_2082180 1069159149178768694874235 := by
  unfold tailWord_2082180
  simp only [CollatzResearch.WordTrace]
  refine ⟨37971671798312471438853997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50628895731083295251805329 37971671798312471438853997)
  ·
    refine ⟨14239376924367176789570249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37971671798312471438853997 14239376924367176789570249)
    ·
      refine ⟨10679532693275382592177687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14239376924367176789570249 10679532693275382592177687)
      ·
        refine ⟨16019299039913073888266531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10679532693275382592177687 16019299039913073888266531)
        ·
          refine ⟨24028948559869610832399797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16019299039913073888266531 24028948559869610832399797)
          ·
            refine ⟨2252713927487776015537481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24028948559869610832399797 2252713927487776015537481)
            ·
              refine ⟨1689535445615832011653111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2252713927487776015537481 1689535445615832011653111)
              ·
                refine ⟨2534303168423748017479667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689535445615832011653111 2534303168423748017479667)
                ·
                  refine ⟨3801454752635622026219501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534303168423748017479667 3801454752635622026219501)
                  ·
                    refine ⟨1425545532238358259832313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3801454752635622026219501 1425545532238358259832313)
                    ·
                      refine ⟨1069159149178768694874235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1425545532238358259832313 1069159149178768694874235)
                      ·
                        rfl

theorem cell23_2082180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_2082180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082180 prefixEnd_2082180 := by exact prefixLift 2082180
  have htrace : WordTrace (prefixWord ++ tailWord_2082180) baseStart_2082180 baseEnd_2082180 := by
    simpa [prefixWord, tailWord_2082180, baseEnd_2082180] using wordTrace_append hprefix tailTrace_2082180
  have hstable : (prefixWord ++ tailWord_2082180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082180).length < 2 ^ (prefixWord ++ tailWord_2082180).sum := by decide
  have hdescent : baseEnd_2082180 < baseStart_2082180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082229 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 1, 7]
def baseStart_2082229 : Nat := 118140960795 + 2082229 * 2 ^ 59
def prefixEnd_2082229 : Nat := 4983230072969 + 3 ^ 40 * 2082229 * 2
def baseEnd_2082229 : Nat := 356394769910279667720503

theorem tailTrace_2082229 : CollatzResearch.WordTrace tailWord_2082229 prefixEnd_2082229 356394769910279667720503 := by
  unfold tailWord_2082229
  simp only [CollatzResearch.WordTrace]
  refine ⟨75945130773447424246241741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50630087182298282830827827 75945130773447424246241741)
  ·
    refine ⟨28479424040042784092340653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75945130773447424246241741 28479424040042784092340653)
    ·
      refine ⟨10679784015016044034627745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28479424040042784092340653 10679784015016044034627745)
      ·
        refine ⟨8009838011262033025970809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10679784015016044034627745 8009838011262033025970809)
        ·
          refine ⟨6007378508446524769478107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8009838011262033025970809 6007378508446524769478107)
          ·
            refine ⟨9011067762669787154217161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6007378508446524769478107 9011067762669787154217161)
            ·
              refine ⟨6758300822002340365662871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9011067762669787154217161 6758300822002340365662871)
              ·
                refine ⟨10137451233003510548494307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758300822002340365662871 10137451233003510548494307)
                ·
                  refine ⟨15206176849505265822741461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10137451233003510548494307 15206176849505265822741461)
                  ·
                    refine ⟨356394769910279667720503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15206176849505265822741461 356394769910279667720503)
                    ·
                      rfl

theorem cell23_2082229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_2082229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082229 prefixEnd_2082229 := by exact prefixLift 2082229
  have htrace : WordTrace (prefixWord ++ tailWord_2082229) baseStart_2082229 baseEnd_2082229 := by
    simpa [prefixWord, tailWord_2082229, baseEnd_2082229] using wordTrace_append hprefix tailTrace_2082229
  have hstable : (prefixWord ++ tailWord_2082229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082229).length < 2 ^ (prefixWord ++ tailWord_2082229).sum := by decide
  have hdescent : baseEnd_2082229 < baseStart_2082229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082233 : List Nat := [1, 2, 1, 4, 4, 2, 1, 3, 5]
def baseStart_2082233 : Nat := 118140960795 + 2082233 * 2 ^ 59
def prefixEnd_2082233 : Nat := 4983230072969 + 3 ^ 40 * 2082233 * 2
def baseEnd_2082233 : Nat := 118798484850384109723499

theorem tailTrace_2082233 : CollatzResearch.WordTrace tailWord_2082233 prefixEnd_2082233 118798484850384109723499 := by
  unfold tailWord_2082233
  simp only [CollatzResearch.WordTrace]
  refine ⟨75945276665432932929387353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50630184443621955286258235 75945276665432932929387353)
  ·
    refine ⟨56958957499074699697040515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75945276665432932929387353 56958957499074699697040515)
    ·
      refine ⟨85438436248612049545560773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56958957499074699697040515 85438436248612049545560773)
      ·
        refine ⟨16019706796614759289792645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85438436248612049545560773 16019706796614759289792645)
        ·
          refine ⟨3003695024365267366836121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16019706796614759289792645 3003695024365267366836121)
          ·
            refine ⟨2252771268273950525127091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3003695024365267366836121 2252771268273950525127091)
            ·
              refine ⟨3379156902410925787690637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2252771268273950525127091 3379156902410925787690637)
              ·
                refine ⟨1267183838404097170383989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3379156902410925787690637 1267183838404097170383989)
                ·
                  refine ⟨118798484850384109723499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1267183838404097170383989 118798484850384109723499)
                  ·
                    rfl

theorem cell23_2082233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 5].length) (baseStart_2082233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082233 prefixEnd_2082233 := by exact prefixLift 2082233
  have htrace : WordTrace (prefixWord ++ tailWord_2082233) baseStart_2082233 baseEnd_2082233 := by
    simpa [prefixWord, tailWord_2082233, baseEnd_2082233] using wordTrace_append hprefix tailTrace_2082233
  have hstable : (prefixWord ++ tailWord_2082233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082233).length < 2 ^ (prefixWord ++ tailWord_2082233).sum := by decide
  have hdescent : baseEnd_2082233 < baseStart_2082233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082272 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 10]
def baseStart_2082272 : Nat := 118140960795 + 2082272 * 2 ^ 59
def prefixEnd_2082272 : Nat := 4983230072969 + 3 ^ 40 * 2082272 * 2
def baseEnd_2082272 : Nat := 118800709933220259435979

theorem tailTrace_2082272 : CollatzResearch.WordTrace tailWord_2082272 prefixEnd_2082272 118800709933220259435979 := by
  unfold tailWord_2082272
  simp only [CollatzResearch.WordTrace]
  refine ⟨37973349556145821295028535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50631132741527761726704713 37973349556145821295028535)
  ·
    refine ⟨56960024334218731942542803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37973349556145821295028535 56960024334218731942542803)
    ·
      refine ⟨85440036501328097913814205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56960024334218731942542803 85440036501328097913814205)
      ·
        refine ⟨32040013687998036717680327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85440036501328097913814205 32040013687998036717680327)
        ·
          refine ⟨48060020531997055076520491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32040013687998036717680327 48060020531997055076520491)
          ·
            refine ⟨72090030797995582614780737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48060020531997055076520491 72090030797995582614780737)
            ·
              refine ⟨54067523098496686961085553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72090030797995582614780737 54067523098496686961085553)
              ·
                refine ⟨40550642323872515220814165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54067523098496686961085553 40550642323872515220814165)
                ·
                  refine ⟨118800709933220259435979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 40550642323872515220814165 118800709933220259435979)
                  ·
                    rfl

theorem cell23_2082272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 10].length) (baseStart_2082272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082272 prefixEnd_2082272 := by exact prefixLift 2082272
  have htrace : WordTrace (prefixWord ++ tailWord_2082272) baseStart_2082272 baseEnd_2082272 := by
    simpa [prefixWord, tailWord_2082272, baseEnd_2082272] using wordTrace_append hprefix tailTrace_2082272
  have hstable : (prefixWord ++ tailWord_2082272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082272).length < 2 ^ (prefixWord ++ tailWord_2082272).sum := by decide
  have hdescent : baseEnd_2082272 < baseStart_2082272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082317 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_2082317 : Nat := 118140960795 + 2082317 * 2 ^ 59
def prefixEnd_2082317 : Nat := 4983230072969 + 3 ^ 40 * 2082317 * 2
def baseEnd_2082317 : Nat := 1069229496028434658861105

theorem tailTrace_2082317 : CollatzResearch.WordTrace tailWord_2082317 prefixEnd_2082317 1069229496028434658861105 := by
  unfold tailWord_2082317
  simp only [CollatzResearch.WordTrace]
  refine ⟨75948340397128615275445205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50632226931419076850296803 75948340397128615275445205)
  ·
    refine ⟨1780039228057701920518247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 75948340397128615275445205 1780039228057701920518247)
    ·
      refine ⟨2670058842086552880777371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1780039228057701920518247 2670058842086552880777371)
      ·
        refine ⟨4005088263129829321166057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670058842086552880777371 4005088263129829321166057)
        ·
          refine ⟨3003816197347371990874543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4005088263129829321166057 3003816197347371990874543)
          ·
            refine ⟨4505724296021057986311815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003816197347371990874543 4505724296021057986311815)
            ·
              refine ⟨6758586444031586979467723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505724296021057986311815 6758586444031586979467723)
              ·
                refine ⟨10137879666047380469201585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758586444031586979467723 10137879666047380469201585)
                ·
                  refine ⟨7603409749535535351901189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10137879666047380469201585 7603409749535535351901189)
                  ·
                    refine ⟨1425639328037912878481473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7603409749535535351901189 1425639328037912878481473)
                    ·
                      refine ⟨1069229496028434658861105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1425639328037912878481473 1069229496028434658861105)
                      ·
                        rfl

theorem cell23_2082317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_2082317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082317 prefixEnd_2082317 := by exact prefixLift 2082317
  have htrace : WordTrace (prefixWord ++ tailWord_2082317) baseStart_2082317 baseEnd_2082317 := by
    simpa [prefixWord, tailWord_2082317, baseEnd_2082317] using wordTrace_append hprefix tailTrace_2082317
  have hstable : (prefixWord ++ tailWord_2082317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082317).length < 2 ^ (prefixWord ++ tailWord_2082317).sum := by decide
  have hdescent : baseEnd_2082317 < baseStart_2082317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082333 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_2082333 : Nat := 118140960795 + 2082333 * 2 ^ 59
def prefixEnd_2082333 : Nat := 4983230072969 + 3 ^ 40 * 2082333 * 2
def baseEnd_2082333 : Nat := 1069237711718906596261031

theorem tailTrace_2082333 : CollatzResearch.WordTrace tailWord_2082333 prefixEnd_2082333 1069237711718906596261031 := by
  unfold tailWord_2082333
  simp only [CollatzResearch.WordTrace]
  refine ⟨75948923965070650008027653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50632615976713766672018435 75948923965070650008027653)
  ·
    refine ⟨14240423243450746876505185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75948923965070650008027653 14240423243450746876505185)
    ·
      refine ⟨10680317432588060157378889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14240423243450746876505185 10680317432588060157378889)
      ·
        refine ⟨8010238074441045118034167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10680317432588060157378889 8010238074441045118034167)
        ·
          refine ⟨12015357111661567677051251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8010238074441045118034167 12015357111661567677051251)
          ·
            refine ⟨18023035667492351515576877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12015357111661567677051251 18023035667492351515576877)
            ·
              refine ⟨6758638375309631818341329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18023035667492351515576877 6758638375309631818341329)
              ·
                refine ⟨5068978781482223863755997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6758638375309631818341329 5068978781482223863755997)
                ·
                  refine ⟨1900867043055833948908499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5068978781482223863755997 1900867043055833948908499)
                  ·
                    refine ⟨2851300564583750923362749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1900867043055833948908499 2851300564583750923362749)
                    ·
                      refine ⟨1069237711718906596261031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2851300564583750923362749 1069237711718906596261031)
                      ·
                        rfl

theorem cell23_2082333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_2082333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082333 prefixEnd_2082333 := by exact prefixLift 2082333
  have htrace : WordTrace (prefixWord ++ tailWord_2082333) baseStart_2082333 baseEnd_2082333 := by
    simpa [prefixWord, tailWord_2082333, baseEnd_2082333] using wordTrace_append hprefix tailTrace_2082333
  have hstable : (prefixWord ++ tailWord_2082333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082333).length < 2 ^ (prefixWord ++ tailWord_2082333).sum := by decide
  have hdescent : baseEnd_2082333 < baseStart_2082333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082334 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2082334 : Nat := 118140960795 + 2082334 * 2 ^ 59
def prefixEnd_2082334 : Nat := 4983230072969 + 3 ^ 40 * 2082334 * 2
def baseEnd_2082334 : Nat := 1069238225199561092348527

theorem tailTrace_2082334 : CollatzResearch.WordTrace tailWord_2082334 prefixEnd_2082334 1069238225199561092348527 := by
  unfold tailWord_2082334
  simp only [CollatzResearch.WordTrace]
  refine ⟨9493620054758378397351757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50632640292044684785876037 9493620054758378397351757)
  ·
    refine ⟨3560107520534391899006909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9493620054758378397351757 3560107520534391899006909)
    ·
      refine ⟨1335040320200396962127591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3560107520534391899006909 1335040320200396962127591)
      ·
        refine ⟨2002560480300595443191387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335040320200396962127591 2002560480300595443191387)
        ·
          refine ⟨3003840720450893164787081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002560480300595443191387 3003840720450893164787081)
          ·
            refine ⟨2252880540338169873590311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3003840720450893164787081 2252880540338169873590311)
            ·
              refine ⟨3379320810507254810385467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2252880540338169873590311 3379320810507254810385467)
              ·
                refine ⟨5068981215760882215578201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379320810507254810385467 5068981215760882215578201)
                ·
                  refine ⟨3801735911820661661683651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5068981215760882215578201 3801735911820661661683651)
                  ·
                    refine ⟨5702603867730992492525477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3801735911820661661683651 5702603867730992492525477)
                    ·
                      refine ⟨1069238225199561092348527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5702603867730992492525477 1069238225199561092348527)
                      ·
                        rfl

theorem cell23_2082334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2082334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082334 prefixEnd_2082334 := by exact prefixLift 2082334
  have htrace : WordTrace (prefixWord ++ tailWord_2082334) baseStart_2082334 baseEnd_2082334 := by
    simpa [prefixWord, tailWord_2082334, baseEnd_2082334] using wordTrace_append hprefix tailTrace_2082334
  have hstable : (prefixWord ++ tailWord_2082334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082334).length < 2 ^ (prefixWord ++ tailWord_2082334).sum := by decide
  have hdescent : baseEnd_2082334 < baseStart_2082334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082336 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 3, 5]
def baseStart_2082336 : Nat := 118140960795 + 2082336 * 2 ^ 59
def prefixEnd_2082336 : Nat := 4983230072969 + 3 ^ 40 * 2082336 * 2
def baseEnd_2082336 : Nat := 356413084053623361507839

theorem tailTrace_2082336 : CollatzResearch.WordTrace tailWord_2082336 prefixEnd_2082336 356413084053623361507839 := by
  unfold tailWord_2082336
  simp only [CollatzResearch.WordTrace]
  refine ⟨37974516692029890760193431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50632688922706521013591241 37974516692029890760193431)
  ·
    refine ⟨56961775038044836140290147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37974516692029890760193431 56961775038044836140290147)
    ·
      refine ⟨85442662557067254210435221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56961775038044836140290147 85442662557067254210435221)
      ·
        refine ⟨4005124807362527541114151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85442662557067254210435221 4005124807362527541114151)
        ·
          refine ⟨6007687211043791311671227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005124807362527541114151 6007687211043791311671227)
          ·
            refine ⟨9011530816565686967506841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6007687211043791311671227 9011530816565686967506841)
            ·
              refine ⟨6758648112424265225630131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9011530816565686967506841 6758648112424265225630131)
              ·
                refine ⟨10137972168636397838445197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758648112424265225630131 10137972168636397838445197)
                ·
                  refine ⟨3801739563238649189416949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10137972168636397838445197 3801739563238649189416949)
                  ·
                    refine ⟨356413084053623361507839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3801739563238649189416949 356413084053623361507839)
                    ·
                      rfl

theorem cell23_2082336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 3, 5].length) (baseStart_2082336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082336 prefixEnd_2082336 := by exact prefixLift 2082336
  have htrace : WordTrace (prefixWord ++ tailWord_2082336) baseStart_2082336 baseEnd_2082336 := by
    simpa [prefixWord, tailWord_2082336, baseEnd_2082336] using wordTrace_append hprefix tailTrace_2082336
  have hstable : (prefixWord ++ tailWord_2082336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082336).length < 2 ^ (prefixWord ++ tailWord_2082336).sum := by decide
  have hdescent : baseEnd_2082336 < baseStart_2082336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082386 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_2082386 : Nat := 118140960795 + 2082386 * 2 ^ 59
def prefixEnd_2082386 : Nat := 4983230072969 + 3 ^ 40 * 2082386 * 2
def baseEnd_2082386 : Nat := 1069264926193594888898287

theorem tailTrace_2082386 : CollatzResearch.WordTrace tailWord_2082386 prefixEnd_2082386 1069264926193594888898287 := by
  unfold tailWord_2082386
  simp only [CollatzResearch.WordTrace]
  refine ⟨18987714258469660014926753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50633904689252426706471341 18987714258469660014926753)
  ·
    refine ⟨14240785693852245011195065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18987714258469660014926753 14240785693852245011195065)
    ·
      refine ⟨10680589270389183758396299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14240785693852245011195065 10680589270389183758396299)
      ·
        refine ⟨16020883905583775637594449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10680589270389183758396299 16020883905583775637594449)
        ·
          refine ⟨12015662929187831728195837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16020883905583775637594449 12015662929187831728195837)
          ·
            refine ⟨4505873598445436898073439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12015662929187831728195837 4505873598445436898073439)
            ·
              refine ⟨6758810397668155347110159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505873598445436898073439 6758810397668155347110159)
              ·
                refine ⟨10138215596502233020665239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758810397668155347110159 10138215596502233020665239)
                ·
                  refine ⟨15207323394753349530997859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10138215596502233020665239 15207323394753349530997859)
                  ·
                    refine ⟨22810985092130024296496789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15207323394753349530997859 22810985092130024296496789)
                    ·
                      refine ⟨1069264926193594888898287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22810985092130024296496789 1069264926193594888898287)
                      ·
                        rfl

theorem cell23_2082386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_2082386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082386 prefixEnd_2082386 := by exact prefixLift 2082386
  have htrace : WordTrace (prefixWord ++ tailWord_2082386) baseStart_2082386 baseEnd_2082386 := by
    simpa [prefixWord, tailWord_2082386, baseEnd_2082386] using wordTrace_append hprefix tailTrace_2082386
  have hstable : (prefixWord ++ tailWord_2082386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082386).length < 2 ^ (prefixWord ++ tailWord_2082386).sum := by decide
  have hdescent : baseEnd_2082386 < baseStart_2082386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082396 : List Nat := [2, 2, 4, 1, 2, 2, 1, 9]
def baseStart_2082396 : Nat := 118140960795 + 2082396 * 2 ^ 59
def prefixEnd_2082396 : Nat := 4983230072969 + 3 ^ 40 * 2082396 * 2
def baseEnd_2082396 : Nat := 39602594851857031473083

theorem tailTrace_2082396 : CollatzResearch.WordTrace tailWord_2082396 prefixEnd_2082396 39602594851857031473083 := by
  unfold tailWord_2082396
  simp only [CollatzResearch.WordTrace]
  refine ⟨37975610881921205883785521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50634147842561607845047361 37975610881921205883785521)
  ·
    refine ⟨28481708161440904412839141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37975610881921205883785521 28481708161440904412839141)
    ·
      refine ⟨5340320280270169577407339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28481708161440904412839141 5340320280270169577407339)
      ·
        refine ⟨8010480420405254366111009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5340320280270169577407339 8010480420405254366111009)
        ·
          refine ⟨6007860315303940774583257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8010480420405254366111009 6007860315303940774583257)
          ·
            refine ⟨4505895236477955580937443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6007860315303940774583257 4505895236477955580937443)
            ·
              refine ⟨6758842854716933371406165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505895236477955580937443 6758842854716933371406165)
              ·
                refine ⟨39602594851857031473083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6758842854716933371406165 39602594851857031473083)
                ·
                  rfl

theorem cell23_2082396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 9].length) (baseStart_2082396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2082396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2082396 prefixEnd_2082396 := by exact prefixLift 2082396
  have htrace : WordTrace (prefixWord ++ tailWord_2082396) baseStart_2082396 baseEnd_2082396 := by
    simpa [prefixWord, tailWord_2082396, baseEnd_2082396] using wordTrace_append hprefix tailTrace_2082396
  have hstable : (prefixWord ++ tailWord_2082396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082396).length < 2 ^ (prefixWord ++ tailWord_2082396).sum := by decide
  have hdescent : baseEnd_2082396 < baseStart_2082396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
