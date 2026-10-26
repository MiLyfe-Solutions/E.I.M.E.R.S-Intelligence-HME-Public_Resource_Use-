import V185TrunkScan23Chunk0226

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1342653 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1342653 : Nat := 118140960795 + 1342653 * 2 ^ 59
def prefixEnd_1342653 : Nat := 4983230072969 + 3 ^ 40 * 1342653 * 2
def baseEnd_1342653 : Nat := 689426341201240597662757

theorem tailTrace_1342653 : CollatzResearch.WordTrace tailWord_1342653 prefixEnd_1342653 689426341201240597662757 := by
  unfold tailWord_1342653
  simp only [CollatzResearch.WordTrace]
  refine ⟨48970578004804962721456613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32647052003203308480971075 48970578004804962721456613)
  ·
    refine ⟨9181983375900930510273115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48970578004804962721456613 9181983375900930510273115)
    ·
      refine ⟨13772975063851395765409673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9181983375900930510273115 13772975063851395765409673)
      ·
        refine ⟨10329731297888546824057255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13772975063851395765409673 10329731297888546824057255)
        ·
          refine ⟨15494596946832820236085883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10329731297888546824057255 15494596946832820236085883)
          ·
            refine ⟨23241895420249230354128825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15494596946832820236085883 23241895420249230354128825)
            ·
              refine ⟨17431421565186922765596619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23241895420249230354128825 17431421565186922765596619)
              ·
                refine ⟨26147132347780384148394929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17431421565186922765596619 26147132347780384148394929)
                ·
                  refine ⟨19610349260835288111296197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26147132347780384148394929 19610349260835288111296197)
                  ·
                    refine ⟨3676940486406616520868037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19610349260835288111296197 3676940486406616520868037)
                    ·
                      refine ⟨689426341201240597662757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3676940486406616520868037 689426341201240597662757)
                      ·
                        rfl

theorem cell23_1342653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1342653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342653 prefixEnd_1342653 := by exact prefixLift 1342653
  have htrace : WordTrace (prefixWord ++ tailWord_1342653) baseStart_1342653 baseEnd_1342653 := by
    simpa [prefixWord, tailWord_1342653, baseEnd_1342653] using wordTrace_append hprefix tailTrace_1342653
  have hstable : (prefixWord ++ tailWord_1342653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342653).length < 2 ^ (prefixWord ++ tailWord_1342653).sum := by decide
  have hdescent : baseEnd_1342653 < baseStart_1342653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342657 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1342657 : Nat := 118140960795 + 1342657 * 2 ^ 59
def prefixEnd_1342657 : Nat := 4983230072969 + 3 ^ 40 * 1342657 * 2
def baseEnd_1342657 : Nat := 689428395123858582012739

theorem tailTrace_1342657 : CollatzResearch.WordTrace tailWord_1342657 prefixEnd_1342657 689428395123858582012739 := by
  unfold tailWord_1342657
  simp only [CollatzResearch.WordTrace]
  refine ⟨48970723896790471404602225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32647149264526980936401483 48970723896790471404602225)
  ·
    refine ⟨36728042922592853553451669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48970723896790471404602225 36728042922592853553451669)
    ·
      refine ⟨1721627011996540010318047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36728042922592853553451669 1721627011996540010318047)
      ·
        refine ⟨2582440517994810015477071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1721627011996540010318047 2582440517994810015477071)
        ·
          refine ⟨3873660776992215023215607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2582440517994810015477071 3873660776992215023215607)
          ·
            refine ⟨5810491165488322534823411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3873660776992215023215607 5810491165488322534823411)
            ·
              refine ⟨8715736748232483802235117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5810491165488322534823411 8715736748232483802235117)
              ·
                refine ⟨3268401280587181425838169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8715736748232483802235117 3268401280587181425838169)
                ·
                  refine ⟨2451300960440386069378627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3268401280587181425838169 2451300960440386069378627)
                  ·
                    refine ⟨3676951440660579104067941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2451300960440386069378627 3676951440660579104067941)
                    ·
                      refine ⟨689428395123858582012739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3676951440660579104067941 689428395123858582012739)
                      ·
                        rfl

theorem cell23_1342657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1342657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342657 prefixEnd_1342657 := by exact prefixLift 1342657
  have htrace : WordTrace (prefixWord ++ tailWord_1342657) baseStart_1342657 baseEnd_1342657 := by
    simpa [prefixWord, tailWord_1342657, baseEnd_1342657] using wordTrace_append hprefix tailTrace_1342657
  have hstable : (prefixWord ++ tailWord_1342657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342657).length < 2 ^ (prefixWord ++ tailWord_1342657).sum := by decide
  have hdescent : baseEnd_1342657 < baseStart_1342657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342677 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1342677 : Nat := 118140960795 + 1342677 * 2 ^ 59
def prefixEnd_1342677 : Nat := 4983230072969 + 3 ^ 40 * 1342677 * 2
def baseEnd_1342677 : Nat := 689438664736948503762647

theorem tailTrace_1342677 : CollatzResearch.WordTrace tailWord_1342677 prefixEnd_1342677 689438664736948503762647 := by
  unfold tailWord_1342677
  simp only [CollatzResearch.WordTrace]
  refine ⟨48971453356718014820330285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32647635571145343213553523 48971453356718014820330285)
  ·
    refine ⟨18364295008769255557623857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48971453356718014820330285 18364295008769255557623857)
    ·
      refine ⟨13773221256576941668217893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18364295008769255557623857 13773221256576941668217893)
      ·
        refine ⟨2582478985608176562790855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13773221256576941668217893 2582478985608176562790855)
        ·
          refine ⟨3873718478412264844186283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2582478985608176562790855 3873718478412264844186283)
          ·
            refine ⟨5810577717618397266279425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3873718478412264844186283 5810577717618397266279425)
            ·
              refine ⟨4357933288213797949709569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5810577717618397266279425 4357933288213797949709569)
              ·
                refine ⟨3268449966160348462282177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4357933288213797949709569 3268449966160348462282177)
                ·
                  refine ⟨2451337474620261346711633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3268449966160348462282177 2451337474620261346711633)
                  ·
                    refine ⟨1838503105965196010033725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2451337474620261346711633 1838503105965196010033725)
                    ·
                      refine ⟨689438664736948503762647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1838503105965196010033725 689438664736948503762647)
                      ·
                        rfl

theorem cell23_1342677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1342677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342677 prefixEnd_1342677 := by exact prefixLift 1342677
  have htrace : WordTrace (prefixWord ++ tailWord_1342677) baseStart_1342677 baseEnd_1342677 := by
    simpa [prefixWord, tailWord_1342677, baseEnd_1342677] using wordTrace_append hprefix tailTrace_1342677
  have hstable : (prefixWord ++ tailWord_1342677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342677).length < 2 ^ (prefixWord ++ tailWord_1342677).sum := by decide
  have hdescent : baseEnd_1342677 < baseStart_1342677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342707 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 3, 1, 3]
def baseStart_1342707 : Nat := 118140960795 + 1342707 * 2 ^ 59
def prefixEnd_1342707 : Nat := 4983230072969 + 3 ^ 40 * 1342707 * 2
def baseEnd_1342707 : Nat := 689454069156583386387509

theorem tailTrace_1342707 : CollatzResearch.WordTrace tailWord_1342707 prefixEnd_1342707 689454069156583386387509 := by
  unfold tailWord_1342707
  simp only [CollatzResearch.WordTrace]
  refine ⟨48972547546609329943922375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32648365031072886629281583 48972547546609329943922375)
  ·
    refine ⟨73458821319913994915883563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48972547546609329943922375 73458821319913994915883563)
    ·
      refine ⟨110188231979870992373825345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73458821319913994915883563 110188231979870992373825345)
      ·
        refine ⟨82641173984903244280369009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110188231979870992373825345 82641173984903244280369009)
        ·
          refine ⟨61980880488677433210276757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82641173984903244280369009 61980880488677433210276757)
          ·
            refine ⟨2905353772906754681731723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61980880488677433210276757 2905353772906754681731723)
            ·
              refine ⟨4358030659360132022597585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905353772906754681731723 4358030659360132022597585)
              ·
                refine ⟨3268522994520099016948189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4358030659360132022597585 3268522994520099016948189)
                ·
                  refine ⟨1225696122945037131355571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3268522994520099016948189 1225696122945037131355571)
                  ·
                    refine ⟨1838544184417555697033357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1225696122945037131355571 1838544184417555697033357)
                    ·
                      refine ⟨689454069156583386387509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1838544184417555697033357 689454069156583386387509)
                      ·
                        rfl

theorem cell23_1342707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 1, 3].length) (baseStart_1342707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342707 prefixEnd_1342707 := by exact prefixLift 1342707
  have htrace : WordTrace (prefixWord ++ tailWord_1342707) baseStart_1342707 baseEnd_1342707 := by
    simpa [prefixWord, tailWord_1342707, baseEnd_1342707] using wordTrace_append hprefix tailTrace_1342707
  have hstable : (prefixWord ++ tailWord_1342707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342707).length < 2 ^ (prefixWord ++ tailWord_1342707).sum := by decide
  have hdescent : baseEnd_1342707 < baseStart_1342707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342708 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1342708 : Nat := 118140960795 + 1342708 * 2 ^ 59
def prefixEnd_1342708 : Nat := 4983230072969 + 3 ^ 40 * 1342708 * 2
def baseEnd_1342708 : Nat := 689454582637237882475005

theorem tailTrace_1342708 : CollatzResearch.WordTrace tailWord_1342708 prefixEnd_1342708 689454582637237882475005 := by
  unfold tailWord_1342708
  simp only [CollatzResearch.WordTrace]
  refine ⟨24486292009802853557354389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32648389346403804743139185 24486292009802853557354389)
  ·
    refine ⟨1147794937959508760500987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24486292009802853557354389 1147794937959508760500987)
    ·
      refine ⟨1721692406939263140751481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1147794937959508760500987 1721692406939263140751481)
      ·
        refine ⟨1291269305204447355563611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1721692406939263140751481 1291269305204447355563611)
        ·
          refine ⟨1936903957806671033345417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291269305204447355563611 1936903957806671033345417)
          ·
            refine ⟨1452677968355003275009063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1936903957806671033345417 1452677968355003275009063)
            ·
              refine ⟨2179016952532504912513595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452677968355003275009063 2179016952532504912513595)
              ·
                refine ⟨3268525428798757368770393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179016952532504912513595 3268525428798757368770393)
                ·
                  refine ⟨2451394071599068026577795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3268525428798757368770393 2451394071599068026577795)
                  ·
                    refine ⟨3677091107398602039866693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2451394071599068026577795 3677091107398602039866693)
                    ·
                      refine ⟨689454582637237882475005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3677091107398602039866693 689454582637237882475005)
                      ·
                        rfl

theorem cell23_1342708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1342708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342708 prefixEnd_1342708 := by exact prefixLift 1342708
  have htrace : WordTrace (prefixWord ++ tailWord_1342708) baseStart_1342708 baseEnd_1342708 := by
    simpa [prefixWord, tailWord_1342708, baseEnd_1342708] using wordTrace_append hprefix tailTrace_1342708
  have hstable : (prefixWord ++ tailWord_1342708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342708).length < 2 ^ (prefixWord ++ tailWord_1342708).sum := by decide
  have hdescent : baseEnd_1342708 < baseStart_1342708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342753 : List Nat := [1, 2, 3, 2, 1, 1, 1, 12]
def baseStart_1342753 : Nat := 118140960795 + 1342753 * 2 ^ 59
def prefixEnd_1342753 : Nat := 4983230072969 + 3 ^ 40 * 1342753 * 2
def baseEnd_1342753 : Nat := 25536210713581118756011

theorem tailTrace_1342753 : CollatzResearch.WordTrace tailWord_1342753 prefixEnd_1342753 25536210713581118756011 := by
  unfold tailWord_1342753
  simp only [CollatzResearch.WordTrace]
  refine ⟨48974225304442679800096913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32649483536295119866731275 48974225304442679800096913)
  ·
    refine ⟨36730668978332009850072685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48974225304442679800096913 36730668978332009850072685)
    ·
      refine ⟨13774000866874503693777257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36730668978332009850072685 13774000866874503693777257)
      ·
        refine ⟨10330500650155877770332943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13774000866874503693777257 10330500650155877770332943)
        ·
          refine ⟨15495750975233816655499415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10330500650155877770332943 15495750975233816655499415)
          ·
            refine ⟨23243626462850724983249123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15495750975233816655499415 23243626462850724983249123)
            ·
              refine ⟨34865439694276087474873685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23243626462850724983249123 34865439694276087474873685)
              ·
                refine ⟨25536210713581118756011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 34865439694276087474873685 25536210713581118756011)
                ·
                  rfl

theorem cell23_1342753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 12].length) (baseStart_1342753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342753 prefixEnd_1342753 := by exact prefixLift 1342753
  have htrace : WordTrace (prefixWord ++ tailWord_1342753) baseStart_1342753 baseEnd_1342753 := by
    simpa [prefixWord, tailWord_1342753, baseEnd_1342753] using wordTrace_append hprefix tailTrace_1342753
  have hstable : (prefixWord ++ tailWord_1342753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342753).length < 2 ^ (prefixWord ++ tailWord_1342753).sum := by decide
  have hdescent : baseEnd_1342753 < baseStart_1342753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342757 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 1, 6]
def baseStart_1342757 : Nat := 118140960795 + 1342757 * 2 ^ 59
def prefixEnd_1342757 : Nat := 4983230072969 + 3 ^ 40 * 1342757 * 2
def baseEnd_1342757 : Nat := 229826581063102730254093

theorem tailTrace_1342757 : CollatzResearch.WordTrace tailWord_1342757 prefixEnd_1342757 229826581063102730254093 := by
  unfold tailWord_1342757
  simp only [CollatzResearch.WordTrace]
  refine ⟨48974371196428188483242525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32649580797618792322161683 48974371196428188483242525)
  ·
    refine ⟨18365389198660570681215947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48974371196428188483242525 18365389198660570681215947)
    ·
      refine ⟨27548083797990856021823921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18365389198660570681215947 27548083797990856021823921)
      ·
        refine ⟨20661062848493142016367941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27548083797990856021823921 20661062848493142016367941)
        ·
          refine ⟨3873949284092464128068989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20661062848493142016367941 3873949284092464128068989)
          ·
            refine ⟨1452730981534674048025871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3873949284092464128068989 1452730981534674048025871)
            ·
              refine ⟨2179096472302011072038807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452730981534674048025871 2179096472302011072038807)
              ·
                refine ⟨3268644708453016608058211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179096472302011072038807 3268644708453016608058211)
                ·
                  refine ⟨4902967062679524912087317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3268644708453016608058211 4902967062679524912087317)
                  ·
                    refine ⟨229826581063102730254093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4902967062679524912087317 229826581063102730254093)
                    ·
                      rfl

theorem cell23_1342757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_1342757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342757 prefixEnd_1342757 := by exact prefixLift 1342757
  have htrace : WordTrace (prefixWord ++ tailWord_1342757) baseStart_1342757 baseEnd_1342757 := by
    simpa [prefixWord, tailWord_1342757, baseEnd_1342757] using wordTrace_append hprefix tailTrace_1342757
  have hstable : (prefixWord ++ tailWord_1342757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342757).length < 2 ^ (prefixWord ++ tailWord_1342757).sum := by decide
  have hdescent : baseEnd_1342757 < baseStart_1342757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342770 : List Nat := [3, 2, 1, 1, 4, 2, 1, 9]
def baseStart_1342770 : Nat := 118140960795 + 1342770 * 2 ^ 59
def prefixEnd_1342770 : Nat := 4983230072969 + 3 ^ 40 * 1342770 * 2
def baseEnd_1342770 : Nat := 25536534016215431107397

theorem tailTrace_1342770 : CollatzResearch.WordTrace tailWord_1342770 prefixEnd_1342770 25536534016215431107397 := by
  unfold tailWord_1342770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12243711336345272925866441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32649896896920727802310509 12243711336345272925866441)
  ·
    refine ⟨9182783502258954694399831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12243711336345272925866441 9182783502258954694399831)
    ·
      refine ⟨13774175253388432041599747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9182783502258954694399831 13774175253388432041599747)
      ·
        refine ⟨20661262880082648062399621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13774175253388432041599747 20661262880082648062399621)
        ·
          refine ⟨3873986790015496511699929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20661262880082648062399621 3873986790015496511699929)
          ·
            refine ⟨2905490092511622383774947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3873986790015496511699929 2905490092511622383774947)
            ·
              refine ⟨4358235138767433575662421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905490092511622383774947 4358235138767433575662421)
              ·
                refine ⟨25536534016215431107397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4358235138767433575662421 25536534016215431107397)
                ·
                  rfl

theorem cell23_1342770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 9].length) (baseStart_1342770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342770 prefixEnd_1342770 := by exact prefixLift 1342770
  have htrace : WordTrace (prefixWord ++ tailWord_1342770) baseStart_1342770 baseEnd_1342770 := by
    simpa [prefixWord, tailWord_1342770, baseEnd_1342770] using wordTrace_append hprefix tailTrace_1342770
  have hstable : (prefixWord ++ tailWord_1342770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342770).length < 2 ^ (prefixWord ++ tailWord_1342770).sum := by decide
  have hdescent : baseEnd_1342770 < baseStart_1342770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342798 : List Nat := [4, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2]
def baseStart_1342798 : Nat := 118140960795 + 1342798 * 2 ^ 59
def prefixEnd_1342798 : Nat := 4983230072969 + 3 ^ 40 * 1342798 * 2
def baseEnd_1342798 : Nat := 689500795896142530349591

theorem tailTrace_1342798 : CollatzResearch.WordTrace tailWord_1342798 prefixEnd_1342798 689500795896142530349591 := by
  unfold tailWord_1342798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6121983323659956560685631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32650577726186434990323365 6121983323659956560685631)
  ·
    refine ⟨9182974985489934841028447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6121983323659956560685631 9182974985489934841028447)
    ·
      refine ⟨13774462478234902261542671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9182974985489934841028447 13774462478234902261542671)
      ·
        refine ⟨20661693717352353392314007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13774462478234902261542671 20661693717352353392314007)
        ·
          refine ⟨30992540576028530088471011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20661693717352353392314007 30992540576028530088471011)
          ·
            refine ⟨46488810864042795132706517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30992540576028530088471011 46488810864042795132706517)
            ·
              refine ⟨1089581504626003010922809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46488810864042795132706517 1089581504626003010922809)
              ·
                refine ⟨817186128469502258192107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089581504626003010922809 817186128469502258192107)
                ·
                  refine ⟨1225779192704253387288161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 817186128469502258192107 1225779192704253387288161)
                  ·
                    refine ⟨919334394528190040466121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1225779192704253387288161 919334394528190040466121)
                    ·
                      refine ⟨689500795896142530349591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 919334394528190040466121 689500795896142530349591)
                      ·
                        rfl

theorem cell23_1342798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_1342798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342798 prefixEnd_1342798 := by exact prefixLift 1342798
  have htrace : WordTrace (prefixWord ++ tailWord_1342798) baseStart_1342798 baseEnd_1342798 := by
    simpa [prefixWord, tailWord_1342798, baseEnd_1342798] using wordTrace_append hprefix tailTrace_1342798
  have hstable : (prefixWord ++ tailWord_1342798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342798).length < 2 ^ (prefixWord ++ tailWord_1342798).sum := by decide
  have hdescent : baseEnd_1342798 < baseStart_1342798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342840 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 6, 4, 3]
def baseStart_1342840 : Nat := 118140960795 + 1342840 * 2 ^ 59
def prefixEnd_1342840 : Nat := 4983230072969 + 3 ^ 40 * 1342840 * 2
def baseEnd_1342840 : Nat := 689522362083631366024397

theorem tailTrace_1342840 : CollatzResearch.WordTrace tailWord_1342840 prefixEnd_1342840 689522362083631366024397 := by
  unfold tailWord_1342840
  simp only [CollatzResearch.WordTrace]
  refine ⟨24488699227563746829256987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32651598970084995772342649 24488699227563746829256987)
  ·
    refine ⟨36733048841345620243885481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24488699227563746829256987 36733048841345620243885481)
    ·
      refine ⟨27549786631009215182914111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36733048841345620243885481 27549786631009215182914111)
      ·
        refine ⟨41324679946513822774371167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27549786631009215182914111 41324679946513822774371167)
        ·
          refine ⟨61987019919770734161556751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41324679946513822774371167 61987019919770734161556751)
          ·
            refine ⟨92980529879656101242335127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61987019919770734161556751 92980529879656101242335127)
            ·
              refine ⟨139470794819484151863502691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92980529879656101242335127 139470794819484151863502691)
              ·
                refine ⟨209206192229226227795254037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139470794819484151863502691 209206192229226227795254037)
                ·
                  refine ⟨9806540260744979427902533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 209206192229226227795254037 9806540260744979427902533)
                  ·
                    refine ⟨1838726298889683642731725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9806540260744979427902533 1838726298889683642731725)
                    ·
                      refine ⟨689522362083631366024397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1838726298889683642731725 689522362083631366024397)
                      ·
                        rfl

theorem cell23_1342840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_1342840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342840 prefixEnd_1342840 := by exact prefixLift 1342840
  have htrace : WordTrace (prefixWord ++ tailWord_1342840) baseStart_1342840 baseEnd_1342840 := by
    simpa [prefixWord, tailWord_1342840, baseEnd_1342840] using wordTrace_append hprefix tailTrace_1342840
  have hstable : (prefixWord ++ tailWord_1342840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342840).length < 2 ^ (prefixWord ++ tailWord_1342840).sum := by decide
  have hdescent : baseEnd_1342840 < baseStart_1342840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342860 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 7]
def baseStart_1342860 : Nat := 118140960795 + 1342860 * 2 ^ 59
def prefixEnd_1342860 : Nat := 4983230072969 + 3 ^ 40 * 1342860 * 2
def baseEnd_1342860 : Nat := 76614736855191254197145

theorem tailTrace_1342860 : CollatzResearch.WordTrace tailWord_1342860 prefixEnd_1342860 76614736855191254197145 := by
  unfold tailWord_1342860
  simp only [CollatzResearch.WordTrace]
  refine ⟨24489063957527518537121017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32652085276703358049494689 24489063957527518537121017)
  ·
    refine ⟨18366797968145638902840763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24489063957527518537121017 18366797968145638902840763)
    ·
      refine ⟨27550196952218458354261145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18366797968145638902840763 27550196952218458354261145)
      ·
        refine ⟨20662647714163843765695859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27550196952218458354261145 20662647714163843765695859)
        ·
          refine ⟨30993971571245765648543789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20662647714163843765695859 30993971571245765648543789)
          ·
            refine ⟨11622739339217162118203921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30993971571245765648543789 11622739339217162118203921)
            ·
              refine ⟨8717054504412871588652941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11622739339217162118203921 8717054504412871588652941)
              ·
                refine ⟨3268895439154826845744853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8717054504412871588652941 3268895439154826845744853)
                ·
                  refine ⟨76614736855191254197145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3268895439154826845744853 76614736855191254197145)
                  ·
                    rfl

theorem cell23_1342860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_1342860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342860 prefixEnd_1342860 := by exact prefixLift 1342860
  have htrace : WordTrace (prefixWord ++ tailWord_1342860) baseStart_1342860 baseEnd_1342860 := by
    simpa [prefixWord, tailWord_1342860, baseEnd_1342860] using wordTrace_append hprefix tailTrace_1342860
  have hstable : (prefixWord ++ tailWord_1342860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342860).length < 2 ^ (prefixWord ++ tailWord_1342860).sum := by decide
  have hdescent : baseEnd_1342860 < baseStart_1342860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342877 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 7]
def baseStart_1342877 : Nat := 118140960795 + 1342877 * 2 ^ 59
def prefixEnd_1342877 : Nat := 4983230072969 + 3 ^ 40 * 1342877 * 2
def baseEnd_1342877 : Nat := 76615706763094191251303

theorem tailTrace_1342877 : CollatzResearch.WordTrace tailWord_1342877 prefixEnd_1342877 76615706763094191251303 := by
  unfold tailWord_1342877
  simp only [CollatzResearch.WordTrace]
  refine ⟨48978747955993448977610885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32652498637328965985073923 48978747955993448977610885)
  ·
    refine ⟨9183515241748771683302041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48978747955993448977610885 9183515241748771683302041)
    ·
      refine ⟨6887636431311578762476531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9183515241748771683302041 6887636431311578762476531)
      ·
        refine ⟨10331454646967368143714797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6887636431311578762476531 10331454646967368143714797)
        ·
          refine ⟨3874295492612763053893049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10331454646967368143714797 3874295492612763053893049)
          ·
            refine ⟨2905721619459572290419787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3874295492612763053893049 2905721619459572290419787)
            ·
              refine ⟨4358582429189358435629681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905721619459572290419787 4358582429189358435629681)
              ·
                refine ⟨3268936821892018826722261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4358582429189358435629681 3268936821892018826722261)
                ·
                  refine ⟨76615706763094191251303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3268936821892018826722261 76615706763094191251303)
                  ·
                    rfl

theorem cell23_1342877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_1342877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342877 prefixEnd_1342877 := by exact prefixLift 1342877
  have htrace : WordTrace (prefixWord ++ tailWord_1342877) baseStart_1342877 baseEnd_1342877 := by
    simpa [prefixWord, tailWord_1342877, baseEnd_1342877] using wordTrace_append hprefix tailTrace_1342877
  have hstable : (prefixWord ++ tailWord_1342877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342877).length < 2 ^ (prefixWord ++ tailWord_1342877).sum := by decide
  have hdescent : baseEnd_1342877 < baseStart_1342877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342887 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1342887 : Nat := 118140960795 + 1342887 * 2 ^ 59
def prefixEnd_1342887 : Nat := 4983230072969 + 3 ^ 40 * 1342887 * 2
def baseEnd_1342887 : Nat := 689546495674392682136681

theorem tailTrace_1342887 : CollatzResearch.WordTrace tailWord_1342887 prefixEnd_1342887 689546495674392682136681 := by
  unfold tailWord_1342887
  simp only [CollatzResearch.WordTrace]
  refine ⟨48979112685957220685474915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32652741790638147123649943 48979112685957220685474915)
  ·
    refine ⟨73468669028935831028212373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48979112685957220685474915 73468669028935831028212373)
    ·
      refine ⟨3443843860731367079447455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73468669028935831028212373 3443843860731367079447455)
      ·
        refine ⟨5165765791097050619171183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3443843860731367079447455 5165765791097050619171183)
        ·
          refine ⟨7748648686645575928756775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5165765791097050619171183 7748648686645575928756775)
          ·
            refine ⟨11622973029968363893135163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7748648686645575928756775 11622973029968363893135163)
            ·
              refine ⟨17434459544952545839702745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11622973029968363893135163 17434459544952545839702745)
              ·
                refine ⟨13075844658714409379777059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17434459544952545839702745 13075844658714409379777059)
                ·
                  refine ⟨19613766988071614069665589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13075844658714409379777059 19613766988071614069665589)
                  ·
                    refine ⟨1838790655131713819031149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19613766988071614069665589 1838790655131713819031149)
                    ·
                      refine ⟨689546495674392682136681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1838790655131713819031149 689546495674392682136681)
                      ·
                        rfl

theorem cell23_1342887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1342887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342887 prefixEnd_1342887 := by exact prefixLift 1342887
  have htrace : WordTrace (prefixWord ++ tailWord_1342887) baseStart_1342887 baseEnd_1342887 := by
    simpa [prefixWord, tailWord_1342887, baseEnd_1342887] using wordTrace_append hprefix tailTrace_1342887
  have hstable : (prefixWord ++ tailWord_1342887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342887).length < 2 ^ (prefixWord ++ tailWord_1342887).sum := by decide
  have hdescent : baseEnd_1342887 < baseStart_1342887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342905 : List Nat := [1, 2, 1, 4, 5, 1, 1, 2, 2, 2, 2]
def baseStart_1342905 : Nat := 118140960795 + 1342905 * 2 ^ 59
def prefixEnd_1342905 : Nat := 4983230072969 + 3 ^ 40 * 1342905 * 2
def baseEnd_1342905 : Nat := 689555738326173611711599

theorem tailTrace_1342905 : CollatzResearch.WordTrace tailWord_1342905 prefixEnd_1342905 689555738326173611711599 := by
  unfold tailWord_1342905
  simp only [CollatzResearch.WordTrace]
  refine ⟨48979769199892009759630169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32653179466594673173086779 48979769199892009759630169)
  ·
    refine ⟨36734826899919007319722627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48979769199892009759630169 36734826899919007319722627)
    ·
      refine ⟨55102240349878510979583941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36734826899919007319722627 55102240349878510979583941)
      ·
        refine ⟨10331670065602220808671989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55102240349878510979583941 10331670065602220808671989)
        ·
          refine ⟨968594068650208200812999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10331670065602220808671989 968594068650208200812999)
          ·
            refine ⟨1452891102975312301219499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968594068650208200812999 1452891102975312301219499)
            ·
              refine ⟨2179336654462968451829249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452891102975312301219499 2179336654462968451829249)
              ·
                refine ⟨1634502490847226338871937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2179336654462968451829249 1634502490847226338871937)
                ·
                  refine ⟨1225876868135419754153953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1634502490847226338871937 1225876868135419754153953)
                  ·
                    refine ⟨919407651101564815615465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1225876868135419754153953 919407651101564815615465)
                    ·
                      refine ⟨689555738326173611711599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 919407651101564815615465 689555738326173611711599)
                      ·
                        rfl

theorem cell23_1342905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_1342905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342905 prefixEnd_1342905 := by exact prefixLift 1342905
  have htrace : WordTrace (prefixWord ++ tailWord_1342905) baseStart_1342905 baseEnd_1342905 := by
    simpa [prefixWord, tailWord_1342905, baseEnd_1342905] using wordTrace_append hprefix tailTrace_1342905
  have hstable : (prefixWord ++ tailWord_1342905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342905).length < 2 ^ (prefixWord ++ tailWord_1342905).sum := by decide
  have hdescent : baseEnd_1342905 < baseStart_1342905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342984 : List Nat := [2, 1, 3, 2, 1, 1, 6, 1, 6]
def baseStart_1342984 : Nat := 118140960795 + 1342984 * 2 ^ 59
def prefixEnd_1342984 : Nat := 4983230072969 + 3 ^ 40 * 1342984 * 2
def baseEnd_1342984 : Nat := 76621811477542089180415

theorem tailTrace_1342984 : CollatzResearch.WordTrace tailWord_1342984 prefixEnd_1342984 76621811477542089180415 := by
  unfold tailWord_1342984
  simp only [CollatzResearch.WordTrace]
  refine ⟨24491325283302903125878003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32655100377737204167837337 24491325283302903125878003)
  ·
    refine ⟨36736987924954354688817005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24491325283302903125878003 36736987924954354688817005)
    ·
      refine ⟨13776370471857883008306377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36736987924954354688817005 13776370471857883008306377)
      ·
        refine ⟨10332277853893412256229783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13776370471857883008306377 10332277853893412256229783)
        ·
          refine ⟨15498416780840118384344675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10332277853893412256229783 15498416780840118384344675)
          ·
            refine ⟨23247625171260177576517013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15498416780840118384344675 23247625171260177576517013)
            ·
              refine ⟨1089732429902820823899235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23247625171260177576517013 1089732429902820823899235)
              ·
                refine ⟨1634598644854231235848853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089732429902820823899235 1634598644854231235848853)
                ·
                  refine ⟨76621811477542089180415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1634598644854231235848853 76621811477542089180415)
                  ·
                    rfl

theorem cell23_1342984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 6].length) (baseStart_1342984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342984 prefixEnd_1342984 := by exact prefixLift 1342984
  have htrace : WordTrace (prefixWord ++ tailWord_1342984) baseStart_1342984 baseEnd_1342984 := by
    simpa [prefixWord, tailWord_1342984, baseEnd_1342984] using wordTrace_append hprefix tailTrace_1342984
  have hstable : (prefixWord ++ tailWord_1342984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342984).length < 2 ^ (prefixWord ++ tailWord_1342984).sum := by decide
  have hdescent : baseEnd_1342984 < baseStart_1342984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343068 : List Nat := [2, 2, 4, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_1343068 : Nat := 118140960795 + 1343068 * 2 ^ 59
def prefixEnd_1343068 : Nat := 4983230072969 + 3 ^ 40 * 1343068 * 2
def baseEnd_1343068 : Nat := 689639435672856473973349

theorem tailTrace_1343068 : CollatzResearch.WordTrace tailWord_1343068 prefixEnd_1343068 689639435672856473973349 := by
  unfold tailWord_1343068
  simp only [CollatzResearch.WordTrace]
  refine ⟨24492857149150744298906929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32657142865534325731875905 24492857149150744298906929)
  ·
    refine ⟨18369642861863058224180197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24492857149150744298906929 18369642861863058224180197)
    ·
      refine ⟨3444308036599323417033787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18369642861863058224180197 3444308036599323417033787)
      ·
        refine ⟨5166462054898985125550681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3444308036599323417033787 5166462054898985125550681)
        ·
          refine ⟨3874846541174238844163011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5166462054898985125550681 3874846541174238844163011)
          ·
            refine ⟨5812269811761358266244517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874846541174238844163011 5812269811761358266244517)
            ·
              refine ⟨1089800589705254674920847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5812269811761358266244517 1089800589705254674920847)
              ·
                refine ⟨1634700884557882012381271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089800589705254674920847 1634700884557882012381271)
                ·
                  refine ⟨2452051326836823018571907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634700884557882012381271 2452051326836823018571907)
                  ·
                    refine ⟨3678076990255234527857861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2452051326836823018571907 3678076990255234527857861)
                    ·
                      refine ⟨689639435672856473973349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3678076990255234527857861 689639435672856473973349)
                      ·
                        rfl

theorem cell23_1343068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_1343068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343068 prefixEnd_1343068 := by exact prefixLift 1343068
  have htrace : WordTrace (prefixWord ++ tailWord_1343068) baseStart_1343068 baseEnd_1343068 := by
    simpa [prefixWord, tailWord_1343068, baseEnd_1343068] using wordTrace_append hprefix tailTrace_1343068
  have hstable : (prefixWord ++ tailWord_1343068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343068).length < 2 ^ (prefixWord ++ tailWord_1343068).sum := by decide
  have hdescent : baseEnd_1343068 < baseStart_1343068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343085 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_1343085 : Nat := 118140960795 + 1343085 * 2 ^ 59
def prefixEnd_1343085 : Nat := 4983230072969 + 3 ^ 40 * 1343085 * 2
def baseEnd_1343085 : Nat := 689648164843982907460771

theorem tailTrace_1343085 : CollatzResearch.WordTrace tailWord_1343085 prefixEnd_1343085 689648164843982907460771 := by
  unfold tailWord_1343085
  simp only [CollatzResearch.WordTrace]
  refine ⟨48986334339239900501182709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32657556226159933667455139 48986334339239900501182709)
  ·
    refine ⟨4592468844303740671985879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48986334339239900501182709 4592468844303740671985879)
    ·
      refine ⟨6888703266455611007978819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4592468844303740671985879 6888703266455611007978819)
      ·
        refine ⟨10333054899683416511968229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6888703266455611007978819 10333054899683416511968229)
        ·
          refine ⟨1937447793690640595994043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10333054899683416511968229 1937447793690640595994043)
          ·
            refine ⟨2906171690535960893991065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1937447793690640595994043 2906171690535960893991065)
            ·
              refine ⟨2179628767901970670493299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2906171690535960893991065 2179628767901970670493299)
              ·
                refine ⟨3269443151852956005739949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179628767901970670493299 3269443151852956005739949)
                ·
                  refine ⟨1226041181944858502152481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3269443151852956005739949 1226041181944858502152481)
                  ·
                    refine ⟨919530886458643876614361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1226041181944858502152481 919530886458643876614361)
                    ·
                      refine ⟨689648164843982907460771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 919530886458643876614361 689648164843982907460771)
                      ·
                        rfl

theorem cell23_1343085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_1343085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343085 prefixEnd_1343085 := by exact prefixLift 1343085
  have htrace : WordTrace (prefixWord ++ tailWord_1343085) baseStart_1343085 baseEnd_1343085 := by
    simpa [prefixWord, tailWord_1343085, baseEnd_1343085] using wordTrace_append hprefix tailTrace_1343085
  have hstable : (prefixWord ++ tailWord_1343085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343085).length < 2 ^ (prefixWord ++ tailWord_1343085).sum := by decide
  have hdescent : baseEnd_1343085 < baseStart_1343085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343101 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_1343101 : Nat := 118140960795 + 1343101 * 2 ^ 59
def prefixEnd_1343101 : Nat := 4983230072969 + 3 ^ 40 * 1343101 * 2
def baseEnd_1343101 : Nat := 689656380534454844860697

theorem tailTrace_1343101 : CollatzResearch.WordTrace tailWord_1343101 prefixEnd_1343101 689656380534454844860697 := by
  unfold tailWord_1343101
  simp only [CollatzResearch.WordTrace]
  refine ⟨48986917907181935233765157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32657945271454623489176771 48986917907181935233765157)
  ·
    refine ⟨9185047107596612856330967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48986917907181935233765157 9185047107596612856330967)
    ·
      refine ⟨13777570661394919284496451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9185047107596612856330967 13777570661394919284496451)
      ·
        refine ⟨20666355992092378926744677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13777570661394919284496451 20666355992092378926744677)
        ·
          refine ⟨3874941748517321048764627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20666355992092378926744677 3874941748517321048764627)
          ·
            refine ⟨5812412622775981573146941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874941748517321048764627 5812412622775981573146941)
            ·
              refine ⟨2179654733540993089930103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5812412622775981573146941 2179654733540993089930103)
              ·
                refine ⟨3269482100311489634895155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179654733540993089930103 3269482100311489634895155)
                ·
                  refine ⟨4904223150467234452342733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3269482100311489634895155 4904223150467234452342733)
                  ·
                    refine ⟨1839083681425212919628525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4904223150467234452342733 1839083681425212919628525)
                    ·
                      refine ⟨689656380534454844860697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1839083681425212919628525 689656380534454844860697)
                      ·
                        rfl

theorem cell23_1343101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_1343101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343101 prefixEnd_1343101 := by exact prefixLift 1343101
  have htrace : WordTrace (prefixWord ++ tailWord_1343101) baseStart_1343101 baseEnd_1343101 := by
    simpa [prefixWord, tailWord_1343101, baseEnd_1343101] using wordTrace_append hprefix tailTrace_1343101
  have hstable : (prefixWord ++ tailWord_1343101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343101).length < 2 ^ (prefixWord ++ tailWord_1343101).sum := by decide
  have hdescent : baseEnd_1343101 < baseStart_1343101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343108 : List Nat := [2, 3, 2, 1, 5, 1, 2, 7]
def baseStart_1343108 : Nat := 118140960795 + 1343108 * 2 ^ 59
def prefixEnd_1343108 : Nat := 4983230072969 + 3 ^ 40 * 1343108 * 2
def baseEnd_1343108 : Nat := 25542962033297641387895

theorem tailTrace_1343108 : CollatzResearch.WordTrace tailWord_1343108 prefixEnd_1343108 25542962033297641387895 := by
  unfold tailWord_1343108
  simp only [CollatzResearch.WordTrace]
  refine ⟨24493586609078287714634989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32658115478771050286179985 24493586609078287714634989)
  ·
    refine ⟨9185094978404357892988121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24493586609078287714634989 9185094978404357892988121)
    ·
      refine ⟨6888821233803268419741091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9185094978404357892988121 6888821233803268419741091)
      ·
        refine ⟨10333231850704902629611637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6888821233803268419741091 10333231850704902629611637)
        ·
          refine ⟨968740486003584621526091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10333231850704902629611637 968740486003584621526091)
          ·
            refine ⟨1453110729005376932289137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968740486003584621526091 1453110729005376932289137)
            ·
              refine ⟨1089833046754032699216853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1453110729005376932289137 1089833046754032699216853)
              ·
                refine ⟨25542962033297641387895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1089833046754032699216853 25542962033297641387895)
                ·
                  rfl

theorem cell23_1343108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 7].length) (baseStart_1343108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343108 prefixEnd_1343108 := by exact prefixLift 1343108
  have htrace : WordTrace (prefixWord ++ tailWord_1343108) baseStart_1343108 baseEnd_1343108 := by
    simpa [prefixWord, tailWord_1343108, baseEnd_1343108] using wordTrace_append hprefix tailTrace_1343108
  have hstable : (prefixWord ++ tailWord_1343108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343108).length < 2 ^ (prefixWord ++ tailWord_1343108).sum := by decide
  have hdescent : baseEnd_1343108 < baseStart_1343108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343114 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1343114 : Nat := 118140960795 + 1343114 * 2 ^ 59
def prefixEnd_1343114 : Nat := 4983230072969 + 3 ^ 40 * 1343114 * 2
def baseEnd_1343114 : Nat := 689663055782963293998137

theorem tailTrace_1343114 : CollatzResearch.WordTrace tailWord_1343114 prefixEnd_1343114 689663055782963293998137 := by
  unfold tailWord_1343114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12246848014033709613497099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32658261370756558969325597 12246848014033709613497099)
  ·
    refine ⟨18370272021050564420245649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12246848014033709613497099 18370272021050564420245649)
    ·
      refine ⟨13777704015787923315184237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18370272021050564420245649 13777704015787923315184237)
      ·
        refine ⟨5166639005920471243194089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13777704015787923315184237 5166639005920471243194089)
        ·
          refine ⟨3874979254440353432395567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5166639005920471243194089 3874979254440353432395567)
          ·
            refine ⟨5812468881660530148593351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874979254440353432395567 5812468881660530148593351)
            ·
              refine ⟨8718703322490795222890027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5812468881660530148593351 8718703322490795222890027)
              ·
                refine ⟨13078054983736192834335041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8718703322490795222890027 13078054983736192834335041)
                ·
                  refine ⟨9808541237802144625751281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13078054983736192834335041 9808541237802144625751281)
                  ·
                    refine ⟨7356405928351608469313461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9808541237802144625751281 7356405928351608469313461)
                    ·
                      refine ⟨689663055782963293998137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7356405928351608469313461 689663055782963293998137)
                      ·
                        rfl

theorem cell23_1343114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1343114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343114 prefixEnd_1343114 := by exact prefixLift 1343114
  have htrace : WordTrace (prefixWord ++ tailWord_1343114) baseStart_1343114 baseEnd_1343114 := by
    simpa [prefixWord, tailWord_1343114, baseEnd_1343114] using wordTrace_append hprefix tailTrace_1343114
  have hstable : (prefixWord ++ tailWord_1343114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343114).length < 2 ^ (prefixWord ++ tailWord_1343114).sum := by decide
  have hdescent : baseEnd_1343114 < baseStart_1343114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343128 : List Nat := [2, 1, 2, 4, 1, 2, 2, 3, 1, 3, 2]
def baseStart_1343128 : Nat := 118140960795 + 1343128 * 2 ^ 59
def prefixEnd_1343128 : Nat := 4983230072969 + 3 ^ 40 * 1343128 * 2
def baseEnd_1343128 : Nat := 689670244512126239223073

theorem tailTrace_1343128 : CollatzResearch.WordTrace tailWord_1343128 prefixEnd_1343128 689670244512126239223073 := by
  unfold tailWord_1343128
  simp only [CollatzResearch.WordTrace]
  refine ⟨24493951339042059422499019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32658601785389412563332025 24493951339042059422499019)
  ·
    refine ⟨36740927008563089133748529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24493951339042059422499019 36740927008563089133748529)
    ·
      refine ⟨27555695256422316850311397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36740927008563089133748529 27555695256422316850311397)
      ·
        refine ⟨5166692860579184409433387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27555695256422316850311397 5166692860579184409433387)
        ·
          refine ⟨7750039290868776614150081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5166692860579184409433387 7750039290868776614150081)
          ·
            refine ⟨5812529468151582460612561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7750039290868776614150081 5812529468151582460612561)
            ·
              refine ⟨4359397101113686845459421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5812529468151582460612561 4359397101113686845459421)
              ·
                refine ⟨1634773912917632567047283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4359397101113686845459421 1634773912917632567047283)
                ·
                  refine ⟨2452160869376448850570925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634773912917632567047283 2452160869376448850570925)
                  ·
                    refine ⟨919560326016168318964097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2452160869376448850570925 919560326016168318964097)
                    ·
                      refine ⟨689670244512126239223073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 919560326016168318964097 689670244512126239223073)
                      ·
                        rfl

theorem cell23_1343128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_1343128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343128 prefixEnd_1343128 := by exact prefixLift 1343128
  have htrace : WordTrace (prefixWord ++ tailWord_1343128) baseStart_1343128 baseEnd_1343128 := by
    simpa [prefixWord, tailWord_1343128, baseEnd_1343128] using wordTrace_append hprefix tailTrace_1343128
  have hstable : (prefixWord ++ tailWord_1343128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343128).length < 2 ^ (prefixWord ++ tailWord_1343128).sum := by decide
  have hdescent : baseEnd_1343128 < baseStart_1343128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343154 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_1343154 : Nat := 118140960795 + 1343154 * 2 ^ 59
def prefixEnd_1343154 : Nat := 4983230072969 + 3 ^ 40 * 1343154 * 2
def baseEnd_1343154 : Nat := 689683595009143137497953

theorem tailTrace_1343154 : CollatzResearch.WordTrace tailWord_1343154 prefixEnd_1343154 689683595009143137497953 := by
  unfold tailWord_1343154
  simp only [CollatzResearch.WordTrace]
  refine ⟨12247212743997481321361129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32659233983993283523629677 12247212743997481321361129)
  ·
    refine ⟨9185409557998110991020847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12247212743997481321361129 9185409557998110991020847)
    ·
      refine ⟨13778114336997166486531271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9185409557998110991020847 13778114336997166486531271)
      ·
        refine ⟨20667171505495749729796907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13778114336997166486531271 20667171505495749729796907)
        ·
          refine ⟨31000757258243624594695361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20667171505495749729796907 31000757258243624594695361)
          ·
            refine ⟨23250567943682718446021521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31000757258243624594695361 23250567943682718446021521)
            ·
              refine ⟨17437925957762038834516141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23250567943682718446021521 17437925957762038834516141)
              ·
                refine ⟨6539222234160764562943553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17437925957762038834516141 6539222234160764562943553)
                ·
                  refine ⟨4904416675620573422207665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6539222234160764562943553 4904416675620573422207665)
                  ·
                    refine ⟨3678312506715430066655749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4904416675620573422207665 3678312506715430066655749)
                    ·
                      refine ⟨689683595009143137497953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3678312506715430066655749 689683595009143137497953)
                      ·
                        rfl

theorem cell23_1343154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_1343154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343154 prefixEnd_1343154 := by exact prefixLift 1343154
  have htrace : WordTrace (prefixWord ++ tailWord_1343154) baseStart_1343154 baseEnd_1343154 := by
    simpa [prefixWord, tailWord_1343154, baseEnd_1343154] using wordTrace_append hprefix tailTrace_1343154
  have hstable : (prefixWord ++ tailWord_1343154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343154).length < 2 ^ (prefixWord ++ tailWord_1343154).sum := by decide
  have hdescent : baseEnd_1343154 < baseStart_1343154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343204 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_1343204 : Nat := 118140960795 + 1343204 * 2 ^ 59
def prefixEnd_1343204 : Nat := 4983230072969 + 3 ^ 40 * 1343204 * 2
def baseEnd_1343204 : Nat := 689709269041867941872723

theorem tailTrace_1343204 : CollatzResearch.WordTrace tailWord_1343204 prefixEnd_1343204 689709269041867941872723 := by
  unfold tailWord_1343204
  simp only [CollatzResearch.WordTrace]
  refine ⟨24495337312904391912382333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32660449750539189216509777 24495337312904391912382333)
  ·
    refine ⟨9185751492339146967143375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24495337312904391912382333 9185751492339146967143375)
    ·
      refine ⟨13778627238508720450715063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9185751492339146967143375 13778627238508720450715063)
      ·
        refine ⟨20667940857763080676072595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13778627238508720450715063 20667940857763080676072595)
        ·
          refine ⟨31001911286644621014108893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20667940857763080676072595 31001911286644621014108893)
          ·
            refine ⟨11625716732491732880290835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31001911286644621014108893 11625716732491732880290835)
            ·
              refine ⟨17438575098737599320436253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11625716732491732880290835 17438575098737599320436253)
              ·
                refine ⟨6539465662026599745163595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17438575098737599320436253 6539465662026599745163595)
                ·
                  refine ⟨9809198493039899617745393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6539465662026599745163595 9809198493039899617745393)
                  ·
                    refine ⟨7356898869779924713309045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9809198493039899617745393 7356898869779924713309045)
                    ·
                      refine ⟨689709269041867941872723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7356898869779924713309045 689709269041867941872723)
                      ·
                        rfl

theorem cell23_1343204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_1343204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343204 prefixEnd_1343204 := by exact prefixLift 1343204
  have htrace : WordTrace (prefixWord ++ tailWord_1343204) baseStart_1343204 baseEnd_1343204 := by
    simpa [prefixWord, tailWord_1343204, baseEnd_1343204] using wordTrace_append hprefix tailTrace_1343204
  have hstable : (prefixWord ++ tailWord_1343204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343204).length < 2 ^ (prefixWord ++ tailWord_1343204).sum := by decide
  have hdescent : baseEnd_1343204 < baseStart_1343204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343231 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 4]
def baseStart_1343231 : Nat := 118140960795 + 1343231 * 2 ^ 59
def prefixEnd_1343231 : Nat := 4983230072969 + 3 ^ 40 * 1343231 * 2
def baseEnd_1343231 : Nat := 689723133019539336235099

theorem tailTrace_1343231 : CollatzResearch.WordTrace tailWord_1343231 prefixEnd_1343231 689723133019539336235099 := by
  unfold tailWord_1343231
  simp only [CollatzResearch.WordTrace]
  refine ⟨48991659396710967435997547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32661106264473978290665031 48991659396710967435997547)
  ·
    refine ⟨73487489095066451153996321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48991659396710967435997547 73487489095066451153996321)
    ·
      refine ⟨55115616821299838365497241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73487489095066451153996321 55115616821299838365497241)
      ·
        refine ⟨41336712615974878774122931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55115616821299838365497241 41336712615974878774122931)
        ·
          refine ⟨62005068923962318161184397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41336712615974878774122931 62005068923962318161184397)
          ·
            refine ⟨23251900846485869310444149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62005068923962318161184397 23251900846485869310444149)
            ·
              refine ⟨2179865704358050247854139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23251900846485869310444149 2179865704358050247854139)
              ·
                refine ⟨3269798556537075371781209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179865704358050247854139 3269798556537075371781209)
                ·
                  refine ⟨2452348917402806528835907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3269798556537075371781209 2452348917402806528835907)
                  ·
                    refine ⟨3678523376104209793253861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2452348917402806528835907 3678523376104209793253861)
                    ·
                      refine ⟨689723133019539336235099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3678523376104209793253861 689723133019539336235099)
                      ·
                        rfl

theorem cell23_1343231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_1343231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343231 prefixEnd_1343231 := by exact prefixLift 1343231
  have htrace : WordTrace (prefixWord ++ tailWord_1343231) baseStart_1343231 baseEnd_1343231 := by
    simpa [prefixWord, tailWord_1343231, baseEnd_1343231] using wordTrace_append hprefix tailTrace_1343231
  have hstable : (prefixWord ++ tailWord_1343231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343231).length < 2 ^ (prefixWord ++ tailWord_1343231).sum := by decide
  have hdescent : baseEnd_1343231 < baseStart_1343231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343244 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_1343244 : Nat := 118140960795 + 1343244 * 2 ^ 59
def prefixEnd_1343244 : Nat := 4983230072969 + 3 ^ 40 * 1343244 * 2
def baseEnd_1343244 : Nat := 689729808268047785372539

theorem tailTrace_1343244 : CollatzResearch.WordTrace tailWord_1343244 prefixEnd_1343244 689729808268047785372539 := by
  unfold tailWord_1343244
  simp only [CollatzResearch.WordTrace]
  refine ⟨24496066772831935328110393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32661422363775913770813857 24496066772831935328110393)
  ·
    refine ⟨18372050079623951496082795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24496066772831935328110393 18372050079623951496082795)
    ·
      refine ⟨27558075119435927244124193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18372050079623951496082795 27558075119435927244124193)
      ·
        refine ⟨20668556339576945433093145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27558075119435927244124193 20668556339576945433093145)
        ·
          refine ⟨15501417254682709074819859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20668556339576945433093145 15501417254682709074819859)
          ·
            refine ⟨23252125882024063612229789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15501417254682709074819859 23252125882024063612229789)
            ·
              refine ⟨8719547205759023854586171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23252125882024063612229789 8719547205759023854586171)
              ·
                refine ⟨13079320808638535781879257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8719547205759023854586171 13079320808638535781879257)
                ·
                  refine ⟨9809490606478901836409443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13079320808638535781879257 9809490606478901836409443)
                  ·
                    refine ⟨14714235909718352754614165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9809490606478901836409443 14714235909718352754614165)
                    ·
                      refine ⟨689729808268047785372539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14714235909718352754614165 689729808268047785372539)
                      ·
                        rfl

theorem cell23_1343244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_1343244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343244 prefixEnd_1343244 := by exact prefixLift 1343244
  have htrace : WordTrace (prefixWord ++ tailWord_1343244) baseStart_1343244 baseEnd_1343244 := by
    simpa [prefixWord, tailWord_1343244, baseEnd_1343244] using wordTrace_append hprefix tailTrace_1343244
  have hstable : (prefixWord ++ tailWord_1343244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343244).length < 2 ^ (prefixWord ++ tailWord_1343244).sum := by decide
  have hdescent : baseEnd_1343244 < baseStart_1343244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343258 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 3, 4]
def baseStart_1343258 : Nat := 118140960795 + 1343258 * 2 ^ 59
def prefixEnd_1343258 : Nat := 4983230072969 + 3 ^ 40 * 1343258 * 2
def baseEnd_1343258 : Nat := 229912332332403576865825

theorem tailTrace_1343258 : CollatzResearch.WordTrace tailWord_1343258 prefixEnd_1343258 229912332332403576865825 := by
  unfold tailWord_1343258
  simp only [CollatzResearch.WordTrace]
  refine ⟨12248161041903287761807607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32661762778408767364820285 12248161041903287761807607)
  ·
    refine ⟨18372241562854931642711411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12248161041903287761807607 18372241562854931642711411)
    ·
      refine ⟨27558362344282397464067117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18372241562854931642711411 27558362344282397464067117)
      ·
        refine ⟨10334385879105899049025169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27558362344282397464067117 10334385879105899049025169)
        ·
          refine ⟨7750789409329424286768877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10334385879105899049025169 7750789409329424286768877)
          ·
            refine ⟨2906546028498534107538329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7750789409329424286768877 2906546028498534107538329)
            ·
              refine ⟨2179909521373900580653747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2906546028498534107538329 2179909521373900580653747)
              ·
                refine ⟨3269864282060850870980621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179909521373900580653747 3269864282060850870980621)
                ·
                  refine ⟨1226199105772819076617733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3269864282060850870980621 1226199105772819076617733)
                  ·
                    refine ⟨229912332332403576865825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1226199105772819076617733 229912332332403576865825)
                    ·
                      rfl

theorem cell23_1343258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_1343258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343258 prefixEnd_1343258 := by exact prefixLift 1343258
  have htrace : WordTrace (prefixWord ++ tailWord_1343258) baseStart_1343258 baseEnd_1343258 := by
    simpa [prefixWord, tailWord_1343258, baseEnd_1343258] using wordTrace_append hprefix tailTrace_1343258
  have hstable : (prefixWord ++ tailWord_1343258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343258).length < 2 ^ (prefixWord ++ tailWord_1343258).sum := by decide
  have hdescent : baseEnd_1343258 < baseStart_1343258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343301 : List Nat := [1, 3, 1, 1, 1, 2, 3, 5, 1, 5]
def baseStart_1343301 : Nat := 118140960795 + 1343301 * 2 ^ 59
def prefixEnd_1343301 : Nat := 4983230072969 + 3 ^ 40 * 1343301 * 2
def baseEnd_1343301 : Nat := 229919692221784687453259

theorem tailTrace_1343301 : CollatzResearch.WordTrace tailWord_1343301 prefixEnd_1343301 229919692221784687453259 := by
  unfold tailWord_1343301
  simp only [CollatzResearch.WordTrace]
  refine ⟨48994212506457369391045757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32662808337638246260697171 48994212506457369391045757)
  ·
    refine ⟨18372829689921513521642159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48994212506457369391045757 18372829689921513521642159)
    ·
      refine ⟨27559244534882270282463239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18372829689921513521642159 27559244534882270282463239)
      ·
        refine ⟨41338866802323405423694859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27559244534882270282463239 41338866802323405423694859)
        ·
          refine ⟨62008300203485108135542289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41338866802323405423694859 62008300203485108135542289)
          ·
            refine ⟨46506225152613831101656717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62008300203485108135542289 46506225152613831101656717)
            ·
              refine ⟨17439834432230186663121269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46506225152613831101656717 17439834432230186663121269)
              ·
                refine ⟨1634984478021579999667619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17439834432230186663121269 1634984478021579999667619)
                ·
                  refine ⟨2452476717032369999501429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634984478021579999667619 2452476717032369999501429)
                  ·
                    refine ⟨229919692221784687453259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2452476717032369999501429 229919692221784687453259)
                    ·
                      rfl

theorem cell23_1343301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_1343301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343301 prefixEnd_1343301 := by exact prefixLift 1343301
  have htrace : WordTrace (prefixWord ++ tailWord_1343301) baseStart_1343301 baseEnd_1343301 := by
    simpa [prefixWord, tailWord_1343301, baseEnd_1343301] using wordTrace_append hprefix tailTrace_1343301
  have hstable : (prefixWord ++ tailWord_1343301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343301).length < 2 ^ (prefixWord ++ tailWord_1343301).sum := by decide
  have hdescent : baseEnd_1343301 < baseStart_1343301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343302 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1343302 : Nat := 118140960795 + 1343302 * 2 ^ 59
def prefixEnd_1343302 : Nat := 4983230072969 + 3 ^ 40 * 1343302 * 2
def baseEnd_1343302 : Nat := 689759590146008558447273

theorem tailTrace_1343302 : CollatzResearch.WordTrace tailWord_1343302 prefixEnd_1343302 689759590146008558447273 := by
  unfold tailWord_1343302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1531070280607929580057255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32662832652969164374554773 1531070280607929580057255)
  ·
    refine ⟨2296605420911894370085883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1531070280607929580057255 2296605420911894370085883)
    ·
      refine ⟨3444908131367841555128825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2296605420911894370085883 3444908131367841555128825)
      ·
        refine ⟨2583681098525881166346619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3444908131367841555128825 2583681098525881166346619)
        ·
          refine ⟨3875521647788821749519929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583681098525881166346619 3875521647788821749519929)
          ·
            refine ⟨2906641235841616312139947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3875521647788821749519929 2906641235841616312139947)
            ·
              refine ⟨4359961853762424468209921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2906641235841616312139947 4359961853762424468209921)
              ·
                refine ⟨3269971390321818351157441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4359961853762424468209921 3269971390321818351157441)
                ·
                  refine ⟨2452478542741363763368081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3269971390321818351157441 2452478542741363763368081)
                  ·
                    refine ⟨1839358907056022822526061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2452478542741363763368081 1839358907056022822526061)
                    ·
                      refine ⟨689759590146008558447273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1839358907056022822526061 689759590146008558447273)
                      ·
                        rfl

theorem cell23_1343302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1343302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343302 prefixEnd_1343302 := by exact prefixLift 1343302
  have htrace : WordTrace (prefixWord ++ tailWord_1343302) baseStart_1343302 baseEnd_1343302 := by
    simpa [prefixWord, tailWord_1343302, baseEnd_1343302] using wordTrace_append hprefix tailTrace_1343302
  have hstable : (prefixWord ++ tailWord_1343302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343302).length < 2 ^ (prefixWord ++ tailWord_1343302).sum := by decide
  have hdescent : baseEnd_1343302 < baseStart_1343302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343309 : List Nat := [1, 6, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1343309 : Nat := 118140960795 + 1343309 * 2 ^ 59
def prefixEnd_1343309 : Nat := 4983230072969 + 3 ^ 40 * 1343309 * 2
def baseEnd_1343309 : Nat := 229921061503530010353247

theorem tailTrace_1343309 : CollatzResearch.WordTrace tailWord_1343309 prefixEnd_1343309 229921061503530010353247 := by
  unfold tailWord_1343309
  simp only [CollatzResearch.WordTrace]
  refine ⟨48994504290428386757336981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32663002860285591171557987 48994504290428386757336981)
  ·
    refine ⟨2296617388613830629250171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48994504290428386757336981 2296617388613830629250171)
    ·
      refine ⟨3444926082920745943875257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2296617388613830629250171 3444926082920745943875257)
      ·
        refine ⟨2583694562190559457906443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3444926082920745943875257 2583694562190559457906443)
        ·
          refine ⟨3875541843285839186859665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583694562190559457906443 3875541843285839186859665)
          ·
            refine ⟨2906656382464379390144749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3875541843285839186859665 2906656382464379390144749)
            ·
              refine ⟨1089996143424142271304281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2906656382464379390144749 1089996143424142271304281)
              ·
                refine ⟨817497107568106703478211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089996143424142271304281 817497107568106703478211)
                ·
                  refine ⟨1226245661352160055217317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 817497107568106703478211 1226245661352160055217317)
                  ·
                    refine ⟨229921061503530010353247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1226245661352160055217317 229921061503530010353247)
                    ·
                      rfl

theorem cell23_1343309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1343309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343309 prefixEnd_1343309 := by exact prefixLift 1343309
  have htrace : WordTrace (prefixWord ++ tailWord_1343309) baseStart_1343309 baseEnd_1343309 := by
    simpa [prefixWord, tailWord_1343309, baseEnd_1343309] using wordTrace_append hprefix tailTrace_1343309
  have hstable : (prefixWord ++ tailWord_1343309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343309).length < 2 ^ (prefixWord ++ tailWord_1343309).sum := by decide
  have hdescent : baseEnd_1343309 < baseStart_1343309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343321 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 3, 1, 4]
def baseStart_1343321 : Nat := 118140960795 + 1343321 * 2 ^ 59
def prefixEnd_1343321 : Nat := 4983230072969 + 3 ^ 40 * 1343321 * 2
def baseEnd_1343321 : Nat := 689769346278443984109685

theorem tailTrace_1343321 : CollatzResearch.WordTrace tailWord_1343321 prefixEnd_1343321 689769346278443984109685 := by
  unfold tailWord_1343321
  simp only [CollatzResearch.WordTrace]
  refine ⟨48994941966384912806773817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32663294644256608537849211 48994941966384912806773817)
  ·
    refine ⟨36746206474788684605080363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48994941966384912806773817 36746206474788684605080363)
    ·
      refine ⟨55119309712183026907620545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36746206474788684605080363 55119309712183026907620545)
      ·
        refine ⟨41339482284137270180715409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55119309712183026907620545 41339482284137270180715409)
        ·
          refine ⟨31004611713102952635536557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41339482284137270180715409 31004611713102952635536557)
          ·
            refine ⟨11626729392413607238326209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31004611713102952635536557 11626729392413607238326209)
            ·
              refine ⟨8720047044310205428744657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11626729392413607238326209 8720047044310205428744657)
              ·
                refine ⟨6540035283232654071558493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8720047044310205428744657 6540035283232654071558493)
                ·
                  refine ⟨2452513231212245276834435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6540035283232654071558493 2452513231212245276834435)
                  ·
                    refine ⟨3678769846818367915251653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2452513231212245276834435 3678769846818367915251653)
                    ·
                      refine ⟨689769346278443984109685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3678769846818367915251653 689769346278443984109685)
                      ·
                        rfl

theorem cell23_1343321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_1343321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343321 prefixEnd_1343321 := by exact prefixLift 1343321
  have htrace : WordTrace (prefixWord ++ tailWord_1343321) baseStart_1343321 baseEnd_1343321 := by
    simpa [prefixWord, tailWord_1343321, baseEnd_1343321] using wordTrace_append hprefix tailTrace_1343321
  have hstable : (prefixWord ++ tailWord_1343321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343321).length < 2 ^ (prefixWord ++ tailWord_1343321).sum := by decide
  have hdescent : baseEnd_1343321 < baseStart_1343321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343341 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1343341 : Nat := 118140960795 + 1343341 * 2 ^ 59
def prefixEnd_1343341 : Nat := 4983230072969 + 3 ^ 40 * 1343341 * 2
def baseEnd_1343341 : Nat := 689779615891533905859593

theorem tailTrace_1343341 : CollatzResearch.WordTrace tailWord_1343341 prefixEnd_1343341 689779615891533905859593 := by
  unfold tailWord_1343341
  simp only [CollatzResearch.WordTrace]
  refine ⟨48995671426312456222501877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32663780950874970815001251 48995671426312456222501877)
  ·
    refine ⟨4593344196216792770859551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48995671426312456222501877 4593344196216792770859551)
    ·
      refine ⟨6890016294325189156289327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4593344196216792770859551 6890016294325189156289327)
      ·
        refine ⟨10335024441487783734433991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6890016294325189156289327 10335024441487783734433991)
        ·
          refine ⟨15502536662231675601650987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10335024441487783734433991 15502536662231675601650987)
          ·
            refine ⟨23253804993347513402476481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15502536662231675601650987 23253804993347513402476481)
            ·
              refine ⟨17440353745010635051857361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23253804993347513402476481 17440353745010635051857361)
              ·
                refine ⟨13080265308757976288893021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17440353745010635051857361 13080265308757976288893021)
                ·
                  refine ⟨4905099490784241108334883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13080265308757976288893021 4905099490784241108334883)
                  ·
                    refine ⟨7357649236176361662502325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4905099490784241108334883 7357649236176361662502325)
                    ·
                      refine ⟨689779615891533905859593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7357649236176361662502325 689779615891533905859593)
                      ·
                        rfl

theorem cell23_1343341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1343341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343341 prefixEnd_1343341 := by exact prefixLift 1343341
  have htrace : WordTrace (prefixWord ++ tailWord_1343341) baseStart_1343341 baseEnd_1343341 := by
    simpa [prefixWord, tailWord_1343341, baseEnd_1343341] using wordTrace_append hprefix tailTrace_1343341
  have hstable : (prefixWord ++ tailWord_1343341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343341).length < 2 ^ (prefixWord ++ tailWord_1343341).sum := by decide
  have hdescent : baseEnd_1343341 < baseStart_1343341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343342 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_1343342 : Nat := 118140960795 + 1343342 * 2 ^ 59
def prefixEnd_1343342 : Nat := 4983230072969 + 3 ^ 40 * 1343342 * 2
def baseEnd_1343342 : Nat := 689780129372188401947089

theorem tailTrace_1343342 : CollatzResearch.WordTrace tailWord_1343342 prefixEnd_1343342 689780129372188401947089 := by
  unfold tailWord_1343342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6124463487413604174161035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32663805266205888928858853 6124463487413604174161035)
  ·
    refine ⟨9186695231120406261241553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6124463487413604174161035 9186695231120406261241553)
    ·
      refine ⟨6890021423340304695931165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9186695231120406261241553 6890021423340304695931165)
      ·
        refine ⟨2583758033752614260974187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6890021423340304695931165 2583758033752614260974187)
        ·
          refine ⟨3875637050628921391461281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583758033752614260974187 3875637050628921391461281)
          ·
            refine ⟨2906727787971691043595961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3875637050628921391461281 2906727787971691043595961)
            ·
              refine ⟨2180045840978768282696971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2906727787971691043595961 2180045840978768282696971)
              ·
                refine ⟨3270068761468152424045457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2180045840978768282696971 3270068761468152424045457)
                ·
                  refine ⟨2452551571101114318034093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3270068761468152424045457 2452551571101114318034093)
                  ·
                    refine ⟨919706839162917869262785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2452551571101114318034093 919706839162917869262785)
                    ·
                      refine ⟨689780129372188401947089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 919706839162917869262785 689780129372188401947089)
                      ·
                        rfl

theorem cell23_1343342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_1343342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343342 prefixEnd_1343342 := by exact prefixLift 1343342
  have htrace : WordTrace (prefixWord ++ tailWord_1343342) baseStart_1343342 baseEnd_1343342 := by
    simpa [prefixWord, tailWord_1343342, baseEnd_1343342] using wordTrace_append hprefix tailTrace_1343342
  have hstable : (prefixWord ++ tailWord_1343342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343342).length < 2 ^ (prefixWord ++ tailWord_1343342).sum := by decide
  have hdescent : baseEnd_1343342 < baseStart_1343342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343361 : List Nat := [1, 2, 4, 4, 12]
def baseStart_1343361 : Nat := 118140960795 + 1343361 * 2 ^ 59
def prefixEnd_1343361 : Nat := 4983230072969 + 3 ^ 40 * 1343361 * 2
def baseEnd_1343361 : Nat := 946213834711418144869

theorem tailTrace_1343361 : CollatzResearch.WordTrace tailWord_1343361 prefixEnd_1343361 946213834711418144869 := by
  unfold tailWord_1343361
  simp only [CollatzResearch.WordTrace]
  refine ⟨48996400886239999638229937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32664267257493333092153291 48996400886239999638229937)
  ·
    refine ⟨36747300664679999728672453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48996400886239999638229937 36747300664679999728672453)
    ·
      refine ⟨6890118874627499949126085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36747300664679999728672453 6890118874627499949126085)
      ·
        refine ⟨1291897288992656240461141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6890118874627499949126085 1291897288992656240461141)
        ·
          refine ⟨946213834711418144869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1291897288992656240461141 946213834711418144869)
          ·
            rfl

theorem cell23_1343361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 12].length) (baseStart_1343361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343361 prefixEnd_1343361 := by exact prefixLift 1343361
  have htrace : WordTrace (prefixWord ++ tailWord_1343361) baseStart_1343361 baseEnd_1343361 := by
    simpa [prefixWord, tailWord_1343361, baseEnd_1343361] using wordTrace_append hprefix tailTrace_1343361
  have hstable : (prefixWord ++ tailWord_1343361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343361).length < 2 ^ (prefixWord ++ tailWord_1343361).sum := by decide
  have hdescent : baseEnd_1343361 < baseStart_1343361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343371 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 3]
def baseStart_1343371 : Nat := 118140960795 + 1343371 * 2 ^ 59
def prefixEnd_1343371 : Nat := 4983230072969 + 3 ^ 40 * 1343371 * 2
def baseEnd_1343371 : Nat := 689795020311168788484455

theorem tailTrace_1343371 : CollatzResearch.WordTrace tailWord_1343371 prefixEnd_1343371 689795020311168788484455 := by
  unfold tailWord_1343371
  simp only [CollatzResearch.WordTrace]
  refine ⟨48996765616203771346093967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32664510410802514230729311 48996765616203771346093967)
  ·
    refine ⟨73495148424305657019140951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48996765616203771346093967 73495148424305657019140951)
    ·
      refine ⟨110242722636458485528711427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73495148424305657019140951 110242722636458485528711427)
      ·
        refine ⟨165364083954687728293067141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110242722636458485528711427 165364083954687728293067141)
        ·
          refine ⟨31005765741503949054950089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165364083954687728293067141 31005765741503949054950089)
          ·
            refine ⟨23254324306127961791212567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31005765741503949054950089 23254324306127961791212567)
            ·
              refine ⟨34881486459191942686818851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23254324306127961791212567 34881486459191942686818851)
              ·
                refine ⟨52322229688787914030228277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34881486459191942686818851 52322229688787914030228277)
                ·
                  refine ⟨4905209033323866940333901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52322229688787914030228277 4905209033323866940333901)
                  ·
                    refine ⟨1839453387496450102625213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4905209033323866940333901 1839453387496450102625213)
                    ·
                      refine ⟨689795020311168788484455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1839453387496450102625213 689795020311168788484455)
                      ·
                        rfl

theorem cell23_1343371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 3].length) (baseStart_1343371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343371 prefixEnd_1343371 := by exact prefixLift 1343371
  have htrace : WordTrace (prefixWord ++ tailWord_1343371) baseStart_1343371 baseEnd_1343371 := by
    simpa [prefixWord, tailWord_1343371, baseEnd_1343371] using wordTrace_append hprefix tailTrace_1343371
  have hstable : (prefixWord ++ tailWord_1343371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343371).length < 2 ^ (prefixWord ++ tailWord_1343371).sum := by decide
  have hdescent : baseEnd_1343371 < baseStart_1343371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343378 : List Nat := [3, 2, 3, 2, 1, 1, 3, 8]
def baseStart_1343378 : Nat := 118140960795 + 1343378 * 2 ^ 59
def prefixEnd_1343378 : Nat := 4983230072969 + 3 ^ 40 * 1343378 * 2
def baseEnd_1343378 : Nat := 25548096839842602262849

theorem tailTrace_1343378 : CollatzResearch.WordTrace tailWord_1343378 prefixEnd_1343378 25548096839842602262849 := by
  unfold tailWord_1343378
  simp only [CollatzResearch.WordTrace]
  refine ⟨12249255231794602885399697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32664680618118941027732525 12249255231794602885399697)
  ·
    refine ⟨9186941423845952164049773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12249255231794602885399697 9186941423845952164049773)
    ·
      refine ⟨3445103033942232061518665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9186941423845952164049773 3445103033942232061518665)
      ·
        refine ⟨2583827275456674046138999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3445103033942232061518665 2583827275456674046138999)
        ·
          refine ⟨3875740913185011069208499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583827275456674046138999 3875740913185011069208499)
          ·
            refine ⟨5813611369777516603812749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3875740913185011069208499 5813611369777516603812749)
            ·
              refine ⟨2180104263666568726429781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5813611369777516603812749 2180104263666568726429781)
              ·
                refine ⟨25548096839842602262849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2180104263666568726429781 25548096839842602262849)
                ·
                  rfl

theorem cell23_1343378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 8].length) (baseStart_1343378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343378 prefixEnd_1343378 := by exact prefixLift 1343378
  have htrace : WordTrace (prefixWord ++ tailWord_1343378) baseStart_1343378 baseEnd_1343378 := by
    simpa [prefixWord, tailWord_1343378, baseEnd_1343378] using wordTrace_append hprefix tailTrace_1343378
  have hstable : (prefixWord ++ tailWord_1343378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343378).length < 2 ^ (prefixWord ++ tailWord_1343378).sum := by decide
  have hdescent : baseEnd_1343378 < baseStart_1343378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343422 : List Nat := [4, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_1343422 : Nat := 118140960795 + 1343422 * 2 ^ 59
def prefixEnd_1343422 : Nat := 4983230072969 + 3 ^ 40 * 1343422 * 2
def baseEnd_1343422 : Nat := 689821207824548088946721

theorem tailTrace_1343422 : CollatzResearch.WordTrace tailWord_1343422 prefixEnd_1343422 689821207824548088946721 := by
  unfold tailWord_1343422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6124828217377375882025065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32665750492679338037467013 6124828217377375882025065)
  ·
    refine ⟨4593621163033031911518799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6124828217377375882025065 4593621163033031911518799)
    ·
      refine ⟨6890431744549547867278199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4593621163033031911518799 6890431744549547867278199)
      ·
        refine ⟨10335647616824321800917299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6890431744549547867278199 10335647616824321800917299)
        ·
          refine ⟨15503471425236482701375949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10335647616824321800917299 15503471425236482701375949)
          ·
            refine ⟨5813801784463681013015981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15503471425236482701375949 5813801784463681013015981)
            ·
              refine ⟨2180175669173880379880993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5813801784463681013015981 2180175669173880379880993)
              ·
                refine ⟨1635131751880410284910745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2180175669173880379880993 1635131751880410284910745)
                ·
                  refine ⟨1226348813910307713683059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1635131751880410284910745 1226348813910307713683059)
                  ·
                    refine ⟨1839523220865461570524589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1226348813910307713683059 1839523220865461570524589)
                    ·
                      refine ⟨689821207824548088946721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1839523220865461570524589 689821207824548088946721)
                      ·
                        rfl

theorem cell23_1343422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_1343422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343422 prefixEnd_1343422 := by exact prefixLift 1343422
  have htrace : WordTrace (prefixWord ++ tailWord_1343422) baseStart_1343422 baseEnd_1343422 := by
    simpa [prefixWord, tailWord_1343422, baseEnd_1343422] using wordTrace_append hprefix tailTrace_1343422
  have hstable : (prefixWord ++ tailWord_1343422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343422).length < 2 ^ (prefixWord ++ tailWord_1343422).sum := by decide
  have hdescent : baseEnd_1343422 < baseStart_1343422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343431 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_1343431 : Nat := 118140960795 + 1343431 * 2 ^ 59
def prefixEnd_1343431 : Nat := 4983230072969 + 3 ^ 40 * 1343431 * 2
def baseEnd_1343431 : Nat := 689825829150438553734179

theorem tailTrace_1343431 : CollatzResearch.WordTrace tailWord_1343431 prefixEnd_1343431 689825829150438553734179 := by
  unfold tailWord_1343431
  simp only [CollatzResearch.WordTrace]
  refine ⟨48998953995986401593278147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32665969330657601062185431 48998953995986401593278147)
  ·
    refine ⟨73498430993979602389917221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48998953995986401593278147 73498430993979602389917221)
    ·
      refine ⟨13780955811371175448109479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73498430993979602389917221 13780955811371175448109479)
      ·
        refine ⟨20671433717056763172164219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13780955811371175448109479 20671433717056763172164219)
        ·
          refine ⟨31007150575585144758246329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20671433717056763172164219 31007150575585144758246329)
          ·
            refine ⟨23255362931688858568684747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31007150575585144758246329 23255362931688858568684747)
            ·
              refine ⟨34883044397533287853027121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23255362931688858568684747 34883044397533287853027121)
              ·
                refine ⟨26162283298149965889770341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34883044397533287853027121 26162283298149965889770341)
                ·
                  refine ⟨4905428118403118604331939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26162283298149965889770341 4905428118403118604331939)
                  ·
                    refine ⟨7358142177604677906497909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4905428118403118604331939 7358142177604677906497909)
                    ·
                      refine ⟨689825829150438553734179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7358142177604677906497909 689825829150438553734179)
                      ·
                        rfl

theorem cell23_1343431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_1343431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343431 prefixEnd_1343431 := by exact prefixLift 1343431
  have htrace : WordTrace (prefixWord ++ tailWord_1343431) baseStart_1343431 baseEnd_1343431 := by
    simpa [prefixWord, tailWord_1343431, baseEnd_1343431] using wordTrace_append hprefix tailTrace_1343431
  have hstable : (prefixWord ++ tailWord_1343431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343431).length < 2 ^ (prefixWord ++ tailWord_1343431).sum := by decide
  have hdescent : baseEnd_1343431 < baseStart_1343431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343441 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_1343441 : Nat := 118140960795 + 1343441 * 2 ^ 59
def prefixEnd_1343441 : Nat := 4983230072969 + 3 ^ 40 * 1343441 * 2
def baseEnd_1343441 : Nat := 689830963956983514609133

theorem tailTrace_1343441 : CollatzResearch.WordTrace tailWord_1343441 prefixEnd_1343441 689830963956983514609133 := by
  unfold tailWord_1343441
  simp only [CollatzResearch.WordTrace]
  refine ⟨48999318725950173301142177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32666212483966782200761451 48999318725950173301142177)
  ·
    refine ⟨36749489044462629975856633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48999318725950173301142177 36749489044462629975856633)
    ·
      refine ⟨27562116783346972481892475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36749489044462629975856633 27562116783346972481892475)
      ·
        refine ⟨41343175175020458722838713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27562116783346972481892475 41343175175020458722838713)
        ·
          refine ⟨31007381381265344042129035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41343175175020458722838713 31007381381265344042129035)
          ·
            refine ⟨46511072071898016063193553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31007381381265344042129035 46511072071898016063193553)
            ·
              refine ⟨34883304053923512047395165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46511072071898016063193553 34883304053923512047395165)
              ·
                refine ⟨13081239020221317017773187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34883304053923512047395165 13081239020221317017773187)
                ·
                  refine ⟨19621858530331975526659781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13081239020221317017773187 19621858530331975526659781)
                  ·
                    refine ⟨3679098474437245411248709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19621858530331975526659781 3679098474437245411248709)
                    ·
                      refine ⟨689830963956983514609133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3679098474437245411248709 689830963956983514609133)
                      ·
                        rfl

theorem cell23_1343441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_1343441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343441 prefixEnd_1343441 := by exact prefixLift 1343441
  have htrace : WordTrace (prefixWord ++ tailWord_1343441) baseStart_1343441 baseEnd_1343441 := by
    simpa [prefixWord, tailWord_1343441, baseEnd_1343441] using wordTrace_append hprefix tailTrace_1343441
  have hstable : (prefixWord ++ tailWord_1343441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343441).length < 2 ^ (prefixWord ++ tailWord_1343441).sum := by decide
  have hdescent : baseEnd_1343441 < baseStart_1343441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343585 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_1343585 : Nat := 118140960795 + 1343585 * 2 ^ 59
def prefixEnd_1343585 : Nat := 4983230072969 + 3 ^ 40 * 1343585 * 2
def baseEnd_1343585 : Nat := 689904905171230951208471

theorem tailTrace_1343585 : CollatzResearch.WordTrace tailWord_1343585 prefixEnd_1343585 689904905171230951208471 := by
  unfold tailWord_1343585
  simp only [CollatzResearch.WordTrace]
  refine ⟨49004570837428485894384209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32669713891618990596256139 49004570837428485894384209)
  ·
    refine ⟨36753428128071364420788157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49004570837428485894384209 36753428128071364420788157)
    ·
      refine ⟨13782535548026761657795559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36753428128071364420788157 13782535548026761657795559)
      ·
        refine ⟨20673803322040142486693339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13782535548026761657795559 20673803322040142486693339)
        ·
          refine ⟨31010704983060213730040009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20673803322040142486693339 31010704983060213730040009)
          ·
            refine ⟨23258028737295160297530007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31010704983060213730040009 23258028737295160297530007)
            ·
              refine ⟨34887043105942740446295011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23258028737295160297530007 34887043105942740446295011)
              ·
                refine ⟨52330564658914110669442517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34887043105942740446295011 52330564658914110669442517)
                ·
                  refine ⟨1226497609193299468815059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 52330564658914110669442517 1226497609193299468815059)
                  ·
                    refine ⟨1839746413789949203222589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1226497609193299468815059 1839746413789949203222589)
                    ·
                      refine ⟨689904905171230951208471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1839746413789949203222589 689904905171230951208471)
                      ·
                        rfl

theorem cell23_1343585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_1343585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343585 prefixEnd_1343585 := by exact prefixLift 1343585
  have htrace : WordTrace (prefixWord ++ tailWord_1343585) baseStart_1343585 baseEnd_1343585 := by
    simpa [prefixWord, tailWord_1343585, baseEnd_1343585] using wordTrace_append hprefix tailTrace_1343585
  have hstable : (prefixWord ++ tailWord_1343585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343585).length < 2 ^ (prefixWord ++ tailWord_1343585).sum := by decide
  have hdescent : baseEnd_1343585 < baseStart_1343585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343602 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_1343602 : Nat := 118140960795 + 1343602 * 2 ^ 59
def prefixEnd_1343602 : Nat := 4983230072969 + 3 ^ 40 * 1343602 * 2
def baseEnd_1343602 : Nat := 689913634342357384695893

theorem tailTrace_1343602 : CollatzResearch.WordTrace tailWord_1343602 prefixEnd_1343602 689913634342357384695893 := by
  unfold tailWord_1343602
  simp only [CollatzResearch.WordTrace]
  refine ⟨12251297719591724449438265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32670127252244598531835373 12251297719591724449438265)
  ·
    refine ⟨9188473289693793337078699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12251297719591724449438265 9188473289693793337078699)
    ·
      refine ⟨13782709934540690005618049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9188473289693793337078699 13782709934540690005618049)
      ·
        refine ⟨10337032450905517504213537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13782709934540690005618049 10337032450905517504213537)
        ·
          refine ⟨7752774338179138128160153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10337032450905517504213537 7752774338179138128160153)
          ·
            refine ⟨5814580753634353596120115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7752774338179138128160153 5814580753634353596120115)
            ·
              refine ⟨8721871130451530394180173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5814580753634353596120115 8721871130451530394180173)
              ·
                refine ⟨3270701673919323897817565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8721871130451530394180173 3270701673919323897817565)
                ·
                  refine ⟨1226513127719746461681587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3270701673919323897817565 1226513127719746461681587)
                  ·
                    refine ⟨1839769691579619692522381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1226513127719746461681587 1839769691579619692522381)
                    ·
                      refine ⟨689913634342357384695893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1839769691579619692522381 689913634342357384695893)
                      ·
                        rfl

theorem cell23_1343602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_1343602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343602 prefixEnd_1343602 := by exact prefixLift 1343602
  have htrace : WordTrace (prefixWord ++ tailWord_1343602) baseStart_1343602 baseEnd_1343602 := by
    simpa [prefixWord, tailWord_1343602, baseEnd_1343602] using wordTrace_append hprefix tailTrace_1343602
  have hstable : (prefixWord ++ tailWord_1343602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343602).length < 2 ^ (prefixWord ++ tailWord_1343602).sum := by decide
  have hdescent : baseEnd_1343602 < baseStart_1343602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343625 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 2, 6, 2]
def baseStart_1343625 : Nat := 118140960795 + 1343625 * 2 ^ 59
def prefixEnd_1343625 : Nat := 4983230072969 + 3 ^ 40 * 1343625 * 2
def baseEnd_1343625 : Nat := 689925444397410794708287

theorem tailTrace_1343625 : CollatzResearch.WordTrace tailWord_1343625 prefixEnd_1343625 689925444397410794708287 := by
  unfold tailWord_1343625
  simp only [CollatzResearch.WordTrace]
  refine ⟨49006029757283572725840329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32670686504855715150560219 49006029757283572725840329)
  ·
    refine ⟨36754522317962679544380247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49006029757283572725840329 36754522317962679544380247)
    ·
      refine ⟨55131783476944019316570371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36754522317962679544380247 55131783476944019316570371)
      ·
        refine ⟨82697675215416028974855557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55131783476944019316570371 82697675215416028974855557)
        ·
          refine ⟨15505814102890505432785417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82697675215416028974855557 15505814102890505432785417)
          ·
            refine ⟨11629360577167879074589063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15505814102890505432785417 11629360577167879074589063)
            ·
              refine ⟨17444040865751818611883595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11629360577167879074589063 17444040865751818611883595)
              ·
                refine ⟨26166061298627727917825393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17444040865751818611883595 26166061298627727917825393)
                ·
                  refine ⟨19624545973970795938369045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26166061298627727917825393 19624545973970795938369045)
                  ·
                    refine ⟨919900592529881059611049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19624545973970795938369045 919900592529881059611049)
                    ·
                      refine ⟨689925444397410794708287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 919900592529881059611049 689925444397410794708287)
                      ·
                        rfl

theorem cell23_1343625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 6, 2].length) (baseStart_1343625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343625 prefixEnd_1343625 := by exact prefixLift 1343625
  have htrace : WordTrace (prefixWord ++ tailWord_1343625) baseStart_1343625 baseEnd_1343625 := by
    simpa [prefixWord, tailWord_1343625, baseEnd_1343625] using wordTrace_append hprefix tailTrace_1343625
  have hstable : (prefixWord ++ tailWord_1343625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343625).length < 2 ^ (prefixWord ++ tailWord_1343625).sum := by decide
  have hdescent : baseEnd_1343625 < baseStart_1343625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343645 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1343645 : Nat := 118140960795 + 1343645 * 2 ^ 59
def prefixEnd_1343645 : Nat := 4983230072969 + 3 ^ 40 * 1343645 * 2
def baseEnd_1343645 : Nat := 689935714010500716458195

theorem tailTrace_1343645 : CollatzResearch.WordTrace tailWord_1343645 prefixEnd_1343645 689935714010500716458195 := by
  unfold tailWord_1343645
  simp only [CollatzResearch.WordTrace]
  refine ⟨49006759217211116141568389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32671172811474077427712259 49006759217211116141568389)
  ·
    refine ⟨9188767353227084276544073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49006759217211116141568389 9188767353227084276544073)
    ·
      refine ⟨6891575514920313207408055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9188767353227084276544073 6891575514920313207408055)
      ·
        refine ⟨10337363272380469811112083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6891575514920313207408055 10337363272380469811112083)
        ·
          refine ⟨15506044908570704716668125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10337363272380469811112083 15506044908570704716668125)
          ·
            refine ⟨5814766840714014268750547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15506044908570704716668125 5814766840714014268750547)
            ·
              refine ⟨8722150261071021403125821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5814766840714014268750547 8722150261071021403125821)
              ·
                refine ⟨3270806347901633026172183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8722150261071021403125821 3270806347901633026172183)
                ·
                  refine ⟨4906209521852449539258275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3270806347901633026172183 4906209521852449539258275)
                  ·
                    refine ⟨7359314282778674308887413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4906209521852449539258275 7359314282778674308887413)
                    ·
                      refine ⟨689935714010500716458195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7359314282778674308887413 689935714010500716458195)
                      ·
                        rfl

theorem cell23_1343645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1343645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343645 prefixEnd_1343645 := by exact prefixLift 1343645
  have htrace : WordTrace (prefixWord ++ tailWord_1343645) baseStart_1343645 baseEnd_1343645 := by
    simpa [prefixWord, tailWord_1343645, baseEnd_1343645] using wordTrace_append hprefix tailTrace_1343645
  have hstable : (prefixWord ++ tailWord_1343645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343645).length < 2 ^ (prefixWord ++ tailWord_1343645).sum := by decide
  have hdescent : baseEnd_1343645 < baseStart_1343645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343646 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_1343646 : Nat := 118140960795 + 1343646 * 2 ^ 59
def prefixEnd_1343646 : Nat := 4983230072969 + 3 ^ 40 * 1343646 * 2
def baseEnd_1343646 : Nat := 689936227491155212545691

theorem tailTrace_1343646 : CollatzResearch.WordTrace tailWord_1343646 prefixEnd_1343646 689936227491155212545691 := by
  unfold tailWord_1343646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6125849461275936664044349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32671197126804995541569861 6125849461275936664044349)
  ·
    refine ⟨2297193547978476249016631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6125849461275936664044349 2297193547978476249016631)
    ·
      refine ⟨3445790321967714373524947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2297193547978476249016631 3445790321967714373524947)
      ·
        refine ⟨5168685482951571560287421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3445790321967714373524947 5168685482951571560287421)
        ·
          refine ⟨1938257056106839335107783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5168685482951571560287421 1938257056106839335107783)
          ·
            refine ⟨2907385584160259002661675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1938257056106839335107783 2907385584160259002661675)
            ·
              refine ⟨4361078376240388503992513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2907385584160259002661675 4361078376240388503992513)
              ·
                refine ⟨3270808782180291377994385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4361078376240388503992513 3270808782180291377994385)
                ·
                  refine ⟨2453106586635218533495789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3270808782180291377994385 2453106586635218533495789)
                  ·
                    refine ⟨919914969988206950060921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453106586635218533495789 919914969988206950060921)
                    ·
                      refine ⟨689936227491155212545691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 919914969988206950060921 689936227491155212545691)
                      ·
                        rfl

theorem cell23_1343646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_1343646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343646 prefixEnd_1343646 := by exact prefixLift 1343646
  have htrace : WordTrace (prefixWord ++ tailWord_1343646) baseStart_1343646 baseEnd_1343646 := by
    simpa [prefixWord, tailWord_1343646, baseEnd_1343646] using wordTrace_append hprefix tailTrace_1343646
  have hstable : (prefixWord ++ tailWord_1343646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343646).length < 2 ^ (prefixWord ++ tailWord_1343646).sum := by decide
  have hdescent : baseEnd_1343646 < baseStart_1343646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343648 : List Nat := [2, 1, 1, 4, 2, 2, 11]
def baseStart_1343648 : Nat := 118140960795 + 1343648 * 2 ^ 59
def prefixEnd_1343648 : Nat := 4983230072969 + 3 ^ 40 * 1343648 * 2
def baseEnd_1343648 : Nat := 8517743882129187712601

theorem tailTrace_1343648 : CollatzResearch.WordTrace tailWord_1343648 prefixEnd_1343648 8517743882129187712601 := by
  unfold tailWord_1343648
  simp only [CollatzResearch.WordTrace]
  refine ⟨24503434318100123826963799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32671245757466831769285065 24503434318100123826963799)
  ·
    refine ⟨36755151477150185740445699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24503434318100123826963799 36755151477150185740445699)
    ·
      refine ⟨55132727215725278610668549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36755151477150185740445699 55132727215725278610668549)
      ·
        refine ⟨10337386352948489739500353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55132727215725278610668549 10337386352948489739500353)
        ·
          refine ⟨7753039764711367304625265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10337386352948489739500353 7753039764711367304625265)
          ·
            refine ⟨5814779823533525478468949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7753039764711367304625265 5814779823533525478468949)
            ·
              refine ⟨8517743882129187712601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5814779823533525478468949 8517743882129187712601)
              ·
                rfl

theorem cell23_1343648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 11].length) (baseStart_1343648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343648 prefixEnd_1343648 := by exact prefixLift 1343648
  have htrace : WordTrace (prefixWord ++ tailWord_1343648) baseStart_1343648 baseEnd_1343648 := by
    simpa [prefixWord, tailWord_1343648, baseEnd_1343648] using wordTrace_append hprefix tailTrace_1343648
  have hstable : (prefixWord ++ tailWord_1343648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343648).length < 2 ^ (prefixWord ++ tailWord_1343648).sum := by decide
  have hdescent : baseEnd_1343648 < baseStart_1343648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343675 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 3]
def baseStart_1343675 : Nat := 118140960795 + 1343675 * 2 ^ 59
def prefixEnd_1343675 : Nat := 4983230072969 + 3 ^ 40 * 1343675 * 2
def baseEnd_1343675 : Nat := 689951118430135599083057

theorem tailTrace_1343675 : CollatzResearch.WordTrace tailWord_1343675 prefixEnd_1343675 689951118430135599083057 := by
  unfold tailWord_1343675
  simp only [CollatzResearch.WordTrace]
  refine ⟨49007853407102431265160479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32671902271401620843440319 49007853407102431265160479)
  ·
    refine ⟨73511780110653646897740719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49007853407102431265160479 73511780110653646897740719)
    ·
      refine ⟨110267670165980470346611079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73511780110653646897740719 110267670165980470346611079)
      ·
        refine ⟨165401505248970705519916619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110267670165980470346611079 165401505248970705519916619)
        ·
          refine ⟨248102257873456058279874929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165401505248970705519916619 248102257873456058279874929)
          ·
            refine ⟨186076693405092043709906197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248102257873456058279874929 186076693405092043709906197)
            ·
              refine ⟨8722345003363689548901853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 186076693405092043709906197 8722345003363689548901853)
              ·
                refine ⟨3270879376261383580838195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8722345003363689548901853 3270879376261383580838195)
                ·
                  refine ⟨4906319064392075371257293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3270879376261383580838195 4906319064392075371257293)
                  ·
                    refine ⟨1839869649147028264221485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4906319064392075371257293 1839869649147028264221485)
                    ·
                      refine ⟨689951118430135599083057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1839869649147028264221485 689951118430135599083057)
                      ·
                        rfl

theorem cell23_1343675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 3].length) (baseStart_1343675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343675 prefixEnd_1343675 := by exact prefixLift 1343675
  have htrace : WordTrace (prefixWord ++ tailWord_1343675) baseStart_1343675 baseEnd_1343675 := by
    simpa [prefixWord, tailWord_1343675, baseEnd_1343675] using wordTrace_append hprefix tailTrace_1343675
  have hstable : (prefixWord ++ tailWord_1343675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343675).length < 2 ^ (prefixWord ++ tailWord_1343675).sum := by decide
  have hdescent : baseEnd_1343675 < baseStart_1343675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343676 : List Nat := [2, 2, 2, 3, 4, 1, 1, 2, 1, 1, 4]
def baseStart_1343676 : Nat := 118140960795 + 1343676 * 2 ^ 59
def prefixEnd_1343676 : Nat := 4983230072969 + 3 ^ 40 * 1343676 * 2
def baseEnd_1343676 : Nat := 689951631910790095170553

theorem tailTrace_1343676 : CollatzResearch.WordTrace tailWord_1343676 prefixEnd_1343676 689951631910790095170553 := by
  unfold tailWord_1343676
  simp only [CollatzResearch.WordTrace]
  refine ⟨24503944940049404217973441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32671926586732538957297921 24503944940049404217973441)
  ·
    refine ⟨18377958705037053163480081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24503944940049404217973441 18377958705037053163480081)
    ·
      refine ⟨13783469028777789872610061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18377958705037053163480081 13783469028777789872610061)
      ·
        refine ⟨5168800885791671202228773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13783469028777789872610061 5168800885791671202228773)
        ·
          refine ⟨969150166085938350417895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5168800885791671202228773 969150166085938350417895)
          ·
            refine ⟨1453725249128907525626843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969150166085938350417895 1453725249128907525626843)
            ·
              refine ⟨2180587873693361288440265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1453725249128907525626843 2180587873693361288440265)
              ·
                refine ⟨1635440905270020966330199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2180587873693361288440265 1635440905270020966330199)
                ·
                  refine ⟨2453161357905031449495299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635440905270020966330199 2453161357905031449495299)
                  ·
                    refine ⟨3679742036857547174242949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2453161357905031449495299 3679742036857547174242949)
                    ·
                      refine ⟨689951631910790095170553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3679742036857547174242949 689951631910790095170553)
                      ·
                        rfl

theorem cell23_1343676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_1343676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343676 prefixEnd_1343676 := by exact prefixLift 1343676
  have htrace : WordTrace (prefixWord ++ tailWord_1343676) baseStart_1343676 baseEnd_1343676 := by
    simpa [prefixWord, tailWord_1343676, baseEnd_1343676] using wordTrace_append hprefix tailTrace_1343676
  have hstable : (prefixWord ++ tailWord_1343676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343676).length < 2 ^ (prefixWord ++ tailWord_1343676).sum := by decide
  have hdescent : baseEnd_1343676 < baseStart_1343676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343719 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_1343719 : Nat := 118140960795 + 1343719 * 2 ^ 59
def prefixEnd_1343719 : Nat := 4983230072969 + 3 ^ 40 * 1343719 * 2
def baseEnd_1343719 : Nat := 689973711578933426932855

theorem tailTrace_1343719 : CollatzResearch.WordTrace tailWord_1343719 prefixEnd_1343719 689973711578933426932855 := by
  unfold tailWord_1343719
  simp only [CollatzResearch.WordTrace]
  refine ⟨49009458218943026779762211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32672972145962017853174807 49009458218943026779762211)
  ·
    refine ⟨73514187328414540169643317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49009458218943026779762211 73514187328414540169643317)
    ·
      refine ⟨6891955062038863140904061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73514187328414540169643317 6891955062038863140904061)
      ·
        refine ⟨2584483148264573677839023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6891955062038863140904061 2584483148264573677839023)
        ·
          refine ⟨3876724722396860516758535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2584483148264573677839023 3876724722396860516758535)
          ·
            refine ⟨5815087083595290775137803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3876724722396860516758535 5815087083595290775137803)
            ·
              refine ⟨8722630625392936162706705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5815087083595290775137803 8722630625392936162706705)
              ·
                refine ⟨6541972969044702122030029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8722630625392936162706705 6541972969044702122030029)
                ·
                  refine ⟨2453239863391763295761261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6541972969044702122030029 2453239863391763295761261)
                  ·
                    refine ⟨919964948771911235910473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453239863391763295761261 919964948771911235910473)
                    ·
                      refine ⟨689973711578933426932855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 919964948771911235910473 689973711578933426932855)
                      ·
                        rfl

theorem cell23_1343719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_1343719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343719 prefixEnd_1343719 := by exact prefixLift 1343719
  have htrace : WordTrace (prefixWord ++ tailWord_1343719) baseStart_1343719 baseEnd_1343719 := by
    simpa [prefixWord, tailWord_1343719, baseEnd_1343719] using wordTrace_append hprefix tailTrace_1343719
  have hstable : (prefixWord ++ tailWord_1343719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343719).length < 2 ^ (prefixWord ++ tailWord_1343719).sum := by decide
  have hdescent : baseEnd_1343719 < baseStart_1343719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343745 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1343745 : Nat := 118140960795 + 1343745 * 2 ^ 59
def prefixEnd_1343745 : Nat := 4983230072969 + 3 ^ 40 * 1343745 * 2
def baseEnd_1343745 : Nat := 689987062075950325207735

theorem tailTrace_1343745 : CollatzResearch.WordTrace tailWord_1343745 prefixEnd_1343745 689987062075950325207735 := by
  unfold tailWord_1343745
  simp only [CollatzResearch.WordTrace]
  refine ⟨49010406516848833220208689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32673604344565888813472459 49010406516848833220208689)
  ·
    refine ⟨36757804887636624915156517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49010406516848833220208689 36757804887636624915156517)
    ·
      refine ⟨6892088416431867171591847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36757804887636624915156517 6892088416431867171591847)
      ·
        refine ⟨10338132624647800757387771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6892088416431867171591847 10338132624647800757387771)
        ·
          refine ⟨15507198936971701136081657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10338132624647800757387771 15507198936971701136081657)
          ·
            refine ⟨11630399202728775852061243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15507198936971701136081657 11630399202728775852061243)
            ·
              refine ⟨17445598804093163778091865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11630399202728775852061243 17445598804093163778091865)
              ·
                refine ⟨13084199103069872833568899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17445598804093163778091865 13084199103069872833568899)
                ·
                  refine ⟨19626298654604809250353349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13084199103069872833568899 19626298654604809250353349)
                  ·
                    refine ⟨3679930997738401734441253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19626298654604809250353349 3679930997738401734441253)
                    ·
                      refine ⟨689987062075950325207735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3679930997738401734441253 689987062075950325207735)
                      ·
                        rfl

theorem cell23_1343745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1343745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343745 prefixEnd_1343745 := by exact prefixLift 1343745
  have htrace : WordTrace (prefixWord ++ tailWord_1343745) baseStart_1343745 baseEnd_1343745 := by
    simpa [prefixWord, tailWord_1343745, baseEnd_1343745] using wordTrace_append hprefix tailTrace_1343745
  have hstable : (prefixWord ++ tailWord_1343745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343745).length < 2 ^ (prefixWord ++ tailWord_1343745).sum := by decide
  have hdescent : baseEnd_1343745 < baseStart_1343745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343806 : List Nat := [4, 2, 1, 2, 1, 4, 1, 3, 5]
def baseStart_1343806 : Nat := 118140960795 + 1343806 * 2 ^ 59
def prefixEnd_1343806 : Nat := 4983230072969 + 3 ^ 40 * 1343806 * 2
def baseEnd_1343806 : Nat := 76668709377319398504995

theorem tailTrace_1343806 : CollatzResearch.WordTrace tailWord_1343806 prefixEnd_1343806 76668709377319398504995 := by
  unfold tailWord_1343806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6126578921203480079772409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32675087579751893758786181 6126578921203480079772409)
  ·
    refine ⟨4594934190902610059829307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6126578921203480079772409 4594934190902610059829307)
    ·
      refine ⟨6892401286353915089743961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4594934190902610059829307 6892401286353915089743961)
      ·
        refine ⟨5169300964765436317307971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6892401286353915089743961 5169300964765436317307971)
        ·
          refine ⟨7753951447148154475961957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5169300964765436317307971 7753951447148154475961957)
          ·
            refine ⟨1453865896340278964242867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7753951447148154475961957 1453865896340278964242867)
            ·
              refine ⟨2180798844510418446364301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1453865896340278964242867 2180798844510418446364301)
              ·
                refine ⟨817799566691406917386613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2180798844510418446364301 817799566691406917386613)
                ·
                  refine ⟨76668709377319398504995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 817799566691406917386613 76668709377319398504995)
                  ·
                    rfl

theorem cell23_1343806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_1343806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343806 prefixEnd_1343806 := by exact prefixLift 1343806
  have htrace : WordTrace (prefixWord ++ tailWord_1343806) baseStart_1343806 baseEnd_1343806 := by
    simpa [prefixWord, tailWord_1343806, baseEnd_1343806] using wordTrace_append hprefix tailTrace_1343806
  have hstable : (prefixWord ++ tailWord_1343806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343806).length < 2 ^ (prefixWord ++ tailWord_1343806).sum := by decide
  have hdescent : baseEnd_1343806 < baseStart_1343806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343832 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 3, 4]
def baseStart_1343832 : Nat := 118140960795 + 1343832 * 2 ^ 59
def prefixEnd_1343832 : Nat := 4983230072969 + 3 ^ 40 * 1343832 * 2
def baseEnd_1343832 : Nat := 230010578297630494939945

theorem tailTrace_1343832 : CollatzResearch.WordTrace tailWord_1343832 prefixEnd_1343832 230010578297630494939945 := by
  unfold tailWord_1343832
  simp only [CollatzResearch.WordTrace]
  refine ⟨24506789833766823539312875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32675719778355764719083833 24506789833766823539312875)
  ·
    refine ⟨36760184750650235308969313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24506789833766823539312875 36760184750650235308969313)
    ·
      refine ⟨27570138562987676481726985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36760184750650235308969313 27570138562987676481726985)
      ·
        refine ⟨20677603922240757361295239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27570138562987676481726985 20677603922240757361295239)
        ·
          refine ⟨31016405883361136041942859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20677603922240757361295239 31016405883361136041942859)
          ·
            refine ⟨46524608825041704062914289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31016405883361136041942859 46524608825041704062914289)
            ·
              refine ⟨34893456618781278047185717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46524608825041704062914289 34893456618781278047185717)
              ·
                refine ⟨3271261558010744816923661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34893456618781278047185717 3271261558010744816923661)
                ·
                  refine ⟨1226723084254029306346373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3271261558010744816923661 1226723084254029306346373)
                  ·
                    refine ⟨230010578297630494939945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1226723084254029306346373 230010578297630494939945)
                    ·
                      rfl

theorem cell23_1343832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_1343832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343832 prefixEnd_1343832 := by exact prefixLift 1343832
  have htrace : WordTrace (prefixWord ++ tailWord_1343832) baseStart_1343832 baseEnd_1343832 := by
    simpa [prefixWord, tailWord_1343832, baseEnd_1343832] using wordTrace_append hprefix tailTrace_1343832
  have hstable : (prefixWord ++ tailWord_1343832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343832).length < 2 ^ (prefixWord ++ tailWord_1343832).sum := by decide
  have hdescent : baseEnd_1343832 < baseStart_1343832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343865 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 8]
def baseStart_1343865 : Nat := 118140960795 + 1343865 * 2 ^ 59
def prefixEnd_1343865 : Nat := 4983230072969 + 3 ^ 40 * 1343865 * 2
def baseEnd_1343865 : Nat := 690048679754489855707183

theorem tailTrace_1343865 : CollatzResearch.WordTrace tailWord_1343865 prefixEnd_1343865 690048679754489855707183 := by
  unfold tailWord_1343865
  simp only [CollatzResearch.WordTrace]
  refine ⟨49014783276414093714577049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32676522184276062476384699 49014783276414093714577049)
  ·
    refine ⟨36761087457310570285932787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49014783276414093714577049 36761087457310570285932787)
    ·
      refine ⟨55141631185965855428899181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36761087457310570285932787 55141631185965855428899181)
      ·
        refine ⟨20678111694737195785837193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55141631185965855428899181 20678111694737195785837193)
        ·
          refine ⟨15508583771052896839377895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20678111694737195785837193 15508583771052896839377895)
          ·
            refine ⟨23262875656579345259066843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15508583771052896839377895 23262875656579345259066843)
            ·
              refine ⟨34894313484869017888600265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23262875656579345259066843 34894313484869017888600265)
              ·
                refine ⟨26170735113651763416450199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34894313484869017888600265 26170735113651763416450199)
                ·
                  refine ⟨39256102670477645124675299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26170735113651763416450199 39256102670477645124675299)
                  ·
                    refine ⟨58884154005716467687012949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39256102670477645124675299 58884154005716467687012949)
                    ·
                      refine ⟨690048679754489855707183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 58884154005716467687012949 690048679754489855707183)
                      ·
                        rfl

theorem cell23_1343865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_1343865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343865 prefixEnd_1343865 := by exact prefixLift 1343865
  have htrace : WordTrace (prefixWord ++ tailWord_1343865) baseStart_1343865 baseEnd_1343865 := by
    simpa [prefixWord, tailWord_1343865, baseEnd_1343865] using wordTrace_append hprefix tailTrace_1343865
  have hstable : (prefixWord ++ tailWord_1343865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343865).length < 2 ^ (prefixWord ++ tailWord_1343865).sum := by decide
  have hdescent : baseEnd_1343865 < baseStart_1343865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343883 : List Nat := [1, 1, 1, 1, 4, 6, 2, 2, 1, 4]
def baseStart_1343883 : Nat := 118140960795 + 1343883 * 2 ^ 59
def prefixEnd_1343883 : Nat := 4983230072969 + 3 ^ 40 * 1343883 * 2
def baseEnd_1343883 : Nat := 230019307468756928427367

theorem tailTrace_1343883 : CollatzResearch.WordTrace tailWord_1343883 prefixEnd_1343883 230019307468756928427367 := by
  unfold tailWord_1343883
  simp only [CollatzResearch.WordTrace]
  refine ⟨49015439790348882788732303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32676959860232588525821535 49015439790348882788732303)
  ·
    refine ⟨73523159685523324183098455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49015439790348882788732303 73523159685523324183098455)
    ·
      refine ⟨110284739528284986274647683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73523159685523324183098455 110284739528284986274647683)
      ·
        refine ⟨165427109292427479411971525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110284739528284986274647683 165427109292427479411971525)
        ·
          refine ⟨31017582992330152389744661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165427109292427479411971525 31017582992330152389744661)
          ·
            refine ⟨1453949202765475893269281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31017582992330152389744661 1453949202765475893269281)
            ·
              refine ⟨1090461902074106919951961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1453949202765475893269281 1090461902074106919951961)
              ·
                refine ⟨817846426555580189963971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1090461902074106919951961 817846426555580189963971)
                ·
                  refine ⟨1226769639833370284945957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 817846426555580189963971 1226769639833370284945957)
                  ·
                    refine ⟨230019307468756928427367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1226769639833370284945957 230019307468756928427367)
                    ·
                      rfl

theorem cell23_1343883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 1, 4].length) (baseStart_1343883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343883 prefixEnd_1343883 := by exact prefixLift 1343883
  have htrace : WordTrace (prefixWord ++ tailWord_1343883) baseStart_1343883 baseEnd_1343883 := by
    simpa [prefixWord, tailWord_1343883, baseEnd_1343883] using wordTrace_append hprefix tailTrace_1343883
  have hstable : (prefixWord ++ tailWord_1343883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343883).length < 2 ^ (prefixWord ++ tailWord_1343883).sum := by decide
  have hdescent : baseEnd_1343883 < baseStart_1343883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343906 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_1343906 : Nat := 118140960795 + 1343906 * 2 ^ 59
def prefixEnd_1343906 : Nat := 4983230072969 + 3 ^ 40 * 1343906 * 2
def baseEnd_1343906 : Nat := 690069732461324195294495

theorem tailTrace_1343906 : CollatzResearch.WordTrace tailWord_1343906 prefixEnd_1343906 690069732461324195294495 := by
  unfold tailWord_1343906
  simp only [CollatzResearch.WordTrace]
  refine ⟨12254069667316389429204893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32677519112843705144546381 12254069667316389429204893)
  ·
    refine ⟨4595276125243646035951835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12254069667316389429204893 4595276125243646035951835)
    ·
      refine ⟨6892914187865469053927753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4595276125243646035951835 6892914187865469053927753)
      ·
        refine ⟨5169685640899101790445815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6892914187865469053927753 5169685640899101790445815)
        ·
          refine ⟨7754528461348652685668723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5169685640899101790445815 7754528461348652685668723)
          ·
            refine ⟨11631792692022979028503085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7754528461348652685668723 11631792692022979028503085)
            ·
              refine ⟨4361922259508617135688657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11631792692022979028503085 4361922259508617135688657)
              ·
                refine ⟨3271441694631462851766493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4361922259508617135688657 3271441694631462851766493)
                ·
                  refine ⟨1226790635486798569412435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3271441694631462851766493 1226790635486798569412435)
                  ·
                    refine ⟨1840185953230197854118653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1226790635486798569412435 1840185953230197854118653)
                    ·
                      refine ⟨690069732461324195294495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1840185953230197854118653 690069732461324195294495)
                      ·
                        rfl

theorem cell23_1343906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_1343906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343906 prefixEnd_1343906 := by exact prefixLift 1343906
  have htrace : WordTrace (prefixWord ++ tailWord_1343906) baseStart_1343906 baseEnd_1343906 := by
    simpa [prefixWord, tailWord_1343906, baseEnd_1343906] using wordTrace_append hprefix tailTrace_1343906
  have hstable : (prefixWord ++ tailWord_1343906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343906).length < 2 ^ (prefixWord ++ tailWord_1343906).sum := by decide
  have hdescent : baseEnd_1343906 < baseStart_1343906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343922 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_1343922 : Nat := 118140960795 + 1343922 * 2 ^ 59
def prefixEnd_1343922 : Nat := 4983230072969 + 3 ^ 40 * 1343922 * 2
def baseEnd_1343922 : Nat := 230025982717265377564807

theorem tailTrace_1343922 : CollatzResearch.WordTrace tailWord_1343922 prefixEnd_1343922 230025982717265377564807 := by
  unfold tailWord_1343922
  simp only [CollatzResearch.WordTrace]
  refine ⟨12254215559301898112350505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32677908158138394966268013 12254215559301898112350505)
  ·
    refine ⟨9190661669476423584262879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12254215559301898112350505 9190661669476423584262879)
    ·
      refine ⟨13785992504214635376394319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9190661669476423584262879 13785992504214635376394319)
      ·
        refine ⟨20678988756321953064591479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13785992504214635376394319 20678988756321953064591479)
        ·
          refine ⟨31018483134482929596887219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20678988756321953064591479 31018483134482929596887219)
          ·
            refine ⟨46527724701724394395330829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31018483134482929596887219 46527724701724394395330829)
            ·
              refine ⟨17447896763146647898249061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46527724701724394395330829 17447896763146647898249061)
              ·
                refine ⟨3271480643089996480921699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17447896763146647898249061 3271480643089996480921699)
                ·
                  refine ⟨4907220964634994721382549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3271480643089996480921699 4907220964634994721382549)
                  ·
                    refine ⟨230025982717265377564807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4907220964634994721382549 230025982717265377564807)
                    ·
                      rfl

theorem cell23_1343922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_1343922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343922 prefixEnd_1343922 := by exact prefixLift 1343922
  have htrace : WordTrace (prefixWord ++ tailWord_1343922) baseStart_1343922 baseEnd_1343922 := by
    simpa [prefixWord, tailWord_1343922, baseEnd_1343922] using wordTrace_append hprefix tailTrace_1343922
  have hstable : (prefixWord ++ tailWord_1343922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343922).length < 2 ^ (prefixWord ++ tailWord_1343922).sum := by decide
  have hdescent : baseEnd_1343922 < baseStart_1343922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343956 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_1343956 : Nat := 118140960795 + 1343956 * 2 ^ 59
def prefixEnd_1343956 : Nat := 4983230072969 + 3 ^ 40 * 1343956 * 2
def baseEnd_1343956 : Nat := 230031802164682999889755

theorem tailTrace_1343956 : CollatzResearch.WordTrace tailWord_1343956 prefixEnd_1343956 230031802164682999889755 := by
  unfold tailWord_1343956
  simp only [CollatzResearch.WordTrace]
  refine ⟨24509051159542208128069861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32678734879389610837426481 24509051159542208128069861)
  ·
    refine ⟨4595447092414164024013099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24509051159542208128069861 4595447092414164024013099)
    ·
      refine ⟨6893170638621246036019649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4595447092414164024013099 6893170638621246036019649)
      ·
        refine ⟨5169877978965934527014737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6893170638621246036019649 5169877978965934527014737)
        ·
          refine ⟨3877408484224450895261053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5169877978965934527014737 3877408484224450895261053)
          ·
            refine ⟨1454028181584169085722895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3877408484224450895261053 1454028181584169085722895)
            ·
              refine ⟨2181042272376253628584343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454028181584169085722895 2181042272376253628584343)
              ·
                refine ⟨3271563408564380442876515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2181042272376253628584343 3271563408564380442876515)
                ·
                  refine ⟨4907345112846570664314773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3271563408564380442876515 4907345112846570664314773)
                  ·
                    refine ⟨230031802164682999889755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4907345112846570664314773 230031802164682999889755)
                    ·
                      rfl

theorem cell23_1343956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_1343956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343956 prefixEnd_1343956 := by exact prefixLift 1343956
  have htrace : WordTrace (prefixWord ++ tailWord_1343956) baseStart_1343956 baseEnd_1343956 := by
    simpa [prefixWord, tailWord_1343956, baseEnd_1343956] using wordTrace_append hprefix tailTrace_1343956
  have hstable : (prefixWord ++ tailWord_1343956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343956).length < 2 ^ (prefixWord ++ tailWord_1343956).sum := by decide
  have hdescent : baseEnd_1343956 < baseStart_1343956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343979 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 6, 1, 3]
def baseStart_1343979 : Nat := 118140960795 + 1343979 * 2 ^ 59
def prefixEnd_1343979 : Nat := 4983230072969 + 3 ^ 40 * 1343979 * 2
def baseEnd_1343979 : Nat := 690107216549102409681659

theorem tailTrace_1343979 : CollatzResearch.WordTrace tailWord_1343979 prefixEnd_1343979 690107216549102409681659 := by
  unfold tailWord_1343979
  simp only [CollatzResearch.WordTrace]
  refine ⟨49018941198001091184226991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32679294132000727456151327 49018941198001091184226991)
  ·
    refine ⟨73528411797001636776340487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49018941198001091184226991 73528411797001636776340487)
    ·
      refine ⟨110292617695502455164510731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73528411797001636776340487 110292617695502455164510731)
      ·
        refine ⟨165438926543253682746766097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110292617695502455164510731 165438926543253682746766097)
        ·
          refine ⟨124079194907440262060074573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165438926543253682746766097 124079194907440262060074573)
          ·
            refine ⟨46529698090290098272527965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124079194907440262060074573 46529698090290098272527965)
            ·
              refine ⟨17448636783858786852197987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46529698090290098272527965 17448636783858786852197987)
              ·
                refine ⟨26172955175788180278296981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17448636783858786852197987 26172955175788180278296981)
                ·
                  refine ⟨1226857273865070950545171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26172955175788180278296981 1226857273865070950545171)
                  ·
                    refine ⟨1840285910797606425817757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1226857273865070950545171 1840285910797606425817757)
                    ·
                      refine ⟨690107216549102409681659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1840285910797606425817757 690107216549102409681659)
                      ·
                        rfl

theorem cell23_1343979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 1, 3].length) (baseStart_1343979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343979 prefixEnd_1343979 := by exact prefixLift 1343979
  have htrace : WordTrace (prefixWord ++ tailWord_1343979) baseStart_1343979 baseEnd_1343979 := by
    simpa [prefixWord, tailWord_1343979, baseEnd_1343979] using wordTrace_append hprefix tailTrace_1343979
  have hstable : (prefixWord ++ tailWord_1343979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343979).length < 2 ^ (prefixWord ++ tailWord_1343979).sum := by decide
  have hdescent : baseEnd_1343979 < baseStart_1343979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343986 : List Nat := [3, 2, 1, 4, 3, 1, 9]
def baseStart_1343986 : Nat := 118140960795 + 1343986 * 2 ^ 59
def prefixEnd_1343986 : Nat := 4983230072969 + 3 ^ 40 * 1343986 * 2
def baseEnd_1343986 : Nat := 8519886554489924472767

theorem tailTrace_1343986 : CollatzResearch.WordTrace tailWord_1343986 prefixEnd_1343986 8519886554489924472767 := by
  unfold tailWord_1343986
  simp only [CollatzResearch.WordTrace]
  refine ⟨12254799127243932844932953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32679464339317154253154541 12254799127243932844932953)
  ·
    refine ⟨9191099345432949633699715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12254799127243932844932953 9191099345432949633699715)
    ·
      refine ⟨13786649018149424450549573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9191099345432949633699715 13786649018149424450549573)
      ·
        refine ⟨2584996690903017084478045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13786649018149424450549573 2584996690903017084478045)
        ·
          refine ⟨969373759088631406679267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2584996690903017084478045 969373759088631406679267)
          ·
            refine ⟨1454060638632947110018901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969373759088631406679267 1454060638632947110018901)
            ·
              refine ⟨8519886554489924472767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1454060638632947110018901 8519886554489924472767)
              ·
                rfl

theorem cell23_1343986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 9].length) (baseStart_1343986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343986 prefixEnd_1343986 := by exact prefixLift 1343986
  have htrace : WordTrace (prefixWord ++ tailWord_1343986) baseStart_1343986 baseEnd_1343986 := by
    simpa [prefixWord, tailWord_1343986, baseEnd_1343986] using wordTrace_append hprefix tailTrace_1343986
  have hstable : (prefixWord ++ tailWord_1343986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343986).length < 2 ^ (prefixWord ++ tailWord_1343986).sum := by decide
  have hdescent : baseEnd_1343986 < baseStart_1343986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343992 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_1343992 : Nat := 118140960795 + 1343992 * 2 ^ 59
def prefixEnd_1343992 : Nat := 4983230072969 + 3 ^ 40 * 1343992 * 2
def baseEnd_1343992 : Nat := 690113891797610858819099

theorem tailTrace_1343992 : CollatzResearch.WordTrace tailWord_1343992 prefixEnd_1343992 690113891797610858819099 := by
  unfold tailWord_1343992
  simp only [CollatzResearch.WordTrace]
  refine ⟨24509707673476997202225115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32679610231302662936300153 24509707673476997202225115)
  ·
    refine ⟨36764561510215495803337673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24509707673476997202225115 36764561510215495803337673)
    ·
      refine ⟨27573421132661621852503255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36764561510215495803337673 27573421132661621852503255)
      ·
        refine ⟨41360131698992432778754883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27573421132661621852503255 41360131698992432778754883)
        ·
          refine ⟨62040197548488649168132325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41360131698992432778754883 62040197548488649168132325)
          ·
            refine ⟨11632537040341621719024811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62040197548488649168132325 11632537040341621719024811)
            ·
              refine ⟨17448805560512432578537217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11632537040341621719024811 17448805560512432578537217)
              ·
                refine ⟨13086604170384324433902913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17448805560512432578537217 13086604170384324433902913)
                ·
                  refine ⟨9814953127788243325427185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13086604170384324433902913 9814953127788243325427185)
                  ·
                    refine ⟨7361214845841182494070389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9814953127788243325427185 7361214845841182494070389)
                    ·
                      refine ⟨690113891797610858819099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7361214845841182494070389 690113891797610858819099)
                      ·
                        rfl

theorem cell23_1343992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_1343992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343992 prefixEnd_1343992 := by exact prefixLift 1343992
  have htrace : WordTrace (prefixWord ++ tailWord_1343992) baseStart_1343992 baseEnd_1343992 := by
    simpa [prefixWord, tailWord_1343992, baseEnd_1343992] using wordTrace_append hprefix tailTrace_1343992
  have hstable : (prefixWord ++ tailWord_1343992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343992).length < 2 ^ (prefixWord ++ tailWord_1343992).sum := by decide
  have hdescent : baseEnd_1343992 < baseStart_1343992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343996 : List Nat := [2, 2, 2, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_1343996 : Nat := 118140960795 + 1343996 * 2 ^ 59
def prefixEnd_1343996 : Nat := 4983230072969 + 3 ^ 40 * 1343996 * 2
def baseEnd_1343996 : Nat := 690115945720228843169081

theorem tailTrace_1343996 : CollatzResearch.WordTrace tailWord_1343996 prefixEnd_1343996 690115945720228843169081 := by
  unfold tailWord_1343996
  simp only [CollatzResearch.WordTrace]
  refine ⟨24509780619469751543797921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32679707492626335391730561 24509780619469751543797921)
  ·
    refine ⟨18382335464602313657848441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24509780619469751543797921 18382335464602313657848441)
    ·
      refine ⟨13786751598451735243386331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18382335464602313657848441 13786751598451735243386331)
      ·
        refine ⟨20680127397677602865079497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13786751598451735243386331 20680127397677602865079497)
        ·
          refine ⟨15510095548258202148809623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20680127397677602865079497 15510095548258202148809623)
          ·
            refine ⟨23265143322387303223214435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15510095548258202148809623 23265143322387303223214435)
            ·
              refine ⟨34897714983580954834821653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23265143322387303223214435 34897714983580954834821653)
              ·
                refine ⟨1635830389855357257882265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34897714983580954834821653 1635830389855357257882265)
                ·
                  refine ⟨1226872792391517943411699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1635830389855357257882265 1226872792391517943411699)
                  ·
                    refine ⟨1840309188587276915117549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1226872792391517943411699 1840309188587276915117549)
                    ·
                      refine ⟨690115945720228843169081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1840309188587276915117549 690115945720228843169081)
                      ·
                        rfl

theorem cell23_1343996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_1343996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1343996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1343996 prefixEnd_1343996 := by exact prefixLift 1343996
  have htrace : WordTrace (prefixWord ++ tailWord_1343996) baseStart_1343996 baseEnd_1343996 := by
    simpa [prefixWord, tailWord_1343996, baseEnd_1343996] using wordTrace_append hprefix tailTrace_1343996
  have hstable : (prefixWord ++ tailWord_1343996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343996).length < 2 ^ (prefixWord ++ tailWord_1343996).sum := by decide
  have hdescent : baseEnd_1343996 < baseStart_1343996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344069 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 1, 5, 3]
def baseStart_1344069 : Nat := 118140960795 + 1344069 * 2 ^ 59
def prefixEnd_1344069 : Nat := 4983230072969 + 3 ^ 40 * 1344069 * 2
def baseEnd_1344069 : Nat := 690153429808007057556245

theorem tailTrace_1344069 : CollatzResearch.WordTrace tailWord_1344069 prefixEnd_1344069 690153429808007057556245 := by
  unfold tailWord_1344069
  simp only [CollatzResearch.WordTrace]
  refine ⟨49022223767675036555003261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32681482511783357703335507 49022223767675036555003261)
  ·
    refine ⟨18383333912878138708126223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49022223767675036555003261 18383333912878138708126223)
    ·
      refine ⟨27575000869317208062189335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18383333912878138708126223 27575000869317208062189335)
      ·
        refine ⟨41362501303975812093284003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27575000869317208062189335 41362501303975812093284003)
        ·
          refine ⟨62043751955963718139926005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41362501303975812093284003 62043751955963718139926005)
          ·
            refine ⟨5816601745871598575618063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62043751955963718139926005 5816601745871598575618063)
            ·
              refine ⟨8724902618807397863427095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5816601745871598575618063 8724902618807397863427095)
              ·
                refine ⟨13087353928211096795140643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8724902618807397863427095 13087353928211096795140643)
                ·
                  refine ⟨19631030892316645192710965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13087353928211096795140643 19631030892316645192710965)
                  ·
                    refine ⟨1840409146154685486816653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19631030892316645192710965 1840409146154685486816653)
                    ·
                      refine ⟨690153429808007057556245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1840409146154685486816653 690153429808007057556245)
                      ·
                        rfl

theorem cell23_1344069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_1344069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344069 prefixEnd_1344069 := by exact prefixLift 1344069
  have htrace : WordTrace (prefixWord ++ tailWord_1344069) baseStart_1344069 baseEnd_1344069 := by
    simpa [prefixWord, tailWord_1344069, baseEnd_1344069] using wordTrace_append hprefix tailTrace_1344069
  have hstable : (prefixWord ++ tailWord_1344069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344069).length < 2 ^ (prefixWord ++ tailWord_1344069).sum := by decide
  have hdescent : baseEnd_1344069 < baseStart_1344069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344070 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_1344070 : Nat := 118140960795 + 1344070 * 2 ^ 59
def prefixEnd_1344070 : Nat := 4983230072969 + 3 ^ 40 * 1344070 * 2
def baseEnd_1344070 : Nat := 690153943288661553643741

theorem tailTrace_1344070 : CollatzResearch.WordTrace tailWord_1344070 prefixEnd_1344070 690153943288661553643741 := by
  unfold tailWord_1344070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1531945632520981678930927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32681506827114275817193109 1531945632520981678930927)
  ·
    refine ⟨2297918448781472518396391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1531945632520981678930927 2297918448781472518396391)
    ·
      refine ⟨3446877673172208777594587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2297918448781472518396391 3446877673172208777594587)
      ·
        refine ⟨5170316509758313166391881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3446877673172208777594587 5170316509758313166391881)
        ·
          refine ⟨3877737382318734874793911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5170316509758313166391881 3877737382318734874793911)
          ·
            refine ⟨5816606073478102312190867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3877737382318734874793911 5816606073478102312190867)
            ·
              refine ⟨8724909110217153468286301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5816606073478102312190867 8724909110217153468286301)
              ·
                refine ⟨3271840916331432550607363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8724909110217153468286301 3271840916331432550607363)
                ·
                  refine ⟨4907761374497148825911045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3271840916331432550607363 4907761374497148825911045)
                  ·
                    refine ⟨920205257718215404858321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4907761374497148825911045 920205257718215404858321)
                    ·
                      refine ⟨690153943288661553643741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 920205257718215404858321 690153943288661553643741)
                      ·
                        rfl

theorem cell23_1344070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_1344070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344070 prefixEnd_1344070 := by exact prefixLift 1344070
  have htrace : WordTrace (prefixWord ++ tailWord_1344070) baseStart_1344070 baseEnd_1344070 := by
    simpa [prefixWord, tailWord_1344070, baseEnd_1344070] using wordTrace_append hprefix tailTrace_1344070
  have hstable : (prefixWord ++ tailWord_1344070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344070).length < 2 ^ (prefixWord ++ tailWord_1344070).sum := by decide
  have hdescent : baseEnd_1344070 < baseStart_1344070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344104 : List Nat := [2, 1, 4, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_1344104 : Nat := 118140960795 + 1344104 * 2 ^ 59
def prefixEnd_1344104 : Nat := 4983230072969 + 3 ^ 40 * 1344104 * 2
def baseEnd_1344104 : Nat := 690171401630914420618585

theorem tailTrace_1344104 : CollatzResearch.WordTrace tailWord_1344104 prefixEnd_1344104 690171401630914420618585 := by
  unfold tailWord_1344104
  simp only [CollatzResearch.WordTrace]
  refine ⟨24511750161274118766263683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32682333548365491688351577 24511750161274118766263683)
  ·
    refine ⟨36767625241911178149395525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24511750161274118766263683 36767625241911178149395525)
    ·
      refine ⟨6893929732858345903011661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36767625241911178149395525 6893929732858345903011661)
      ·
        refine ⟨2585223649821879713629373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6893929732858345903011661 2585223649821879713629373)
        ·
          refine ⟨969458868683204892611015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2585223649821879713629373 969458868683204892611015)
          ·
            refine ⟨1454188303024807338916523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969458868683204892611015 1454188303024807338916523)
            ·
              refine ⟨2181282454537211008374785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454188303024807338916523 2181282454537211008374785)
              ·
                refine ⟨1635961840902908256281089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2181282454537211008374785 1635961840902908256281089)
                ·
                  refine ⟨1226971380677181192210817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1635961840902908256281089 1226971380677181192210817)
                  ·
                    refine ⟨920228535507885894158113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1226971380677181192210817 920228535507885894158113)
                    ·
                      refine ⟨690171401630914420618585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 920228535507885894158113 690171401630914420618585)
                      ·
                        rfl

theorem cell23_1344104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_1344104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344104 prefixEnd_1344104 := by exact prefixLift 1344104
  have htrace : WordTrace (prefixWord ++ tailWord_1344104) baseStart_1344104 baseEnd_1344104 := by
    simpa [prefixWord, tailWord_1344104, baseEnd_1344104] using wordTrace_append hprefix tailTrace_1344104
  have hstable : (prefixWord ++ tailWord_1344104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344104).length < 2 ^ (prefixWord ++ tailWord_1344104).sum := by decide
  have hdescent : baseEnd_1344104 < baseStart_1344104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344219 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 5]
def baseStart_1344219 : Nat := 118140960795 + 1344219 * 2 ^ 59
def prefixEnd_1344219 : Nat := 4983230072969 + 3 ^ 40 * 1344219 * 2
def baseEnd_1344219 : Nat := 690230451906181470680555

theorem tailTrace_1344219 : CollatzResearch.WordTrace tailWord_1344219 prefixEnd_1344219 690230451906181470680555 := by
  unfold tailWord_1344219
  simp only [CollatzResearch.WordTrace]
  refine ⟨49027694717131612172963711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32685129811421074781975807 49027694717131612172963711)
  ·
    refine ⟨73541542075697418259445567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49027694717131612172963711 73541542075697418259445567)
    ·
      refine ⟨110312313113546127389168351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73541542075697418259445567 110312313113546127389168351)
      ·
        refine ⟨165468469670319191083752527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110312313113546127389168351 165468469670319191083752527)
        ·
          refine ⟨248202704505478786625628791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165468469670319191083752527 248202704505478786625628791)
          ·
            refine ⟨372304056758218179938443187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248202704505478786625628791 372304056758218179938443187)
            ·
              refine ⟨558456085137327269907664781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372304056758218179938443187 558456085137327269907664781)
              ·
                refine ⟨209421031926497726215374293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 558456085137327269907664781 209421031926497726215374293)
                ·
                  refine ⟨4908305435777290458172835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 209421031926497726215374293 4908305435777290458172835)
                  ·
                    refine ⟨7362458153665935687259253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4908305435777290458172835 7362458153665935687259253)
                    ·
                      refine ⟨690230451906181470680555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7362458153665935687259253 690230451906181470680555)
                      ·
                        rfl

theorem cell23_1344219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 5].length) (baseStart_1344219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344219 prefixEnd_1344219 := by exact prefixLift 1344219
  have htrace : WordTrace (prefixWord ++ tailWord_1344219) baseStart_1344219 baseEnd_1344219 := by
    simpa [prefixWord, tailWord_1344219, baseEnd_1344219] using wordTrace_append hprefix tailTrace_1344219
  have hstable : (prefixWord ++ tailWord_1344219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344219).length < 2 ^ (prefixWord ++ tailWord_1344219).sum := by decide
  have hdescent : baseEnd_1344219 < baseStart_1344219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344227 : List Nat := [1, 1, 1, 7, 1, 2, 1, 4, 1, 1, 3]
def baseStart_1344227 : Nat := 118140960795 + 1344227 * 2 ^ 59
def prefixEnd_1344227 : Nat := 4983230072969 + 3 ^ 40 * 1344227 * 2
def baseEnd_1344227 : Nat := 690234559751417439380519

theorem tailTrace_1344227 : CollatzResearch.WordTrace tailWord_1344227 prefixEnd_1344227 690234559751417439380519 := by
  unfold tailWord_1344227
  simp only [CollatzResearch.WordTrace]
  refine ⟨49027986501102629539254935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32685324334068419692836623 49027986501102629539254935)
  ·
    refine ⟨73541979751653944308882403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49027986501102629539254935 73541979751653944308882403)
    ·
      refine ⟨110312969627480916463323605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73541979751653944308882403 110312969627480916463323605)
      ·
        refine ⟨2585460225644083979609147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 110312969627480916463323605 2585460225644083979609147)
        ·
          refine ⟨3878190338466125969413721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2585460225644083979609147 3878190338466125969413721)
          ·
            refine ⟨2908642753849594477060291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3878190338466125969413721 2908642753849594477060291)
            ·
              refine ⟨4362964130774391715590437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2908642753849594477060291 4362964130774391715590437)
              ·
                refine ⟨818055774520198446673207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4362964130774391715590437 818055774520198446673207)
                ·
                  refine ⟨1227083661780297670009811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818055774520198446673207 1227083661780297670009811)
                  ·
                    refine ⟨1840625492670446505014717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1227083661780297670009811 1840625492670446505014717)
                    ·
                      refine ⟨690234559751417439380519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1840625492670446505014717 690234559751417439380519)
                      ·
                        rfl

theorem cell23_1344227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_1344227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344227 prefixEnd_1344227 := by exact prefixLift 1344227
  have htrace : WordTrace (prefixWord ++ tailWord_1344227) baseStart_1344227 baseEnd_1344227 := by
    simpa [prefixWord, tailWord_1344227, baseEnd_1344227] using wordTrace_append hprefix tailTrace_1344227
  have hstable : (prefixWord ++ tailWord_1344227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344227).length < 2 ^ (prefixWord ++ tailWord_1344227).sum := by decide
  have hdescent : baseEnd_1344227 < baseStart_1344227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344244 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1344244 : Nat := 118140960795 + 1344244 * 2 ^ 59
def prefixEnd_1344244 : Nat := 4983230072969 + 3 ^ 40 * 1344244 * 2
def baseEnd_1344244 : Nat := 690243288922543872867941

theorem tailTrace_1344244 : CollatzResearch.WordTrace tailWord_1344244 prefixEnd_1344244 690243288922543872867941 := by
  unfold tailWord_1344244
  simp only [CollatzResearch.WordTrace]
  refine ⟨24514303271020520721311893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32685737694694027628415857 24514303271020520721311893)
  ·
    refine ⟨1149107965829086908811495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24514303271020520721311893 1149107965829086908811495)
    ·
      refine ⟨1723661948743630363217243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1149107965829086908811495 1723661948743630363217243)
      ·
        refine ⟨2585492923115445544825865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1723661948743630363217243 2585492923115445544825865)
        ·
          refine ⟨1939119692336584158619399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2585492923115445544825865 1939119692336584158619399)
          ·
            refine ⟨2908679538504876237929099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939119692336584158619399 2908679538504876237929099)
            ·
              refine ⟨4363019307757314356893649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2908679538504876237929099 4363019307757314356893649)
              ·
                refine ⟨3272264480817985767670237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4363019307757314356893649 3272264480817985767670237)
                ·
                  refine ⟨1227099180306744662876339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3272264480817985767670237 1227099180306744662876339)
                  ·
                    refine ⟨1840648770460116994314509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1227099180306744662876339 1840648770460116994314509)
                    ·
                      refine ⟨690243288922543872867941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1840648770460116994314509 690243288922543872867941)
                      ·
                        rfl

theorem cell23_1344244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1344244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344244 prefixEnd_1344244 := by exact prefixLift 1344244
  have htrace : WordTrace (prefixWord ++ tailWord_1344244) baseStart_1344244 baseEnd_1344244 := by
    simpa [prefixWord, tailWord_1344244, baseEnd_1344244] using wordTrace_append hprefix tailTrace_1344244
  have hstable : (prefixWord ++ tailWord_1344244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344244).length < 2 ^ (prefixWord ++ tailWord_1344244).sum := by decide
  have hdescent : baseEnd_1344244 < baseStart_1344244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344249 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 7]
def baseStart_1344249 : Nat := 118140960795 + 1344249 * 2 ^ 59
def prefixEnd_1344249 : Nat := 4983230072969 + 3 ^ 40 * 1344249 * 2
def baseEnd_1344249 : Nat := 690245856325816353305417

theorem tailTrace_1344249 : CollatzResearch.WordTrace tailWord_1344249 prefixEnd_1344249 690245856325816353305417 := by
  unfold tailWord_1344249
  simp only [CollatzResearch.WordTrace]
  refine ⟨49028788907022927296555801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32685859271348618197703867 49028788907022927296555801)
  ·
    refine ⟨36771591680267195472416851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49028788907022927296555801 36771591680267195472416851)
    ·
      refine ⟨55157387520400793208625277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36771591680267195472416851 55157387520400793208625277)
      ·
        refine ⟨20684020320150297453234479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55157387520400793208625277 20684020320150297453234479)
        ·
          refine ⟨31026030480225446179851719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20684020320150297453234479 31026030480225446179851719)
          ·
            refine ⟨46539045720338169269777579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31026030480225446179851719 46539045720338169269777579)
            ·
              refine ⟨69808568580507253904666369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46539045720338169269777579 69808568580507253904666369)
              ·
                refine ⟨52356426435380440428499777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69808568580507253904666369 52356426435380440428499777)
                ·
                  refine ⟨39267319826535330321374833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52356426435380440428499777 39267319826535330321374833)
                  ·
                    refine ⟨29450489869901497741031125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39267319826535330321374833 29450489869901497741031125)
                    ·
                      refine ⟨690245856325816353305417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29450489869901497741031125 690245856325816353305417)
                      ·
                        rfl

theorem cell23_1344249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_1344249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344249 prefixEnd_1344249 := by exact prefixLift 1344249
  have htrace : WordTrace (prefixWord ++ tailWord_1344249) baseStart_1344249 baseEnd_1344249 := by
    simpa [prefixWord, tailWord_1344249, baseEnd_1344249] using wordTrace_append hprefix tailTrace_1344249
  have hstable : (prefixWord ++ tailWord_1344249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344249).length < 2 ^ (prefixWord ++ tailWord_1344249).sum := by decide
  have hdescent : baseEnd_1344249 < baseStart_1344249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344253 : List Nat := [1, 4, 1, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_1344253 : Nat := 118140960795 + 1344253 * 2 ^ 59
def prefixEnd_1344253 : Nat := 4983230072969 + 3 ^ 40 * 1344253 * 2
def baseEnd_1344253 : Nat := 690247910248434337655399

theorem tailTrace_1344253 : CollatzResearch.WordTrace tailWord_1344253 prefixEnd_1344253 690247910248434337655399 := by
  unfold tailWord_1344253
  simp only [CollatzResearch.WordTrace]
  refine ⟨49028934799008435979701413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32685956532672290653134275 49028934799008435979701413)
  ·
    refine ⟨9192925274814081746194015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49028934799008435979701413 9192925274814081746194015)
    ·
      refine ⟨13789387912221122619291023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9192925274814081746194015 13789387912221122619291023)
      ·
        refine ⟨20684081868331683928936535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13789387912221122619291023 20684081868331683928936535)
        ·
          refine ⟨31026122802497525893404803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20684081868331683928936535 31026122802497525893404803)
          ·
            refine ⟨46539184203746288840107205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31026122802497525893404803 46539184203746288840107205)
            ·
              refine ⟨8726097038202429157520101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46539184203746288840107205 8726097038202429157520101)
              ·
                refine ⟨1636143194662955467035019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8726097038202429157520101 1636143194662955467035019)
                ·
                  refine ⟨2454214791994433200552529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636143194662955467035019 2454214791994433200552529)
                  ·
                    refine ⟨1840661093995824900414397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2454214791994433200552529 1840661093995824900414397)
                    ·
                      refine ⟨690247910248434337655399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1840661093995824900414397 690247910248434337655399)
                      ·
                        rfl

theorem cell23_1344253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_1344253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344253 prefixEnd_1344253 := by exact prefixLift 1344253
  have htrace : WordTrace (prefixWord ++ tailWord_1344253) baseStart_1344253 baseEnd_1344253 := by
    simpa [prefixWord, tailWord_1344253, baseEnd_1344253] using wordTrace_append hprefix tailTrace_1344253
  have hstable : (prefixWord ++ tailWord_1344253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344253).length < 2 ^ (prefixWord ++ tailWord_1344253).sum := by decide
  have hdescent : baseEnd_1344253 < baseStart_1344253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344263 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1344263 : Nat := 118140960795 + 1344263 * 2 ^ 59
def prefixEnd_1344263 : Nat := 4983230072969 + 3 ^ 40 * 1344263 * 2
def baseEnd_1344263 : Nat := 690253045054979298530353

theorem tailTrace_1344263 : CollatzResearch.WordTrace tailWord_1344263 prefixEnd_1344263 690253045054979298530353 := by
  unfold tailWord_1344263
  simp only [CollatzResearch.WordTrace]
  refine ⟨49029299528972207687565443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32686199685981471791710295 49029299528972207687565443)
  ·
    refine ⟨73543949293458311531348165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49029299528972207687565443 73543949293458311531348165)
    ·
      refine ⟨13789490492523433412127781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73543949293458311531348165 13789490492523433412127781)
      ·
        refine ⟨2585529467348143764773959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13789490492523433412127781 2585529467348143764773959)
        ·
          refine ⟨3878294201022215647160939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2585529467348143764773959 3878294201022215647160939)
          ·
            refine ⟨5817441301533323470741409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3878294201022215647160939 5817441301533323470741409)
            ·
              refine ⟨4363080976149992603056057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5817441301533323470741409 4363080976149992603056057)
              ·
                refine ⟨3272310732112494452292043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4363080976149992603056057 3272310732112494452292043)
                ·
                  refine ⟨4908466098168741678438065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3272310732112494452292043 4908466098168741678438065)
                  ·
                    refine ⟨3681349573626556258828549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4908466098168741678438065 3681349573626556258828549)
                    ·
                      refine ⟨690253045054979298530353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3681349573626556258828549 690253045054979298530353)
                      ·
                        rfl

theorem cell23_1344263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1344263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344263 prefixEnd_1344263 := by exact prefixLift 1344263
  have htrace : WordTrace (prefixWord ++ tailWord_1344263) baseStart_1344263 baseEnd_1344263 := by
    simpa [prefixWord, tailWord_1344263, baseEnd_1344263] using wordTrace_append hprefix tailTrace_1344263
  have hstable : (prefixWord ++ tailWord_1344263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344263).length < 2 ^ (prefixWord ++ tailWord_1344263).sum := by decide
  have hdescent : baseEnd_1344263 < baseStart_1344263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344318 : List Nat := [4, 2, 1, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_1344318 : Nat := 118140960795 + 1344318 * 2 ^ 59
def prefixEnd_1344318 : Nat := 4983230072969 + 3 ^ 40 * 1344318 * 2
def baseEnd_1344318 : Nat := 690281286490976583342601

theorem tailTrace_1344318 : CollatzResearch.WordTrace tailWord_1344318 prefixEnd_1344318 690281286490976583342601 := by
  unfold tailWord_1344318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6128913192971619010102201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32687537029181968053878405 6128913192971619010102201)
  ·
    refine ⟨4596684894728714257576651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6128913192971619010102201 4596684894728714257576651)
    ·
      refine ⟨6895027342093071386364977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4596684894728714257576651 6895027342093071386364977)
      ·
        refine ⟨5171270506569803539773733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6895027342093071386364977 5171270506569803539773733)
        ·
          refine ⟨969613219981838163707575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5171270506569803539773733 969613219981838163707575)
          ·
            refine ⟨1454419829972757245561363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969613219981838163707575 1454419829972757245561363)
            ·
              refine ⟨2181629744959135868342045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454419829972757245561363 2181629744959135868342045)
              ·
                refine ⟨818111154359675950628267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2181629744959135868342045 818111154359675950628267)
                ·
                  refine ⟨1227166731539513925942401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818111154359675950628267 1227166731539513925942401)
                  ·
                    refine ⟨920375048654635444456801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1227166731539513925942401 920375048654635444456801)
                    ·
                      refine ⟨690281286490976583342601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 920375048654635444456801 690281286490976583342601)
                      ·
                        rfl

theorem cell23_1344318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_1344318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344318 prefixEnd_1344318 := by exact prefixLift 1344318
  have htrace : WordTrace (prefixWord ++ tailWord_1344318) baseStart_1344318 baseEnd_1344318 := by
    simpa [prefixWord, tailWord_1344318, baseEnd_1344318] using wordTrace_append hprefix tailTrace_1344318
  have hstable : (prefixWord ++ tailWord_1344318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344318).length < 2 ^ (prefixWord ++ tailWord_1344318).sum := by decide
  have hdescent : baseEnd_1344318 < baseStart_1344318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344323 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 3, 4, 2]
def baseStart_1344323 : Nat := 118140960795 + 1344323 * 2 ^ 59
def prefixEnd_1344323 : Nat := 4983230072969 + 3 ^ 40 * 1344323 * 2
def baseEnd_1344323 : Nat := 690283853894249063780077

theorem tailTrace_1344323 : CollatzResearch.WordTrace tailWord_1344323 prefixEnd_1344323 690283853894249063780077 := by
  unfold tailWord_1344323
  simp only [CollatzResearch.WordTrace]
  refine ⟨49031487908754837934749623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32687658605836558623166415 49031487908754837934749623)
  ·
    refine ⟨73547231863132256902124435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49031487908754837934749623 73547231863132256902124435)
    ·
      refine ⟨110320847794698385353186653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73547231863132256902124435 110320847794698385353186653)
      ·
        refine ⟨41370317923011894507444995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110320847794698385353186653 41370317923011894507444995)
        ·
          refine ⟨62055476884517841761167493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41370317923011894507444995 62055476884517841761167493)
          ·
            refine ⟨11635401915847095330218905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62055476884517841761167493 11635401915847095330218905)
            ·
              refine ⟨8726551436885321497664179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11635401915847095330218905 8726551436885321497664179)
              ·
                refine ⟨13089827155327982246496269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8726551436885321497664179 13089827155327982246496269)
                ·
                  refine ⟨4908685183247993342436101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13089827155327982246496269 4908685183247993342436101)
                  ·
                    refine ⟨920378471858998751706769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4908685183247993342436101 920378471858998751706769)
                    ·
                      refine ⟨690283853894249063780077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 920378471858998751706769 690283853894249063780077)
                      ·
                        rfl

theorem cell23_1344323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 4, 2].length) (baseStart_1344323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344323 prefixEnd_1344323 := by exact prefixLift 1344323
  have htrace : WordTrace (prefixWord ++ tailWord_1344323) baseStart_1344323 baseEnd_1344323 := by
    simpa [prefixWord, tailWord_1344323, baseEnd_1344323] using wordTrace_append hprefix tailTrace_1344323
  have hstable : (prefixWord ++ tailWord_1344323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344323).length < 2 ^ (prefixWord ++ tailWord_1344323).sum := by decide
  have hdescent : baseEnd_1344323 < baseStart_1344323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344336 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 4]
def baseStart_1344336 : Nat := 118140960795 + 1344336 * 2 ^ 59
def prefixEnd_1344336 : Nat := 4983230072969 + 3 ^ 40 * 1344336 * 2
def baseEnd_1344336 : Nat := 690290529142757512917517

theorem tailTrace_1344336 : CollatzResearch.WordTrace tailWord_1344336 prefixEnd_1344336 690290529142757512917517 := by
  unfold tailWord_1344336
  simp only [CollatzResearch.WordTrace]
  refine ⟨24515981028853870577486431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32687974705138494103315241 24515981028853870577486431)
  ·
    refine ⟨36773971543280805866229647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24515981028853870577486431 36773971543280805866229647)
    ·
      refine ⟨55160957314921208799344471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36773971543280805866229647 55160957314921208799344471)
      ·
        refine ⟨82741435972381813199016707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55160957314921208799344471 82741435972381813199016707)
        ·
          refine ⟨124112153958572719798525061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82741435972381813199016707 124112153958572719798525061)
          ·
            refine ⟨23271028867232384962223449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124112153958572719798525061 23271028867232384962223449)
            ·
              refine ⟨17453271650424288721667587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23271028867232384962223449 17453271650424288721667587)
              ·
                refine ⟨26179907475636433082501381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17453271650424288721667587 26179907475636433082501381)
                ·
                  refine ⟨4908732651681831202969009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26179907475636433082501381 4908732651681831202969009)
                  ·
                    refine ⟨3681549488761373402226757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4908732651681831202969009 3681549488761373402226757)
                    ·
                      refine ⟨690290529142757512917517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3681549488761373402226757 690290529142757512917517)
                      ·
                        rfl

theorem cell23_1344336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_1344336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344336 prefixEnd_1344336 := by exact prefixLift 1344336
  have htrace : WordTrace (prefixWord ++ tailWord_1344336) baseStart_1344336 baseEnd_1344336 := by
    simpa [prefixWord, tailWord_1344336, baseEnd_1344336] using wordTrace_append hprefix tailTrace_1344336
  have hstable : (prefixWord ++ tailWord_1344336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344336).length < 2 ^ (prefixWord ++ tailWord_1344336).sum := by decide
  have hdescent : baseEnd_1344336 < baseStart_1344336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344393 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 2, 5]
def baseStart_1344393 : Nat := 118140960795 + 1344393 * 2 ^ 59
def prefixEnd_1344393 : Nat := 4983230072969 + 3 ^ 40 * 1344393 * 2
def baseEnd_1344393 : Nat := 230106599180021263301585

theorem tailTrace_1344393 : CollatzResearch.WordTrace tailWord_1344393 prefixEnd_1344393 230106599180021263301585 := by
  unfold tailWord_1344393
  simp only [CollatzResearch.WordTrace]
  refine ⟨49034041018501239889797833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32689360679000826593198555 49034041018501239889797833)
  ·
    refine ⟨36775530763875929917348375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49034041018501239889797833 36775530763875929917348375)
    ·
      refine ⟨55163296145813894876022563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36775530763875929917348375 55163296145813894876022563)
      ·
        refine ⟨82744944218720842314033845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55163296145813894876022563 82744944218720842314033845)
        ·
          refine ⟨7757338520505078966940673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82744944218720842314033845 7757338520505078966940673)
          ·
            refine ⟨5818003890378809225205505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7757338520505078966940673 5818003890378809225205505)
            ·
              refine ⟨4363502917784106918904129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5818003890378809225205505 4363502917784106918904129)
              ·
                refine ⟨3272627188338080189178097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4363502917784106918904129 3272627188338080189178097)
                ·
                  refine ⟨2454470391253560141883573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3272627188338080189178097 2454470391253560141883573)
                  ·
                    refine ⟨230106599180021263301585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2454470391253560141883573 230106599180021263301585)
                    ·
                      rfl

theorem cell23_1344393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 5].length) (baseStart_1344393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344393 prefixEnd_1344393 := by exact prefixLift 1344393
  have htrace : WordTrace (prefixWord ++ tailWord_1344393) baseStart_1344393 baseEnd_1344393 := by
    simpa [prefixWord, tailWord_1344393, baseEnd_1344393] using wordTrace_append hprefix tailTrace_1344393
  have hstable : (prefixWord ++ tailWord_1344393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344393).length < 2 ^ (prefixWord ++ tailWord_1344393).sum := by decide
  have hdescent : baseEnd_1344393 < baseStart_1344393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344413 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1344413 : Nat := 118140960795 + 1344413 * 2 ^ 59
def prefixEnd_1344413 : Nat := 4983230072969 + 3 ^ 40 * 1344413 * 2
def baseEnd_1344413 : Nat := 690330067153153711654663

theorem tailTrace_1344413 : CollatzResearch.WordTrace tailWord_1344413 prefixEnd_1344413 690330067153153711654663 := by
  unfold tailWord_1344413
  simp only [CollatzResearch.WordTrace]
  refine ⟨49034770478428783305525893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32689846985619188870350595 49034770478428783305525893)
  ·
    refine ⟨9194019464705396869786105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49034770478428783305525893 9194019464705396869786105)
    ·
      refine ⟨6895514598529047652339579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9194019464705396869786105 6895514598529047652339579)
      ·
        refine ⟨10343271897793571478509369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6895514598529047652339579 10343271897793571478509369)
        ·
          refine ⟨7757453923345178608882027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10343271897793571478509369 7757453923345178608882027)
          ·
            refine ⟨11636180885017767913323041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7757453923345178608882027 11636180885017767913323041)
            ·
              refine ⟨8727135663763325934992281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11636180885017767913323041 8727135663763325934992281)
              ·
                refine ⟨6545351747822494451244211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8727135663763325934992281 6545351747822494451244211)
                ·
                  refine ⟨9818027621733741676866317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6545351747822494451244211 9818027621733741676866317)
                  ·
                    refine ⟨3681760358150153128824869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9818027621733741676866317 3681760358150153128824869)
                    ·
                      refine ⟨690330067153153711654663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3681760358150153128824869 690330067153153711654663)
                      ·
                        rfl

theorem cell23_1344413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1344413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344413 prefixEnd_1344413 := by exact prefixLift 1344413
  have htrace : WordTrace (prefixWord ++ tailWord_1344413) baseStart_1344413 baseEnd_1344413 := by
    simpa [prefixWord, tailWord_1344413, baseEnd_1344413] using wordTrace_append hprefix tailTrace_1344413
  have hstable : (prefixWord ++ tailWord_1344413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344413).length < 2 ^ (prefixWord ++ tailWord_1344413).sum := by decide
  have hdescent : baseEnd_1344413 < baseStart_1344413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344537 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 3, 2, 2]
def baseStart_1344537 : Nat := 118140960795 + 1344537 * 2 ^ 59
def prefixEnd_1344537 : Nat := 4983230072969 + 3 ^ 40 * 1344537 * 2
def baseEnd_1344537 : Nat := 690393738754311226504093

theorem tailTrace_1344537 : CollatzResearch.WordTrace tailWord_1344537 prefixEnd_1344537 690393738754311226504093 := by
  unfold tailWord_1344537
  simp only [CollatzResearch.WordTrace]
  refine ⟨49039293129979552483039865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32692862086653034988693243 49039293129979552483039865)
  ·
    refine ⟨36779469847484664362279899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49039293129979552483039865 36779469847484664362279899)
    ·
      refine ⟨55169204771226996543419849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36779469847484664362279899 55169204771226996543419849)
      ·
        refine ⟨41376903578420247407564887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55169204771226996543419849 41376903578420247407564887)
        ·
          refine ⟨62065355367630371111347331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41376903578420247407564887 62065355367630371111347331)
          ·
            refine ⟨93098033051445556667020997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62065355367630371111347331 93098033051445556667020997)
            ·
              refine ⟨17455881197146041875066437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93098033051445556667020997 17455881197146041875066437)
              ·
                refine ⟨3272977724464882851574957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17455881197146041875066437 3272977724464882851574957)
                ·
                  refine ⟨1227366646674331069340609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3272977724464882851574957 1227366646674331069340609)
                  ·
                    refine ⟨920524985005748302005457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1227366646674331069340609 920524985005748302005457)
                    ·
                      refine ⟨690393738754311226504093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 920524985005748302005457 690393738754311226504093)
                      ·
                        rfl

theorem cell23_1344537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 2, 2].length) (baseStart_1344537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344537 prefixEnd_1344537 := by exact prefixLift 1344537
  have htrace : WordTrace (prefixWord ++ tailWord_1344537) baseStart_1344537 baseEnd_1344537 := by
    simpa [prefixWord, tailWord_1344537, baseEnd_1344537] using wordTrace_append hprefix tailTrace_1344537
  have hstable : (prefixWord ++ tailWord_1344537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344537).length < 2 ^ (prefixWord ++ tailWord_1344537).sum := by decide
  have hdescent : baseEnd_1344537 < baseStart_1344537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344543 : List Nat := [1, 1, 2, 4, 1, 3, 2, 9]
def baseStart_1344543 : Nat := 118140960795 + 1344543 * 2 ^ 59
def prefixEnd_1344543 : Nat := 4983230072969 + 3 ^ 40 * 1344543 * 2
def baseEnd_1344543 : Nat := 25570252579194007519595

theorem tailTrace_1344543 : CollatzResearch.WordTrace tailWord_1344543 prefixEnd_1344543 25570252579194007519595 := by
  unfold tailWord_1344543
  simp only [CollatzResearch.WordTrace]
  refine ⟨49039511967957815507758283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32693007978638543671838855 49039511967957815507758283)
  ·
    refine ⟨73559267951936723261637425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49039511967957815507758283 73559267951936723261637425)
    ·
      refine ⟨55169450963952542446228069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73559267951936723261637425 55169450963952542446228069)
      ·
        refine ⟨10344272055741101708667763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55169450963952542446228069 10344272055741101708667763)
        ·
          refine ⟨15516408083611652563001645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10344272055741101708667763 15516408083611652563001645)
          ·
            refine ⟨5818653031354369711125617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15516408083611652563001645 5818653031354369711125617)
            ·
              refine ⟨4363989773515777283344213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5818653031354369711125617 4363989773515777283344213)
              ·
                refine ⟨25570252579194007519595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4363989773515777283344213 25570252579194007519595)
                ·
                  rfl

theorem cell23_1344543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 9].length) (baseStart_1344543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344543 prefixEnd_1344543 := by exact prefixLift 1344543
  have htrace : WordTrace (prefixWord ++ tailWord_1344543) baseStart_1344543 baseEnd_1344543 := by
    simpa [prefixWord, tailWord_1344543, baseEnd_1344543] using wordTrace_append hprefix tailTrace_1344543
  have hstable : (prefixWord ++ tailWord_1344543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344543).length < 2 ^ (prefixWord ++ tailWord_1344543).sum := by decide
  have hdescent : baseEnd_1344543 < baseStart_1344543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344564 : List Nat := [2, 5, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_1344564 : Nat := 118140960795 + 1344564 * 2 ^ 59
def prefixEnd_1344564 : Nat := 4983230072969 + 3 ^ 40 * 1344564 * 2
def baseEnd_1344564 : Nat := 230135867577327540288823

theorem tailTrace_1344564 : CollatzResearch.WordTrace tailWord_1344564 prefixEnd_1344564 230135867577327540288823 := by
  unfold tailWord_1344564
  simp only [CollatzResearch.WordTrace]
  refine ⟨24520138950440868047136373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32693518600587824062848497 24520138950440868047136373)
  ·
    refine ⟨2298763026603831379419035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24520138950440868047136373 2298763026603831379419035)
    ·
      refine ⟨3448144539905747069128553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2298763026603831379419035 3448144539905747069128553)
      ·
        refine ⟨2586108404929310301846415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3448144539905747069128553 2586108404929310301846415)
        ·
          refine ⟨3879162607393965452769623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586108404929310301846415 3879162607393965452769623)
          ·
            refine ⟨5818743911090948179154435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3879162607393965452769623 5818743911090948179154435)
            ·
              refine ⟨8728115866636422268731653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5818743911090948179154435 8728115866636422268731653)
              ·
                refine ⟨1636521724994329175387185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8728115866636422268731653 1636521724994329175387185)
                ·
                  refine ⟨1227391293745746881540389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1636521724994329175387185 1227391293745746881540389)
                  ·
                    refine ⟨230135867577327540288823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1227391293745746881540389 230135867577327540288823)
                    ·
                      rfl

theorem cell23_1344564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_1344564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344564 prefixEnd_1344564 := by exact prefixLift 1344564
  have htrace : WordTrace (prefixWord ++ tailWord_1344564) baseStart_1344564 baseEnd_1344564 := by
    simpa [prefixWord, tailWord_1344564, baseEnd_1344564] using wordTrace_append hprefix tailTrace_1344564
  have hstable : (prefixWord ++ tailWord_1344564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344564).length < 2 ^ (prefixWord ++ tailWord_1344564).sum := by decide
  have hdescent : baseEnd_1344564 < baseStart_1344564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344577 : List Nat := [1, 2, 5, 1, 3, 2, 1, 8]
def baseStart_1344577 : Nat := 118140960795 + 1344577 * 2 ^ 59
def prefixEnd_1344577 : Nat := 4983230072969 + 3 ^ 40 * 1344577 * 2
def baseEnd_1344577 : Nat := 25570899184462632222367

theorem tailTrace_1344577 : CollatzResearch.WordTrace tailWord_1344577 prefixEnd_1344577 25570899184462632222367 := by
  unfold tailWord_1344577
  simp only [CollatzResearch.WordTrace]
  refine ⟨49040752049834639314495985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32693834699889759542997323 49040752049834639314495985)
  ·
    refine ⟨36780564037375979485871989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49040752049834639314495985 36780564037375979485871989)
    ·
      refine ⟨3448177878503998076800499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36780564037375979485871989 3448177878503998076800499)
      ·
        refine ⟨5172266817755997115200749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3448177878503998076800499 5172266817755997115200749)
        ·
          refine ⟨1939600056658498918200281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5172266817755997115200749 1939600056658498918200281)
          ·
            refine ⟨1454700042493874188650211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1939600056658498918200281 1454700042493874188650211)
            ·
              refine ⟨2182050063740811282975317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454700042493874188650211 2182050063740811282975317)
              ·
                refine ⟨25570899184462632222367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2182050063740811282975317 25570899184462632222367)
                ·
                  rfl

theorem cell23_1344577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 8].length) (baseStart_1344577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344577 prefixEnd_1344577 := by exact prefixLift 1344577
  have htrace : WordTrace (prefixWord ++ tailWord_1344577) baseStart_1344577 baseEnd_1344577 := by
    simpa [prefixWord, tailWord_1344577, baseEnd_1344577] using wordTrace_append hprefix tailTrace_1344577
  have hstable : (prefixWord ++ tailWord_1344577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344577).length < 2 ^ (prefixWord ++ tailWord_1344577).sum := by decide
  have hdescent : baseEnd_1344577 < baseStart_1344577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344597 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 3, 3, 2]
def baseStart_1344597 : Nat := 118140960795 + 1344597 * 2 ^ 59
def prefixEnd_1344597 : Nat := 4983230072969 + 3 ^ 40 * 1344597 * 2
def baseEnd_1344597 : Nat := 690424547593580991753817

theorem tailTrace_1344597 : CollatzResearch.WordTrace tailWord_1344597 prefixEnd_1344597 690424547593580991753817 := by
  unfold tailWord_1344597
  simp only [CollatzResearch.WordTrace]
  refine ⟨49041481509762182730224045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32694321006508121820149363 49041481509762182730224045)
  ·
    refine ⟨18390555566160818523834017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49041481509762182730224045 18390555566160818523834017)
    ·
      refine ⟨13792916674620613892875513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18390555566160818523834017 13792916674620613892875513)
      ·
        refine ⟨10344687505965460419656635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13792916674620613892875513 10344687505965460419656635)
        ·
          refine ⟨15517031258948190629484953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10344687505965460419656635 15517031258948190629484953)
          ·
            refine ⟨11637773444211142972113715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15517031258948190629484953 11637773444211142972113715)
            ·
              refine ⟨17456660166316714458170573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11637773444211142972113715 17456660166316714458170573)
              ·
                refine ⟨6546247562368767921813965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17456660166316714458170573 6546247562368767921813965)
                ·
                  refine ⟨2454842835888287970680237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6546247562368767921813965 2454842835888287970680237)
                  ·
                    refine ⟨920566063458107989005089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2454842835888287970680237 920566063458107989005089)
                    ·
                      refine ⟨690424547593580991753817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 920566063458107989005089 690424547593580991753817)
                      ·
                        rfl

theorem cell23_1344597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_1344597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344597 prefixEnd_1344597 := by exact prefixLift 1344597
  have htrace : WordTrace (prefixWord ++ tailWord_1344597) baseStart_1344597 baseEnd_1344597 := by
    simpa [prefixWord, tailWord_1344597, baseEnd_1344597] using wordTrace_append hprefix tailTrace_1344597
  have hstable : (prefixWord ++ tailWord_1344597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344597).length < 2 ^ (prefixWord ++ tailWord_1344597).sum := by decide
  have hdescent : baseEnd_1344597 < baseStart_1344597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344605 : List Nat := [1, 4, 4, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_1344605 : Nat := 118140960795 + 1344605 * 2 ^ 59
def prefixEnd_1344605 : Nat := 4983230072969 + 3 ^ 40 * 1344605 * 2
def baseEnd_1344605 : Nat := 690428655438816960453781

theorem tailTrace_1344605 : CollatzResearch.WordTrace tailWord_1344605 prefixEnd_1344605 690428655438816960453781 := by
  unfold tailWord_1344605
  simp only [CollatzResearch.WordTrace]
  refine ⟨49041773293733200096515269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32694515529155466731010179 49041773293733200096515269)
  ·
    refine ⟨9195332492574975018096613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49041773293733200096515269 9195332492574975018096613)
    ·
      refine ⟨1724124842357807815893115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9195332492574975018096613 1724124842357807815893115)
      ·
        refine ⟨2586187263536711723839673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724124842357807815893115 2586187263536711723839673)
        ·
          refine ⟨1939640447652533792879755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2586187263536711723839673 1939640447652533792879755)
          ·
            refine ⟨2909460671478800689319633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939640447652533792879755 2909460671478800689319633)
            ·
              refine ⟨2182095503609100516989725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2909460671478800689319633 2182095503609100516989725)
              ·
                refine ⟨818285813853412693871147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2182095503609100516989725 818285813853412693871147)
                ·
                  refine ⟨1227428720780119040806721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818285813853412693871147 1227428720780119040806721)
                  ·
                    refine ⟨920571540585089280605041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1227428720780119040806721 920571540585089280605041)
                    ·
                      refine ⟨690428655438816960453781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 920571540585089280605041 690428655438816960453781)
                      ·
                        rfl

theorem cell23_1344605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_1344605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344605 prefixEnd_1344605 := by exact prefixLift 1344605
  have htrace : WordTrace (prefixWord ++ tailWord_1344605) baseStart_1344605 baseEnd_1344605 := by
    simpa [prefixWord, tailWord_1344605, baseEnd_1344605] using wordTrace_append hprefix tailTrace_1344605
  have hstable : (prefixWord ++ tailWord_1344605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344605).length < 2 ^ (prefixWord ++ tailWord_1344605).sum := by decide
  have hdescent : baseEnd_1344605 < baseStart_1344605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344621 : List Nat := [1, 5, 1, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_1344621 : Nat := 118140960795 + 1344621 * 2 ^ 59
def prefixEnd_1344621 : Nat := 4983230072969 + 3 ^ 40 * 1344621 * 2
def baseEnd_1344621 : Nat := 690436871129288897853707

theorem tailTrace_1344621 : CollatzResearch.WordTrace tailWord_1344621 prefixEnd_1344621 690436871129288897853707 := by
  unfold tailWord_1344621
  simp only [CollatzResearch.WordTrace]
  refine ⟨49042356861675234829097717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32694904574450156552731811 49042356861675234829097717)
  ·
    refine ⟨4597720955782053265227911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49042356861675234829097717 4597720955782053265227911)
    ·
      refine ⟨6896581433673079897841867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4597720955782053265227911 6896581433673079897841867)
      ·
        refine ⟨10344872150509619846762801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6896581433673079897841867 10344872150509619846762801)
        ·
          refine ⟨7758654112882214885072101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10344872150509619846762801 7758654112882214885072101)
          ·
            refine ⟨1454747646165415290951019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7758654112882214885072101 1454747646165415290951019)
            ·
              refine ⟨2182121469248122936426529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454747646165415290951019 2182121469248122936426529)
              ·
                refine ⟨1636591101936092202319897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2182121469248122936426529 1636591101936092202319897)
                ·
                  refine ⟨1227443326452069151739923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1636591101936092202319897 1227443326452069151739923)
                  ·
                    refine ⟨1841164989678103727609885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1227443326452069151739923 1841164989678103727609885)
                    ·
                      refine ⟨690436871129288897853707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1841164989678103727609885 690436871129288897853707)
                      ·
                        rfl

theorem cell23_1344621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_1344621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344621 prefixEnd_1344621 := by exact prefixLift 1344621
  have htrace : WordTrace (prefixWord ++ tailWord_1344621) baseStart_1344621 baseEnd_1344621 := by
    simpa [prefixWord, tailWord_1344621, baseEnd_1344621] using wordTrace_append hprefix tailTrace_1344621
  have hstable : (prefixWord ++ tailWord_1344621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344621).length < 2 ^ (prefixWord ++ tailWord_1344621).sum := by decide
  have hdescent : baseEnd_1344621 < baseStart_1344621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344640 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 4]
def baseStart_1344640 : Nat := 118140960795 + 1344640 * 2 ^ 59
def prefixEnd_1344640 : Nat := 4983230072969 + 3 ^ 40 * 1344640 * 2
def baseEnd_1344640 : Nat := 690446627261724323516119

theorem tailTrace_1344640 : CollatzResearch.WordTrace tailWord_1344640 prefixEnd_1344640 690446627261724323516119 := by
  unfold tailWord_1344640
  simp only [CollatzResearch.WordTrace]
  refine ⟨24521524924303200537019687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32695366565737600716026249 24521524924303200537019687)
  ·
    refine ⟨36782287386454800805529531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24521524924303200537019687 36782287386454800805529531)
    ·
      refine ⟨55173431079682201208294297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36782287386454800805529531 55173431079682201208294297)
      ·
        refine ⟨41380073309761650906220723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55173431079682201208294297 41380073309761650906220723)
        ·
          refine ⟨62070109964642476359331085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41380073309761650906220723 62070109964642476359331085)
          ·
            refine ⟨23276291236740928634749157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62070109964642476359331085 23276291236740928634749157)
            ·
              refine ⟨4364304606888924119015467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23276291236740928634749157 4364304606888924119015467)
              ·
                refine ⟨6546456910333386178523201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4364304606888924119015467 6546456910333386178523201)
                ·
                  refine ⟨4909842682750039633892401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6546456910333386178523201 4909842682750039633892401)
                  ·
                    refine ⟨3682382012062529725419301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4909842682750039633892401 3682382012062529725419301)
                    ·
                      refine ⟨690446627261724323516119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3682382012062529725419301 690446627261724323516119)
                      ·
                        rfl

theorem cell23_1344640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_1344640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344640 prefixEnd_1344640 := by exact prefixLift 1344640
  have htrace : WordTrace (prefixWord ++ tailWord_1344640) baseStart_1344640 baseEnd_1344640 := by
    simpa [prefixWord, tailWord_1344640, baseEnd_1344640] using wordTrace_append hprefix tailTrace_1344640
  have hstable : (prefixWord ++ tailWord_1344640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344640).length < 2 ^ (prefixWord ++ tailWord_1344640).sum := by decide
  have hdescent : baseEnd_1344640 < baseStart_1344640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344644 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_1344644 : Nat := 118140960795 + 1344644 * 2 ^ 59
def prefixEnd_1344644 : Nat := 4983230072969 + 3 ^ 40 * 1344644 * 2
def baseEnd_1344644 : Nat := 690448681184342307866101

theorem tailTrace_1344644 : CollatzResearch.WordTrace tailWord_1344644 prefixEnd_1344644 690448681184342307866101 := by
  unfold tailWord_1344644
  simp only [CollatzResearch.WordTrace]
  refine ⟨24521597870295954878592493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32695463827061273171456657 24521597870295954878592493)
  ·
    refine ⟨9195599201360983079472185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24521597870295954878592493 9195599201360983079472185)
    ·
      refine ⟨6896699401020737309604139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9195599201360983079472185 6896699401020737309604139)
      ·
        refine ⟨10345049101531105964406209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6896699401020737309604139 10345049101531105964406209)
        ·
          refine ⟨7758786826148329473304657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10345049101531105964406209 7758786826148329473304657)
          ·
            refine ⟨5819090119611247104978493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7758786826148329473304657 5819090119611247104978493)
            ·
              refine ⟨2182158794854217664366935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5819090119611247104978493 2182158794854217664366935)
              ·
                refine ⟨3273238192281326496550403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182158794854217664366935 3273238192281326496550403)
                ·
                  refine ⟨4909857288421989744825605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273238192281326496550403 4909857288421989744825605)
                  ·
                    refine ⟨920598241579123077154801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4909857288421989744825605 920598241579123077154801)
                    ·
                      refine ⟨690448681184342307866101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 920598241579123077154801 690448681184342307866101)
                      ·
                        rfl

theorem cell23_1344644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_1344644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344644 prefixEnd_1344644 := by exact prefixLift 1344644
  have htrace : WordTrace (prefixWord ++ tailWord_1344644) baseStart_1344644 baseEnd_1344644 := by
    simpa [prefixWord, tailWord_1344644, baseEnd_1344644] using wordTrace_append hprefix tailTrace_1344644
  have hstable : (prefixWord ++ tailWord_1344644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344644).length < 2 ^ (prefixWord ++ tailWord_1344644).sum := by decide
  have hdescent : baseEnd_1344644 < baseStart_1344644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344650 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 7]
def baseStart_1344650 : Nat := 118140960795 + 1344650 * 2 ^ 59
def prefixEnd_1344650 : Nat := 4983230072969 + 3 ^ 40 * 1344650 * 2
def baseEnd_1344650 : Nat := 76716862452029920487897

theorem tailTrace_1344650 : CollatzResearch.WordTrace tailWord_1344650 prefixEnd_1344650 76716862452029920487897 := by
  unfold tailWord_1344650
  simp only [CollatzResearch.WordTrace]
  refine ⟨12260853644642543195475851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32695609719046781854602269 12260853644642543195475851)
  ·
    refine ⟨18391280466963814793213777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12260853644642543195475851 18391280466963814793213777)
    ·
      refine ⟨13793460350222861094910333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18391280466963814793213777 13793460350222861094910333)
      ·
        refine ⟨5172547631333572910591375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13793460350222861094910333 5172547631333572910591375)
        ·
          refine ⟨7758821447000359365887063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5172547631333572910591375 7758821447000359365887063)
          ·
            refine ⟨11638232170500539048830595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7758821447000359365887063 11638232170500539048830595)
            ·
              refine ⟨17457348255750808573245893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11638232170500539048830595 17457348255750808573245893)
              ·
                refine ⟨3273252797953276607483605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17457348255750808573245893 3273252797953276607483605)
                ·
                  refine ⟨76716862452029920487897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3273252797953276607483605 76716862452029920487897)
                  ·
                    rfl

theorem cell23_1344650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_1344650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344650 prefixEnd_1344650 := by exact prefixLift 1344650
  have htrace : WordTrace (prefixWord ++ tailWord_1344650) baseStart_1344650 baseEnd_1344650 := by
    simpa [prefixWord, tailWord_1344650, baseEnd_1344650] using wordTrace_append hprefix tailTrace_1344650
  have hstable : (prefixWord ++ tailWord_1344650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344650).length < 2 ^ (prefixWord ++ tailWord_1344650).sum := by decide
  have hdescent : baseEnd_1344650 < baseStart_1344650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344690 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1344690 : Nat := 118140960795 + 1344690 * 2 ^ 59
def prefixEnd_1344690 : Nat := 4983230072969 + 3 ^ 40 * 1344690 * 2
def baseEnd_1344690 : Nat := 690472301294449127890889

theorem tailTrace_1344690 : CollatzResearch.WordTrace tailWord_1344690 prefixEnd_1344690 690472301294449127890889 := by
  unfold tailWord_1344690
  simp only [CollatzResearch.WordTrace]
  refine ⟨12261218374606314903339881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32696582332283506408906349 12261218374606314903339881)
  ·
    refine ⟨9195913780954736177504911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12261218374606314903339881 9195913780954736177504911)
    ·
      refine ⟨13793870671432104266257367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9195913780954736177504911 13793870671432104266257367)
      ·
        refine ⟨20690806007148156399386051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13793870671432104266257367 20690806007148156399386051)
        ·
          refine ⟨31036209010722234599079077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20690806007148156399386051 31036209010722234599079077)
          ·
            refine ⟨5819289189510418987327327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31036209010722234599079077 5819289189510418987327327)
            ·
              refine ⟨8728933784265628480990991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5819289189510418987327327 8728933784265628480990991)
              ·
                refine ⟨13093400676398442721486487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8728933784265628480990991 13093400676398442721486487)
                ·
                  refine ⟨19640101014597664082229731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13093400676398442721486487 19640101014597664082229731)
                  ·
                    refine ⟨29460151521896496123344597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19640101014597664082229731 29460151521896496123344597)
                    ·
                      refine ⟨690472301294449127890889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29460151521896496123344597 690472301294449127890889)
                      ·
                        rfl

theorem cell23_1344690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1344690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344690 prefixEnd_1344690 := by exact prefixLift 1344690
  have htrace : WordTrace (prefixWord ++ tailWord_1344690) baseStart_1344690 baseEnd_1344690 := by
    simpa [prefixWord, tailWord_1344690, baseEnd_1344690] using wordTrace_append hprefix tailTrace_1344690
  have hstable : (prefixWord ++ tailWord_1344690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344690).length < 2 ^ (prefixWord ++ tailWord_1344690).sum := by decide
  have hdescent : baseEnd_1344690 < baseStart_1344690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344730 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1344730 : Nat := 118140960795 + 1344730 * 2 ^ 59
def prefixEnd_1344730 : Nat := 4983230072969 + 3 ^ 40 * 1344730 * 2
def baseEnd_1344730 : Nat := 690492840520628971390705

theorem tailTrace_1344730 : CollatzResearch.WordTrace tailWord_1344730 prefixEnd_1344730 690492840520628971390705 := by
  unfold tailWord_1344730
  simp only [CollatzResearch.WordTrace]
  refine ⟨12261583104570086611203911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32697554945520230963210429 12261583104570086611203911)
  ·
    refine ⟨18392374656855129916805867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12261583104570086611203911 18392374656855129916805867)
    ·
      refine ⟨27588561985282694875208801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18392374656855129916805867 27588561985282694875208801)
      ·
        refine ⟨20691421488962021156406601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27588561985282694875208801 20691421488962021156406601)
        ·
          refine ⟨15518566116721515867304951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20691421488962021156406601 15518566116721515867304951)
          ·
            refine ⟨23277849175082273800957427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15518566116721515867304951 23277849175082273800957427)
            ·
              refine ⟨34916773762623410701436141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23277849175082273800957427 34916773762623410701436141)
              ·
                refine ⟨13093790160983779013038553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34916773762623410701436141 13093790160983779013038553)
                ·
                  refine ⟨9820342620737834259778915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13093790160983779013038553 9820342620737834259778915)
                  ·
                    refine ⟨14730513931106751389668373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9820342620737834259778915 14730513931106751389668373)
                    ·
                      refine ⟨690492840520628971390705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14730513931106751389668373 690492840520628971390705)
                      ·
                        rfl

theorem cell23_1344730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1344730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344730 prefixEnd_1344730 := by exact prefixLift 1344730
  have htrace : WordTrace (prefixWord ++ tailWord_1344730) baseStart_1344730 baseEnd_1344730 := by
    simpa [prefixWord, tailWord_1344730, baseEnd_1344730] using wordTrace_append hprefix tailTrace_1344730
  have hstable : (prefixWord ++ tailWord_1344730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344730).length < 2 ^ (prefixWord ++ tailWord_1344730).sum := by decide
  have hdescent : baseEnd_1344730 < baseStart_1344730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344740 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 8]
def baseStart_1344740 : Nat := 118140960795 + 1344740 * 2 ^ 59
def prefixEnd_1344740 : Nat := 4983230072969 + 3 ^ 40 * 1344740 * 2
def baseEnd_1344740 : Nat := 76721997258574881362851

theorem tailTrace_1344740 : CollatzResearch.WordTrace tailWord_1344740 prefixEnd_1344740 76721997258574881362851 := by
  unfold tailWord_1344740
  simp only [CollatzResearch.WordTrace]
  refine ⟨24523348574122059076339837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32697798098829412101786449 24523348574122059076339837)
  ·
    refine ⟨9196255715295772153627439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24523348574122059076339837 9196255715295772153627439)
    ·
      refine ⟨13794383572943658230441159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9196255715295772153627439 13794383572943658230441159)
      ·
        refine ⟨20691575359415487345661739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13794383572943658230441159 20691575359415487345661739)
        ·
          refine ⟨31037363039123231018492609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20691575359415487345661739 31037363039123231018492609)
          ·
            refine ⟨23278022279342423263869457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31037363039123231018492609 23278022279342423263869457)
            ·
              refine ⟨17458516709506817447902093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23278022279342423263869457 17458516709506817447902093)
              ·
                refine ⟨6546943766065056542963285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17458516709506817447902093 6546943766065056542963285)
                ·
                  refine ⟨76721997258574881362851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6546943766065056542963285 76721997258574881362851)
                  ·
                    rfl

theorem cell23_1344740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_1344740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344740 prefixEnd_1344740 := by exact prefixLift 1344740
  have htrace : WordTrace (prefixWord ++ tailWord_1344740) baseStart_1344740 baseEnd_1344740 := by
    simpa [prefixWord, tailWord_1344740, baseEnd_1344740] using wordTrace_append hprefix tailTrace_1344740
  have hstable : (prefixWord ++ tailWord_1344740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344740).length < 2 ^ (prefixWord ++ tailWord_1344740).sum := by decide
  have hdescent : baseEnd_1344740 < baseStart_1344740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344827 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 3]
def baseStart_1344827 : Nat := 118140960795 + 1344827 * 2 ^ 59
def prefixEnd_1344827 : Nat := 4983230072969 + 3 ^ 40 * 1344827 * 2
def baseEnd_1344827 : Nat := 690542648144115091877759

theorem tailTrace_1344827 : CollatzResearch.WordTrace tailWord_1344827 prefixEnd_1344827 690542648144115091877759 := by
  unfold tailWord_1344827
  simp only [CollatzResearch.WordTrace]
  refine ⟨49049870298928932011096735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32699913532619288007397823 49049870298928932011096735)
  ·
    refine ⟨73574805448393398016645103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49049870298928932011096735 73574805448393398016645103)
    ·
      refine ⟨110362208172590097024967655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73574805448393398016645103 110362208172590097024967655)
      ·
        refine ⟨165543312258885145537451483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110362208172590097024967655 165543312258885145537451483)
        ·
          refine ⟨248314968388327718306177225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165543312258885145537451483 248314968388327718306177225)
          ·
            refine ⟨186236226291245788729632919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248314968388327718306177225 186236226291245788729632919)
            ·
              refine ⟨279354339436868683094449379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186236226291245788729632919 279354339436868683094449379)
              ·
                refine ⟨419031509155303024641674069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279354339436868683094449379 419031509155303024641674069)
                ·
                  refine ⟨2455262748956853660009809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 419031509155303024641674069 2455262748956853660009809)
                  ·
                    refine ⟨1841447061717640245007357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2455262748956853660009809 1841447061717640245007357)
                    ·
                      refine ⟨690542648144115091877759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1841447061717640245007357 690542648144115091877759)
                      ·
                        rfl

theorem cell23_1344827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 3].length) (baseStart_1344827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344827 prefixEnd_1344827 := by exact prefixLift 1344827
  have htrace : WordTrace (prefixWord ++ tailWord_1344827) baseStart_1344827 baseEnd_1344827 := by
    simpa [prefixWord, tailWord_1344827, baseEnd_1344827] using wordTrace_append hprefix tailTrace_1344827
  have hstable : (prefixWord ++ tailWord_1344827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344827).length < 2 ^ (prefixWord ++ tailWord_1344827).sum := by decide
  have hdescent : baseEnd_1344827 < baseStart_1344827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344837 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_1344837 : Nat := 118140960795 + 1344837 * 2 ^ 59
def prefixEnd_1344837 : Nat := 4983230072969 + 3 ^ 40 * 1344837 * 2
def baseEnd_1344837 : Nat := 690547782950660052752713

theorem tailTrace_1344837 : CollatzResearch.WordTrace tailWord_1344837 prefixEnd_1344837 690547782950660052752713 := by
  unfold tailWord_1344837
  simp only [CollatzResearch.WordTrace]
  refine ⟨49050235028892703718960765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32700156685928469145973843 49050235028892703718960765)
  ·
    refine ⟨18393838135834763894610287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49050235028892703718960765 18393838135834763894610287)
    ·
      refine ⟨27590757203752145841915431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18393838135834763894610287 27590757203752145841915431)
      ·
        refine ⟨41386135805628218762873147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27590757203752145841915431 41386135805628218762873147)
        ·
          refine ⟨62079203708442328144309721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41386135805628218762873147 62079203708442328144309721)
          ·
            refine ⟨46559402781331746108232291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62079203708442328144309721 46559402781331746108232291)
            ·
              refine ⟨69839104171997619162348437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46559402781331746108232291 69839104171997619162348437)
              ·
                refine ⟨3273708008062388398235083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69839104171997619162348437 3273708008062388398235083)
                ·
                  refine ⟨4910562012093582597352625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273708008062388398235083 4910562012093582597352625)
                  ·
                    refine ⟨3682921509070186948014469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4910562012093582597352625 3682921509070186948014469)
                    ·
                      refine ⟨690547782950660052752713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3682921509070186948014469 690547782950660052752713)
                      ·
                        rfl

theorem cell23_1344837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_1344837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344837 prefixEnd_1344837 := by exact prefixLift 1344837
  have htrace : WordTrace (prefixWord ++ tailWord_1344837) baseStart_1344837 baseEnd_1344837 := by
    simpa [prefixWord, tailWord_1344837, baseEnd_1344837] using wordTrace_append hprefix tailTrace_1344837
  have hstable : (prefixWord ++ tailWord_1344837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344837).length < 2 ^ (prefixWord ++ tailWord_1344837).sum := by decide
  have hdescent : baseEnd_1344837 < baseStart_1344837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344844 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 1, 1, 5]
def baseStart_1344844 : Nat := 118140960795 + 1344844 * 2 ^ 59
def prefixEnd_1344844 : Nat := 4983230072969 + 3 ^ 40 * 1344844 * 2
def baseEnd_1344844 : Nat := 690551377315241525365181

theorem tailTrace_1344844 : CollatzResearch.WordTrace tailWord_1344844 prefixEnd_1344844 690551377315241525365181 := by
  unfold tailWord_1344844
  simp only [CollatzResearch.WordTrace]
  refine ⟨24525245169933671957232793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32700326893244895942977057 24525245169933671957232793)
  ·
    refine ⟨18393933877450253967924595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24525245169933671957232793 18393933877450253967924595)
    ·
      refine ⟨27590900816175380951886893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18393933877450253967924595 27590900816175380951886893)
      ·
        refine ⟨10346587806065767856957585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27590900816175380951886893 10346587806065767856957585)
        ·
          refine ⟨7759940854549325892718189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10346587806065767856957585 7759940854549325892718189)
          ·
            refine ⟨2909977820455997209769321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7759940854549325892718189 2909977820455997209769321)
            ·
              refine ⟨2182483365341997907326991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2909977820455997209769321 2182483365341997907326991)
              ·
                refine ⟨3273725048012996860990487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182483365341997907326991 3273725048012996860990487)
                ·
                  refine ⟨4910587572019495291485731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273725048012996860990487 4910587572019495291485731)
                  ·
                    refine ⟨7365881358029242937228597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4910587572019495291485731 7365881358029242937228597)
                    ·
                      refine ⟨690551377315241525365181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7365881358029242937228597 690551377315241525365181)
                      ·
                        rfl

theorem cell23_1344844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_1344844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344844 prefixEnd_1344844 := by exact prefixLift 1344844
  have htrace : WordTrace (prefixWord ++ tailWord_1344844) baseStart_1344844 baseEnd_1344844 := by
    simpa [prefixWord, tailWord_1344844, baseEnd_1344844] using wordTrace_append hprefix tailTrace_1344844
  have hstable : (prefixWord ++ tailWord_1344844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344844).length < 2 ^ (prefixWord ++ tailWord_1344844).sum := by decide
  have hdescent : baseEnd_1344844 < baseStart_1344844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344845 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_1344845 : Nat := 118140960795 + 1344845 * 2 ^ 59
def prefixEnd_1344845 : Nat := 4983230072969 + 3 ^ 40 * 1344845 * 2
def baseEnd_1344845 : Nat := 690551890795896021452677

theorem tailTrace_1344845 : CollatzResearch.WordTrace tailWord_1344845 prefixEnd_1344845 690551890795896021452677 := by
  unfold tailWord_1344845
  simp only [CollatzResearch.WordTrace]
  refine ⟨49050526812863721085251989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32700351208575814056834659 49050526812863721085251989)
  ·
    refine ⟨2299243444352986925871187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49050526812863721085251989 2299243444352986925871187)
    ·
      refine ⟨3448865166529480388806781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299243444352986925871187 3448865166529480388806781)
      ·
        refine ⟨1293324437448555145802543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3448865166529480388806781 1293324437448555145802543)
        ·
          refine ⟨1939986656172832718703815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293324437448555145802543 1939986656172832718703815)
          ·
            refine ⟨2909979984259249078055723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939986656172832718703815 2909979984259249078055723)
            ·
              refine ⟨4364969976388873617083585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2909979984259249078055723 4364969976388873617083585)
              ·
                refine ⟨3273727482291655212812689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4364969976388873617083585 3273727482291655212812689)
                ·
                  refine ⟨2455295611718741409609517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3273727482291655212812689 2455295611718741409609517)
                  ·
                    refine ⟨920735854394528028603569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2455295611718741409609517 920735854394528028603569)
                    ·
                      refine ⟨690551890795896021452677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 920735854394528028603569 690551890795896021452677)
                      ·
                        rfl

theorem cell23_1344845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_1344845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344845 prefixEnd_1344845 := by exact prefixLift 1344845
  have htrace : WordTrace (prefixWord ++ tailWord_1344845) baseStart_1344845 baseEnd_1344845 := by
    simpa [prefixWord, tailWord_1344845, baseEnd_1344845] using wordTrace_append hprefix tailTrace_1344845
  have hstable : (prefixWord ++ tailWord_1344845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344845).length < 2 ^ (prefixWord ++ tailWord_1344845).sum := by decide
  have hdescent : baseEnd_1344845 < baseStart_1344845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344858 : List Nat := [3, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2]
def baseStart_1344858 : Nat := 118140960795 + 1344858 * 2 ^ 59
def prefixEnd_1344858 : Nat := 4983230072969 + 3 ^ 40 * 1344858 * 2
def baseEnd_1344858 : Nat := 690558566044404470590117

theorem tailTrace_1344858 : CollatzResearch.WordTrace tailWord_1344858 prefixEnd_1344858 690558566044404470590117 := by
  unfold tailWord_1344858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12262750240454156076368807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32700667307877749536983485 12262750240454156076368807)
  ·
    refine ⟨18394125360681234114553211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12262750240454156076368807 18394125360681234114553211)
    ·
      refine ⟨27591188041021851171829817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18394125360681234114553211 27591188041021851171829817)
      ·
        refine ⟨20693391030766388378872363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27591188041021851171829817 20693391030766388378872363)
        ·
          refine ⟨31040086546149582568308545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20693391030766388378872363 31040086546149582568308545)
          ·
            refine ⟨23280064909612186926231409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31040086546149582568308545 23280064909612186926231409)
            ·
              refine ⟨17460048682209140194673557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23280064909612186926231409 17460048682209140194673557)
              ·
                refine ⟨818439781978553446625323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17460048682209140194673557 818439781978553446625323)
                ·
                  refine ⟨1227659672967830169937985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818439781978553446625323 1227659672967830169937985)
                  ·
                    refine ⟨920744754725872627453489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1227659672967830169937985 920744754725872627453489)
                    ·
                      refine ⟨690558566044404470590117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 920744754725872627453489 690558566044404470590117)
                      ·
                        rfl

theorem cell23_1344858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_1344858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344858 prefixEnd_1344858 := by exact prefixLift 1344858
  have htrace : WordTrace (prefixWord ++ tailWord_1344858) baseStart_1344858 baseEnd_1344858 := by
    simpa [prefixWord, tailWord_1344858, baseEnd_1344858] using wordTrace_append hprefix tailTrace_1344858
  have hstable : (prefixWord ++ tailWord_1344858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344858).length < 2 ^ (prefixWord ++ tailWord_1344858).sum := by decide
  have hdescent : baseEnd_1344858 < baseStart_1344858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344868 : List Nat := [2, 3, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_1344868 : Nat := 118140960795 + 1344868 * 2 ^ 59
def prefixEnd_1344868 : Nat := 4983230072969 + 3 ^ 40 * 1344868 * 2
def baseEnd_1344868 : Nat := 230187900283649810488357

theorem tailTrace_1344868 : CollatzResearch.WordTrace tailWord_1344868 prefixEnd_1344868 230187900283649810488357 := by
  unfold tailWord_1344868
  simp only [CollatzResearch.WordTrace]
  refine ⟨24525682845890198006669629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32700910461186930675559505 24525682845890198006669629)
  ·
    refine ⟨9197131067208824252501111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24525682845890198006669629 9197131067208824252501111)
    ·
      refine ⟨13795696600813236378751667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9197131067208824252501111 13795696600813236378751667)
      ·
        refine ⟨20693544901219854568127501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13795696600813236378751667 20693544901219854568127501)
        ·
          refine ⟨7760079337957445463047813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20693544901219854568127501 7760079337957445463047813)
          ·
            refine ⟨1455014875867021024321465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7760079337957445463047813 1455014875867021024321465)
            ·
              refine ⟨1091261156900265768241099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455014875867021024321465 1091261156900265768241099)
              ·
                refine ⟨1636891735350398652361649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091261156900265768241099 1636891735350398652361649)
                ·
                  refine ⟨1227668801512798989271237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1636891735350398652361649 1227668801512798989271237)
                  ·
                    refine ⟨230187900283649810488357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1227668801512798989271237 230187900283649810488357)
                    ·
                      rfl

theorem cell23_1344868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_1344868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344868 prefixEnd_1344868 := by exact prefixLift 1344868
  have htrace : WordTrace (prefixWord ++ tailWord_1344868) baseStart_1344868 baseEnd_1344868 := by
    simpa [prefixWord, tailWord_1344868, baseEnd_1344868] using wordTrace_append hprefix tailTrace_1344868
  have hstable : (prefixWord ++ tailWord_1344868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344868).length < 2 ^ (prefixWord ++ tailWord_1344868).sum := by decide
  have hdescent : baseEnd_1344868 < baseStart_1344868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344878 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1344878 : Nat := 118140960795 + 1344878 * 2 ^ 59
def prefixEnd_1344878 : Nat := 4983230072969 + 3 ^ 40 * 1344878 * 2
def baseEnd_1344878 : Nat := 690568835657494392340025

theorem tailTrace_1344878 : CollatzResearch.WordTrace tailWord_1344878 prefixEnd_1344878 690568835657494392340025 := by
  unfold tailWord_1344878
  simp only [CollatzResearch.WordTrace]
  refine ⟨6131466302718020965150411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32701153614496111814135525 6131466302718020965150411)
  ·
    refine ⟨9197199454077031447725617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6131466302718020965150411 9197199454077031447725617)
    ·
      refine ⟨6897899590557773585794213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9197199454077031447725617 6897899590557773585794213)
      ·
        refine ⟨1293356173229582547336415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6897899590557773585794213 1293356173229582547336415)
        ·
          refine ⟨1940034259844373821004623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293356173229582547336415 1940034259844373821004623)
          ·
            refine ⟨2910051389766560731506935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940034259844373821004623 2910051389766560731506935)
            ·
              refine ⟨4365077084649841097260403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2910051389766560731506935 4365077084649841097260403)
              ·
                refine ⟨6547615626974761645890605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4365077084649841097260403 6547615626974761645890605)
                ·
                  refine ⟨2455355860115535617208977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6547615626974761645890605 2455355860115535617208977)
                  ·
                    refine ⟨1841516895086651712906733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2455355860115535617208977 1841516895086651712906733)
                    ·
                      refine ⟨690568835657494392340025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1841516895086651712906733 690568835657494392340025)
                      ·
                        rfl

theorem cell23_1344878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1344878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344878 prefixEnd_1344878 := by exact prefixLift 1344878
  have htrace : WordTrace (prefixWord ++ tailWord_1344878) baseStart_1344878 baseEnd_1344878 := by
    simpa [prefixWord, tailWord_1344878, baseEnd_1344878] using wordTrace_append hprefix tailTrace_1344878
  have hstable : (prefixWord ++ tailWord_1344878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344878).length < 2 ^ (prefixWord ++ tailWord_1344878).sum := by decide
  have hdescent : baseEnd_1344878 < baseStart_1344878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344901 : List Nat := [1, 3, 1, 1, 3, 1, 2, 5, 1, 3, 2]
def baseStart_1344901 : Nat := 118140960795 + 1344901 * 2 ^ 59
def prefixEnd_1344901 : Nat := 4983230072969 + 3 ^ 40 * 1344901 * 2
def baseEnd_1344901 : Nat := 690580645712547802352419

theorem tailTrace_1344901 : CollatzResearch.WordTrace tailWord_1344901 prefixEnd_1344901 690580645712547802352419 := by
  unfold tailWord_1344901
  simp only [CollatzResearch.WordTrace]
  refine ⟨49052569300660842649290557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32701712867107228432860371 49052569300660842649290557)
  ·
    refine ⟨18394713487747815993483959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49052569300660842649290557 18394713487747815993483959)
    ·
      refine ⟨27592070231621723990225939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18394713487747815993483959 27592070231621723990225939)
      ·
        refine ⟨41388105347432585985338909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27592070231621723990225939 41388105347432585985338909)
        ·
          refine ⟨15520539505287219744502091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41388105347432585985338909 15520539505287219744502091)
          ·
            refine ⟨23280809257930829616753137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15520539505287219744502091 23280809257930829616753137)
            ·
              refine ⟨17460606943448122212564853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23280809257930829616753137 17460606943448122212564853)
              ·
                refine ⟨1636931900948261457427955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17460606943448122212564853 1636931900948261457427955)
                ·
                  refine ⟨2455397851422392186141933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636931900948261457427955 2455397851422392186141933)
                  ·
                    refine ⟨920774194283397069803225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2455397851422392186141933 920774194283397069803225)
                    ·
                      refine ⟨690580645712547802352419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 920774194283397069803225 690580645712547802352419)
                      ·
                        rfl

theorem cell23_1344901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 3, 2].length) (baseStart_1344901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344901 prefixEnd_1344901 := by exact prefixLift 1344901
  have htrace : WordTrace (prefixWord ++ tailWord_1344901) baseStart_1344901 baseEnd_1344901 := by
    simpa [prefixWord, tailWord_1344901, baseEnd_1344901] using wordTrace_append hprefix tailTrace_1344901
  have hstable : (prefixWord ++ tailWord_1344901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344901).length < 2 ^ (prefixWord ++ tailWord_1344901).sum := by decide
  have hdescent : baseEnd_1344901 < baseStart_1344901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344907 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 2, 6]
def baseStart_1344907 : Nat := 118140960795 + 1344907 * 2 ^ 59
def prefixEnd_1344907 : Nat := 4983230072969 + 3 ^ 40 * 1344907 * 2
def baseEnd_1344907 : Nat := 230194575532158259625797

theorem tailTrace_1344907 : CollatzResearch.WordTrace tailWord_1344907 prefixEnd_1344907 230194575532158259625797 := by
  unfold tailWord_1344907
  simp only [CollatzResearch.WordTrace]
  refine ⟨49052788138639105674008975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32701858759092737116005983 49052788138639105674008975)
  ·
    refine ⟨73579182207958658511013463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49052788138639105674008975 73579182207958658511013463)
    ·
      refine ⟨110368773311937987766520195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73579182207958658511013463 110368773311937987766520195)
      ·
        refine ⟨165553159967906981649780293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110368773311937987766520195 165553159967906981649780293)
        ·
          refine ⟨31041217493982559059333805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165553159967906981649780293 31041217493982559059333805)
          ·
            refine ⟨11640456560243459647250177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31041217493982559059333805 11640456560243459647250177)
            ·
              refine ⟨8730342420182594735437633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11640456560243459647250177 8730342420182594735437633)
              ·
                refine ⟨6547756815136946051578225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8730342420182594735437633 6547756815136946051578225)
                ·
                  refine ⟨4910817611352709538683669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6547756815136946051578225 4910817611352709538683669)
                  ·
                    refine ⟨230194575532158259625797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4910817611352709538683669 230194575532158259625797)
                    ·
                      rfl

theorem cell23_1344907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 6].length) (baseStart_1344907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344907 prefixEnd_1344907 := by exact prefixLift 1344907
  have htrace : WordTrace (prefixWord ++ tailWord_1344907) baseStart_1344907 baseEnd_1344907 := by
    simpa [prefixWord, tailWord_1344907, baseEnd_1344907] using wordTrace_append hprefix tailTrace_1344907
  have hstable : (prefixWord ++ tailWord_1344907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344907).length < 2 ^ (prefixWord ++ tailWord_1344907).sum := by decide
  have hdescent : baseEnd_1344907 < baseStart_1344907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344917 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_1344917 : Nat := 118140960795 + 1344917 * 2 ^ 59
def prefixEnd_1344917 : Nat := 4983230072969 + 3 ^ 40 * 1344917 * 2
def baseEnd_1344917 : Nat := 690588861403019739752345

theorem tailTrace_1344917 : CollatzResearch.WordTrace tailWord_1344917 prefixEnd_1344917 690588861403019739752345 := by
  unfold tailWord_1344917
  simp only [CollatzResearch.WordTrace]
  refine ⟨49053152868602877381873005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32702101912401918254582003 49053152868602877381873005)
  ·
    refine ⟨18394932325726079018202377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49053152868602877381873005 18394932325726079018202377)
    ·
      refine ⟨13796199244294559263651783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18394932325726079018202377 13796199244294559263651783)
      ·
        refine ⟨20694298866441838895477675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13796199244294559263651783 20694298866441838895477675)
        ·
          refine ⟨31041448299662758343216513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20694298866441838895477675 31041448299662758343216513)
          ·
            refine ⟨23281086224747068757412385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31041448299662758343216513 23281086224747068757412385)
            ·
              refine ⟨17460814668560301568059289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23281086224747068757412385 17460814668560301568059289)
              ·
                refine ⟨13095611001420226176044467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17460814668560301568059289 13095611001420226176044467)
                ·
                  refine ⟨19643416502130339264066701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13095611001420226176044467 19643416502130339264066701)
                  ·
                    refine ⟨7366281188298877224025013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19643416502130339264066701 7366281188298877224025013)
                    ·
                      refine ⟨690588861403019739752345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7366281188298877224025013 690588861403019739752345)
                      ·
                        rfl

theorem cell23_1344917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_1344917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344917 prefixEnd_1344917 := by exact prefixLift 1344917
  have htrace : WordTrace (prefixWord ++ tailWord_1344917) baseStart_1344917 baseEnd_1344917 := by
    simpa [prefixWord, tailWord_1344917, baseEnd_1344917] using wordTrace_append hprefix tailTrace_1344917
  have hstable : (prefixWord ++ tailWord_1344917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344917).length < 2 ^ (prefixWord ++ tailWord_1344917).sum := by decide
  have hdescent : baseEnd_1344917 < baseStart_1344917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344931 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 1, 4, 2]
def baseStart_1344931 : Nat := 118140960795 + 1344931 * 2 ^ 59
def prefixEnd_1344931 : Nat := 4983230072969 + 3 ^ 40 * 1344931 * 2
def baseEnd_1344931 : Nat := 690596050132182684977281

theorem tailTrace_1344931 : CollatzResearch.WordTrace tailWord_1344931 prefixEnd_1344931 690596050132182684977281 := by
  unfold tailWord_1344931
  simp only [CollatzResearch.WordTrace]
  refine ⟨49053663490552157772882647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32702442327034771848588431 49053663490552157772882647)
  ·
    refine ⟨73580495235828236659323971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49053663490552157772882647 73580495235828236659323971)
    ·
      refine ⟨110370742853742354988985957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73580495235828236659323971 110370742853742354988985957)
      ·
        refine ⟨20694514285076691560434867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110370742853742354988985957 20694514285076691560434867)
        ·
          refine ⟨31041771427615037340652301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20694514285076691560434867 31041771427615037340652301)
          ·
            refine ⟨11640664285355639002744613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31041771427615037340652301 11640664285355639002744613)
            ·
              refine ⟨2182624553504182313014615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11640664285355639002744613 2182624553504182313014615)
              ·
                refine ⟨3273936830256273469521923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182624553504182313014615 3273936830256273469521923)
                ·
                  refine ⟨4910905245384410204282885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273936830256273469521923 4910905245384410204282885)
                  ·
                    refine ⟨920794733509576913303041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4910905245384410204282885 920794733509576913303041)
                    ·
                      refine ⟨690596050132182684977281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 920794733509576913303041 690596050132182684977281)
                      ·
                        rfl

theorem cell23_1344931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_1344931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1344931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1344931 prefixEnd_1344931 := by exact prefixLift 1344931
  have htrace : WordTrace (prefixWord ++ tailWord_1344931) baseStart_1344931 baseEnd_1344931 := by
    simpa [prefixWord, tailWord_1344931, baseEnd_1344931] using wordTrace_append hprefix tailTrace_1344931
  have hstable : (prefixWord ++ tailWord_1344931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344931).length < 2 ^ (prefixWord ++ tailWord_1344931).sum := by decide
  have hdescent : baseEnd_1344931 < baseStart_1344931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345005 : List Nat := [1, 5, 1, 3, 2, 2, 1, 3, 5]
def baseStart_1345005 : Nat := 118140960795 + 1345005 * 2 ^ 59
def prefixEnd_1345005 : Nat := 4983230072969 + 3 ^ 40 * 1345005 * 2
def baseEnd_1345005 : Nat := 76737116411179488383549

theorem tailTrace_1345005 : CollatzResearch.WordTrace tailWord_1345005 prefixEnd_1345005 76737116411179488383549 := by
  unfold tailWord_1345005
  simp only [CollatzResearch.WordTrace]
  refine ⟨49056362492284068411076469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32704241661522712274050979 49056362492284068411076469)
  ·
    refine ⟨4599033983651631413538419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49056362492284068411076469 4599033983651631413538419)
    ·
      refine ⟨6898550975477447120307629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4599033983651631413538419 6898550975477447120307629)
      ·
        refine ⟨2586956615804042670115361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6898550975477447120307629 2586956615804042670115361)
        ·
          refine ⟨1940217461853032002586521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2586956615804042670115361 1940217461853032002586521)
          ·
            refine ⟨1455163096389774001939891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1940217461853032002586521 1455163096389774001939891)
            ·
              refine ⟨2182744644584661002909837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455163096389774001939891 2182744644584661002909837)
              ·
                refine ⟨818529241719247876091189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2182744644584661002909837 818529241719247876091189)
                ·
                  refine ⟨76737116411179488383549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 818529241719247876091189 76737116411179488383549)
                  ·
                    rfl

theorem cell23_1345005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_1345005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345005 prefixEnd_1345005 := by exact prefixLift 1345005
  have htrace : WordTrace (prefixWord ++ tailWord_1345005) baseStart_1345005 baseEnd_1345005 := by
    simpa [prefixWord, tailWord_1345005, baseEnd_1345005] using wordTrace_append hprefix tailTrace_1345005
  have hstable : (prefixWord ++ tailWord_1345005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345005).length < 2 ^ (prefixWord ++ tailWord_1345005).sum := by decide
  have hdescent : baseEnd_1345005 < baseStart_1345005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345021 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_1345021 : Nat := 118140960795 + 1345021 * 2 ^ 59
def prefixEnd_1345021 : Nat := 4983230072969 + 3 ^ 40 * 1345021 * 2
def baseEnd_1345021 : Nat := 690642263391087332851867

theorem tailTrace_1345021 : CollatzResearch.WordTrace tailWord_1345021 prefixEnd_1345021 690642263391087332851867 := by
  unfold tailWord_1345021
  simp only [CollatzResearch.WordTrace]
  refine ⟨49056946060226103143658917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32704630706817402095772611 49056946060226103143658917)
  ·
    refine ⟨9198177386292394339436047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49056946060226103143658917 9198177386292394339436047)
    ·
      refine ⟨13797266079438591509154071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9198177386292394339436047 13797266079438591509154071)
      ·
        refine ⟨20695899119157887263731107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13797266079438591509154071 20695899119157887263731107)
        ·
          refine ⟨31043848678736830895596661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20695899119157887263731107 31043848678736830895596661)
          ·
            refine ⟨2910360813631577896462187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31043848678736830895596661 2910360813631577896462187)
            ·
              refine ⟨4365541220447366844693281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2910360813631577896462187 4365541220447366844693281)
              ·
                refine ⟨3274155915335525133519961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4365541220447366844693281 3274155915335525133519961)
                ·
                  refine ⟨2455616936501643850139971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3274155915335525133519961 2455616936501643850139971)
                  ·
                    refine ⟨3683425404752465775209957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2455616936501643850139971 3683425404752465775209957)
                    ·
                      refine ⟨690642263391087332851867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3683425404752465775209957 690642263391087332851867)
                      ·
                        rfl

theorem cell23_1345021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_1345021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345021 prefixEnd_1345021 := by exact prefixLift 1345021
  have htrace : WordTrace (prefixWord ++ tailWord_1345021) baseStart_1345021 baseEnd_1345021 := by
    simpa [prefixWord, tailWord_1345021, baseEnd_1345021] using wordTrace_append hprefix tailTrace_1345021
  have hstable : (prefixWord ++ tailWord_1345021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345021).length < 2 ^ (prefixWord ++ tailWord_1345021).sum := by decide
  have hdescent : baseEnd_1345021 < baseStart_1345021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345022 : List Nat := [4, 2, 2, 3, 1, 1, 3, 2, 5]
def baseStart_1345022 : Nat := 118140960795 + 1345022 * 2 ^ 59
def prefixEnd_1345022 : Nat := 4983230072969 + 3 ^ 40 * 1345022 * 2
def baseEnd_1345022 : Nat := 76738086319082425437707

theorem tailTrace_1345022 : CollatzResearch.WordTrace tailWord_1345022 prefixEnd_1345022 76738086319082425437707 := by
  unfold tailWord_1345022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6132122816652810039305665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32704655022148320209630213 6132122816652810039305665)
  ·
    refine ⟨4599092112489607529479249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6132122816652810039305665 4599092112489607529479249)
    ·
      refine ⟨3449319084367205647109437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4599092112489607529479249 3449319084367205647109437)
      ·
        refine ⟨1293494656637702117666039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3449319084367205647109437 1293494656637702117666039)
        ·
          refine ⟨1940241984956553176499059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293494656637702117666039 1940241984956553176499059)
          ·
            refine ⟨2910362977434829764748589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940241984956553176499059 2910362977434829764748589)
            ·
              refine ⟨1091386116538061161780721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2910362977434829764748589 1091386116538061161780721)
              ·
                refine ⟨818539587403545871335541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091386116538061161780721 818539587403545871335541)
                ·
                  refine ⟨76738086319082425437707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 818539587403545871335541 76738086319082425437707)
                  ·
                    rfl

theorem cell23_1345022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_1345022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345022 prefixEnd_1345022 := by exact prefixLift 1345022
  have htrace : WordTrace (prefixWord ++ tailWord_1345022) baseStart_1345022 baseEnd_1345022 := by
    simpa [prefixWord, tailWord_1345022, baseEnd_1345022] using wordTrace_append hprefix tailTrace_1345022
  have hstable : (prefixWord ++ tailWord_1345022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345022).length < 2 ^ (prefixWord ++ tailWord_1345022).sum := by decide
  have hdescent : baseEnd_1345022 < baseStart_1345022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345111 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_1345111 : Nat := 118140960795 + 1345111 * 2 ^ 59
def prefixEnd_1345111 : Nat := 4983230072969 + 3 ^ 40 * 1345111 * 2
def baseEnd_1345111 : Nat := 690688476649991980726453

theorem tailTrace_1345111 : CollatzResearch.WordTrace tailWord_1345111 prefixEnd_1345111 690688476649991980726453 := by
  unfold tailWord_1345111
  simp only [CollatzResearch.WordTrace]
  refine ⟨49060228629900048514435187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32706819086600032342956791 49060228629900048514435187)
  ·
    refine ⟨73590342944850072771652781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49060228629900048514435187 73590342944850072771652781)
    ·
      refine ⟨27596378604318777289369793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73590342944850072771652781 27596378604318777289369793)
      ·
        refine ⟨20697283953239082967027345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27596378604318777289369793 20697283953239082967027345)
        ·
          refine ⟨15522962964929312225270509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20697283953239082967027345 15522962964929312225270509)
          ·
            refine ⟨5821111111848492084476441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15522962964929312225270509 5821111111848492084476441)
            ·
              refine ⟨4365833333886369063357331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5821111111848492084476441 4365833333886369063357331)
              ·
                refine ⟨6548750000829553595035997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4365833333886369063357331 6548750000829553595035997)
                ·
                  refine ⟨2455781250311082598138499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6548750000829553595035997 2455781250311082598138499)
                  ·
                    refine ⟨3683671875466623897207749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2455781250311082598138499 3683671875466623897207749)
                    ·
                      refine ⟨690688476649991980726453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3683671875466623897207749 690688476649991980726453)
                      ·
                        rfl

theorem cell23_1345111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_1345111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345111 prefixEnd_1345111 := by exact prefixLift 1345111
  have htrace : WordTrace (prefixWord ++ tailWord_1345111) baseStart_1345111 baseEnd_1345111 := by
    simpa [prefixWord, tailWord_1345111, baseEnd_1345111] using wordTrace_append hprefix tailTrace_1345111
  have hstable : (prefixWord ++ tailWord_1345111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345111).length < 2 ^ (prefixWord ++ tailWord_1345111).sum := by decide
  have hdescent : baseEnd_1345111 < baseStart_1345111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345121 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 4, 4]
def baseStart_1345121 : Nat := 118140960795 + 1345121 * 2 ^ 59
def prefixEnd_1345121 : Nat := 4983230072969 + 3 ^ 40 * 1345121 * 2
def baseEnd_1345121 : Nat := 230231203818845647200469

theorem tailTrace_1345121 : CollatzResearch.WordTrace tailWord_1345121 prefixEnd_1345121 230231203818845647200469 := by
  unfold tailWord_1345121
  simp only [CollatzResearch.WordTrace]
  refine ⟨49060593359863820222299217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32707062239909213481532811 49060593359863820222299217)
  ·
    refine ⟨36795445019897865166724413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49060593359863820222299217 36795445019897865166724413)
    ·
      refine ⟨13798291882461699437521655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36795445019897865166724413 13798291882461699437521655)
      ·
        refine ⟨20697437823692549156282483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13798291882461699437521655 20697437823692549156282483)
        ·
          refine ⟨31046156735538823734423725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20697437823692549156282483 31046156735538823734423725)
          ·
            refine ⟨11642308775827058900408897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31046156735538823734423725 11642308775827058900408897)
            ·
              refine ⟨8731731581870294175306673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11642308775827058900408897 8731731581870294175306673)
              ·
                refine ⟨6548798686402720631480005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8731731581870294175306673 6548798686402720631480005)
                ·
                  refine ⟨1227899753700510118402501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6548798686402720631480005 1227899753700510118402501)
                  ·
                    refine ⟨230231203818845647200469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1227899753700510118402501 230231203818845647200469)
                    ·
                      rfl

theorem cell23_1345121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_1345121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345121 prefixEnd_1345121 := by exact prefixLift 1345121
  have htrace : WordTrace (prefixWord ++ tailWord_1345121) baseStart_1345121 baseEnd_1345121 := by
    simpa [prefixWord, tailWord_1345121, baseEnd_1345121] using wordTrace_append hprefix tailTrace_1345121
  have hstable : (prefixWord ++ tailWord_1345121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345121).length < 2 ^ (prefixWord ++ tailWord_1345121).sum := by decide
  have hdescent : baseEnd_1345121 < baseStart_1345121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345125 : List Nat := [1, 3, 1, 3, 3, 3, 2, 1, 1, 5]
def baseStart_1345125 : Nat := 118140960795 + 1345125 * 2 ^ 59
def prefixEnd_1345125 : Nat := 4983230072969 + 3 ^ 40 * 1345125 * 2
def baseEnd_1345125 : Nat := 230231888459718308650463

theorem tailTrace_1345125 : CollatzResearch.WordTrace tailWord_1345125 prefixEnd_1345125 230231888459718308650463 := by
  unfold tailWord_1345125
  simp only [CollatzResearch.WordTrace]
  refine ⟨49060739251849328905444829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32707159501232885936963219 49060739251849328905444829)
  ·
    refine ⟨18397777219443498339541811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49060739251849328905444829 18397777219443498339541811)
    ·
      refine ⟨27596665829165247509312717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18397777219443498339541811 27596665829165247509312717)
      ·
        refine ⟨10348749685936967815992269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27596665829165247509312717 10348749685936967815992269)
        ·
          refine ⟨3880781132226362930997101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10348749685936967815992269 3880781132226362930997101)
          ·
            refine ⟨1455292924584886099123913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3880781132226362930997101 1455292924584886099123913)
            ·
              refine ⟨1091469693438664574342935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455292924584886099123913 1091469693438664574342935)
              ·
                refine ⟨1637204540157996861514403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091469693438664574342935 1637204540157996861514403)
                ·
                  refine ⟨2455806810236995292271605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637204540157996861514403 2455806810236995292271605)
                  ·
                    refine ⟨230231888459718308650463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2455806810236995292271605 230231888459718308650463)
                    ·
                      rfl

theorem cell23_1345125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_1345125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345125 prefixEnd_1345125 := by exact prefixLift 1345125
  have htrace : WordTrace (prefixWord ++ tailWord_1345125) baseStart_1345125 baseEnd_1345125 := by
    simpa [prefixWord, tailWord_1345125, baseEnd_1345125] using wordTrace_append hprefix tailTrace_1345125
  have hstable : (prefixWord ++ tailWord_1345125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345125).length < 2 ^ (prefixWord ++ tailWord_1345125).sum := by decide
  have hdescent : baseEnd_1345125 < baseStart_1345125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345138 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_1345138 : Nat := 118140960795 + 1345138 * 2 ^ 59
def prefixEnd_1345138 : Nat := 4983230072969 + 3 ^ 40 * 1345138 * 2
def baseEnd_1345138 : Nat := 230234113542554458362943

theorem tailTrace_1345138 : CollatzResearch.WordTrace tailWord_1345138 prefixEnd_1345138 230234113542554458362943 := by
  unfold tailWord_1345138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12265303350200558031417017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32707475600534821417112045 12265303350200558031417017)
  ·
    refine ⟨9198977512650418523562763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12265303350200558031417017 9198977512650418523562763)
    ·
      refine ⟨13798466268975627785344145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9198977512650418523562763 13798466268975627785344145)
      ·
        refine ⟨10348849701731720839008109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13798466268975627785344145 10348849701731720839008109)
        ·
          refine ⟨3880818638149395314628041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10348849701731720839008109 3880818638149395314628041)
          ·
            refine ⟨2910613978612046485971031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3880818638149395314628041 2910613978612046485971031)
            ·
              refine ⟨4365920967918069728956547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2910613978612046485971031 4365920967918069728956547)
              ·
                refine ⟨6548881451877104593434821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4365920967918069728956547 6548881451877104593434821)
                ·
                  refine ⟨1227915272226957111269029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6548881451877104593434821 1227915272226957111269029)
                  ·
                    refine ⟨230234113542554458362943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1227915272226957111269029 230234113542554458362943)
                    ·
                      rfl

theorem cell23_1345138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_1345138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345138 prefixEnd_1345138 := by exact prefixLift 1345138
  have htrace : WordTrace (prefixWord ++ tailWord_1345138) baseStart_1345138 baseEnd_1345138 := by
    simpa [prefixWord, tailWord_1345138, baseEnd_1345138] using wordTrace_append hprefix tailTrace_1345138
  have hstable : (prefixWord ++ tailWord_1345138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345138).length < 2 ^ (prefixWord ++ tailWord_1345138).sum := by decide
  have hdescent : baseEnd_1345138 < baseStart_1345138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345145 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 3, 2, 2]
def baseStart_1345145 : Nat := 118140960795 + 1345145 * 2 ^ 59
def prefixEnd_1345145 : Nat := 4983230072969 + 3 ^ 40 * 1345145 * 2
def baseEnd_1345145 : Nat := 690705934992244847701297

theorem tailTrace_1345145 : CollatzResearch.WordTrace tailWord_1345145 prefixEnd_1345145 690705934992244847701297 := by
  unfold tailWord_1345145
  simp only [CollatzResearch.WordTrace]
  refine ⟨49061468711776872321172889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32707645807851248214115259 49061468711776872321172889)
  ·
    refine ⟨36796101533832654240879667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49061468711776872321172889 36796101533832654240879667)
    ·
      refine ⟨55194152300748981361319501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36796101533832654240879667 55194152300748981361319501)
      ·
        refine ⟨20697807112780868010494813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55194152300748981361319501 20697807112780868010494813)
        ·
          refine ⟨7761677667292825503935555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20697807112780868010494813 7761677667292825503935555)
          ·
            refine ⟨11642516500939238255903333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7761677667292825503935555 11642516500939238255903333)
            ·
              refine ⟨2182971843926107172981875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11642516500939238255903333 2182971843926107172981875)
              ·
                refine ⟨3274457765889160759472813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182971843926107172981875 3274457765889160759472813)
                ·
                  refine ⟨1227921662208435284802305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3274457765889160759472813 1227921662208435284802305)
                  ·
                    refine ⟨920941246656326463601729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1227921662208435284802305 920941246656326463601729)
                    ·
                      refine ⟨690705934992244847701297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 920941246656326463601729 690705934992244847701297)
                      ·
                        rfl

theorem cell23_1345145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_1345145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345145 prefixEnd_1345145 := by exact prefixLift 1345145
  have htrace : WordTrace (prefixWord ++ tailWord_1345145) baseStart_1345145 baseEnd_1345145 := by
    simpa [prefixWord, tailWord_1345145, baseEnd_1345145] using wordTrace_append hprefix tailTrace_1345145
  have hstable : (prefixWord ++ tailWord_1345145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345145).length < 2 ^ (prefixWord ++ tailWord_1345145).sum := by decide
  have hdescent : baseEnd_1345145 < baseStart_1345145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345212 : List Nat := [2, 2, 2, 3, 1, 2, 4, 1, 2, 1, 3]
def baseStart_1345212 : Nat := 118140960795 + 1345212 * 2 ^ 59
def prefixEnd_1345212 : Nat := 4983230072969 + 3 ^ 40 * 1345212 * 2
def baseEnd_1345212 : Nat := 690740338196096085563489

theorem tailTrace_1345212 : CollatzResearch.WordTrace tailWord_1345212 prefixEnd_1345212 690740338196096085563489 := by
  unfold tailWord_1345212
  simp only [CollatzResearch.WordTrace]
  refine ⟨24531956201267071381930945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32709274935022761842574593 24531956201267071381930945)
  ·
    refine ⟨18398967150950303536448209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24531956201267071381930945 18398967150950303536448209)
    ·
      refine ⟨13799225363212727652336157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18398967150950303536448209 13799225363212727652336157)
      ·
        refine ⟨5174709511204772869626059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13799225363212727652336157 5174709511204772869626059)
        ·
          refine ⟨7762064266807159304439089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5174709511204772869626059 7762064266807159304439089)
          ·
            refine ⟨5821548200105369478329317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7762064266807159304439089 5821548200105369478329317)
            ·
              refine ⟨1091540287519756777186747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5821548200105369478329317 1091540287519756777186747)
              ·
                refine ⟨1637310431279635165780121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091540287519756777186747 1637310431279635165780121)
                ·
                  refine ⟨1227982823459726374335091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1637310431279635165780121 1227982823459726374335091)
                  ·
                    refine ⟨1841974235189589561502637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1227982823459726374335091 1841974235189589561502637)
                    ·
                      refine ⟨690740338196096085563489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1841974235189589561502637 690740338196096085563489)
                      ·
                        rfl

theorem cell23_1345212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_1345212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345212 prefixEnd_1345212 := by exact prefixLift 1345212
  have htrace : WordTrace (prefixWord ++ tailWord_1345212) baseStart_1345212 baseEnd_1345212 := by
    simpa [prefixWord, tailWord_1345212, baseEnd_1345212] using wordTrace_append hprefix tailTrace_1345212
  have hstable : (prefixWord ++ tailWord_1345212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345212).length < 2 ^ (prefixWord ++ tailWord_1345212).sum := by decide
  have hdescent : baseEnd_1345212 < baseStart_1345212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345221 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 2, 4, 3]
def baseStart_1345221 : Nat := 118140960795 + 1345221 * 2 ^ 59
def prefixEnd_1345221 : Nat := 4983230072969 + 3 ^ 40 * 1345221 * 2
def baseEnd_1345221 : Nat := 690744959521986550350947

theorem tailTrace_1345221 : CollatzResearch.WordTrace tailWord_1345221 prefixEnd_1345221 690744959521986550350947 := by
  unfold tailWord_1345221
  simp only [CollatzResearch.WordTrace]
  refine ⟨49064240659501537300939517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32709493773001024867293011 49064240659501537300939517)
  ·
    refine ⟨18399090247313076487852319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49064240659501537300939517 18399090247313076487852319)
    ·
      refine ⟨27598635370969614731778479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18399090247313076487852319 27598635370969614731778479)
      ·
        refine ⟨41397953056454422097667719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27598635370969614731778479 41397953056454422097667719)
        ·
          refine ⟨62096929584681633146501579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41397953056454422097667719 62096929584681633146501579)
          ·
            refine ⟨93145394377022449719752369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62096929584681633146501579 93145394377022449719752369)
            ·
              refine ⟨69859045782766837289814277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93145394377022449719752369 69859045782766837289814277)
              ·
                refine ⟨13098571084268781991840177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69859045782766837289814277 13098571084268781991840177)
                ·
                  refine ⟨9823928313201586493880133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13098571084268781991840177 9823928313201586493880133)
                  ·
                    refine ⟨1841986558725297467602525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9823928313201586493880133 1841986558725297467602525)
                    ·
                      refine ⟨690744959521986550350947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1841986558725297467602525 690744959521986550350947)
                      ·
                        rfl

theorem cell23_1345221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_1345221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345221 prefixEnd_1345221 := by exact prefixLift 1345221
  have htrace : WordTrace (prefixWord ++ tailWord_1345221) baseStart_1345221 baseEnd_1345221 := by
    simpa [prefixWord, tailWord_1345221, baseEnd_1345221] using wordTrace_append hprefix tailTrace_1345221
  have hstable : (prefixWord ++ tailWord_1345221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345221).length < 2 ^ (prefixWord ++ tailWord_1345221).sum := by decide
  have hdescent : baseEnd_1345221 < baseStart_1345221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345252 : List Nat := [2, 3, 1, 1, 1, 3, 4, 2, 2, 2, 2]
def baseStart_1345252 : Nat := 118140960795 + 1345252 * 2 ^ 59
def prefixEnd_1345252 : Nat := 4983230072969 + 3 ^ 40 * 1345252 * 2
def baseEnd_1345252 : Nat := 690760877422275929063305

theorem tailTrace_1345252 : CollatzResearch.WordTrace tailWord_1345252 prefixEnd_1345252 690760877422275929063305 := by
  unfold tailWord_1345252
  simp only [CollatzResearch.WordTrace]
  refine ⟨24532685661194614797659005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32710247548259486396878673 24532685661194614797659005)
  ·
    refine ⟨9199757122947980549122127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24532685661194614797659005 9199757122947980549122127)
    ·
      refine ⟨13799635684421970823683191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9199757122947980549122127 13799635684421970823683191)
      ·
        refine ⟨20699453526632956235524787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13799635684421970823683191 20699453526632956235524787)
        ·
          refine ⟨31049180289949434353287181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20699453526632956235524787 31049180289949434353287181)
          ·
            refine ⟨11643442608731037882482693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31049180289949434353287181 11643442608731037882482693)
            ·
              refine ⟨2183145489137069602965505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11643442608731037882482693 2183145489137069602965505)
              ·
                refine ⟨1637359116852802202224129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2183145489137069602965505 1637359116852802202224129)
                ·
                  refine ⟨1228019337639601651668097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1637359116852802202224129 1228019337639601651668097)
                  ·
                    refine ⟨921014503229701238751073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1228019337639601651668097 921014503229701238751073)
                    ·
                      refine ⟨690760877422275929063305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 921014503229701238751073 690760877422275929063305)
                      ·
                        rfl

theorem cell23_1345252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_1345252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345252 prefixEnd_1345252 := by exact prefixLift 1345252
  have htrace : WordTrace (prefixWord ++ tailWord_1345252) baseStart_1345252 baseEnd_1345252 := by
    simpa [prefixWord, tailWord_1345252, baseEnd_1345252] using wordTrace_append hprefix tailTrace_1345252
  have hstable : (prefixWord ++ tailWord_1345252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345252).length < 2 ^ (prefixWord ++ tailWord_1345252).sum := by decide
  have hdescent : baseEnd_1345252 < baseStart_1345252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345271 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 4, 5]
def baseStart_1345271 : Nat := 118140960795 + 1345271 * 2 ^ 59
def prefixEnd_1345271 : Nat := 4983230072969 + 3 ^ 40 * 1345271 * 2
def baseEnd_1345271 : Nat := 230256877851570451575239

theorem tailTrace_1345271 : CollatzResearch.WordTrace tailWord_1345271 prefixEnd_1345271 230256877851570451575239 := by
  unfold tailWord_1345271
  simp only [CollatzResearch.WordTrace]
  refine ⟨49066064309320395840259667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32710709539546930560173111 49066064309320395840259667)
  ·
    refine ⟨73599096463980593760389501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49066064309320395840259667 73599096463980593760389501)
    ·
      refine ⟨27599661173992722660146063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73599096463980593760389501 27599661173992722660146063)
      ·
        refine ⟨41399491760989083990219095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27599661173992722660146063 41399491760989083990219095)
        ·
          refine ⟨62099237641483625985328643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41399491760989083990219095 62099237641483625985328643)
          ·
            refine ⟨93148856462225438977992965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62099237641483625985328643 93148856462225438977992965)
            ·
              refine ⟨17465410586667269808373681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93148856462225438977992965 17465410586667269808373681)
              ·
                refine ⟨13099057940000452356280261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17465410586667269808373681 13099057940000452356280261)
                ·
                  refine ⟨2456073363750084816802549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13099057940000452356280261 2456073363750084816802549)
                  ·
                    refine ⟨230256877851570451575239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2456073363750084816802549 230256877851570451575239)
                    ·
                      rfl

theorem cell23_1345271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_1345271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345271 prefixEnd_1345271 := by exact prefixLift 1345271
  have htrace : WordTrace (prefixWord ++ tailWord_1345271) baseStart_1345271 baseEnd_1345271 := by
    simpa [prefixWord, tailWord_1345271, baseEnd_1345271] using wordTrace_append hprefix tailTrace_1345271
  have hstable : (prefixWord ++ tailWord_1345271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345271).length < 2 ^ (prefixWord ++ tailWord_1345271).sum := by decide
  have hdescent : baseEnd_1345271 < baseStart_1345271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345281 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1345281 : Nat := 118140960795 + 1345281 * 2 ^ 59
def prefixEnd_1345281 : Nat := 4983230072969 + 3 ^ 40 * 1345281 * 2
def baseEnd_1345281 : Nat := 690775768361256315600671

theorem tailTrace_1345281 : CollatzResearch.WordTrace tailWord_1345281 prefixEnd_1345281 690775768361256315600671 := by
  unfold tailWord_1345281
  simp only [CollatzResearch.WordTrace]
  refine ⟨49066429039284167548123697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32710952692856111698749131 49066429039284167548123697)
  ·
    refine ⟨36799821779463125661092773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49066429039284167548123697 36799821779463125661092773)
    ·
      refine ⟨6899966583649336061454895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36799821779463125661092773 6899966583649336061454895)
      ·
        refine ⟨10349949875474004092182343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6899966583649336061454895 10349949875474004092182343)
        ·
          refine ⟨15524924813211006138273515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10349949875474004092182343 15524924813211006138273515)
          ·
            refine ⟨23287387219816509207410273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15524924813211006138273515 23287387219816509207410273)
            ·
              refine ⟨17465540414862381905557705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23287387219816509207410273 17465540414862381905557705)
              ·
                refine ⟨13099155311146786429168279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17465540414862381905557705 13099155311146786429168279)
                ·
                  refine ⟨19648732966720179643752419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13099155311146786429168279 19648732966720179643752419)
                  ·
                    refine ⟨29473099450080269465628629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19648732966720179643752419 29473099450080269465628629)
                    ·
                      refine ⟨690775768361256315600671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29473099450080269465628629 690775768361256315600671)
                      ·
                        rfl

theorem cell23_1345281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1345281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345281 prefixEnd_1345281 := by exact prefixLift 1345281
  have htrace : WordTrace (prefixWord ++ tailWord_1345281) baseStart_1345281 baseEnd_1345281 := by
    simpa [prefixWord, tailWord_1345281, baseEnd_1345281] using wordTrace_append hprefix tailTrace_1345281
  have hstable : (prefixWord ++ tailWord_1345281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345281).length < 2 ^ (prefixWord ++ tailWord_1345281).sum := by decide
  have hdescent : baseEnd_1345281 < baseStart_1345281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345308 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1345308 : Nat := 118140960795 + 1345308 * 2 ^ 59
def prefixEnd_1345308 : Nat := 4983230072969 + 3 ^ 40 * 1345308 * 2
def baseEnd_1345308 : Nat := 690789632338927709963047

theorem tailTrace_1345308 : CollatzResearch.WordTrace tailWord_1345308 prefixEnd_1345308 690789632338927709963047 := by
  unfold tailWord_1345308
  simp only [CollatzResearch.WordTrace]
  refine ⟨24533706905093175579678289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32711609206790900772904385 24533706905093175579678289)
  ·
    refine ⟨18400280178819881684758717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24533706905093175579678289 18400280178819881684758717)
    ·
      refine ⟨6900105067057455631784519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18400280178819881684758717 6900105067057455631784519)
      ·
        refine ⟨10350157600586183447676779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6900105067057455631784519 10350157600586183447676779)
        ·
          refine ⟨15525236400879275171515169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10350157600586183447676779 15525236400879275171515169)
          ·
            refine ⟨11643927300659456378636377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15525236400879275171515169 11643927300659456378636377)
            ·
              refine ⟨8732945475494592283977283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11643927300659456378636377 8732945475494592283977283)
              ·
                refine ⟨13099418213241888425965925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8732945475494592283977283 13099418213241888425965925)
                ·
                  refine ⟨2456140914982854079868611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13099418213241888425965925 2456140914982854079868611)
                  ·
                    refine ⟨3684211372474281119802917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2456140914982854079868611 3684211372474281119802917)
                    ·
                      refine ⟨690789632338927709963047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3684211372474281119802917 690789632338927709963047)
                      ·
                        rfl

theorem cell23_1345308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1345308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345308 prefixEnd_1345308 := by exact prefixLift 1345308
  have htrace : WordTrace (prefixWord ++ tailWord_1345308) baseStart_1345308 baseEnd_1345308 := by
    simpa [prefixWord, tailWord_1345308, baseEnd_1345308] using wordTrace_append hprefix tailTrace_1345308
  have hstable : (prefixWord ++ tailWord_1345308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345308).length < 2 ^ (prefixWord ++ tailWord_1345308).sum := by decide
  have hdescent : baseEnd_1345308 < baseStart_1345308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345321 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 4, 4, 4]
def baseStart_1345321 : Nat := 118140960795 + 1345321 * 2 ^ 59
def prefixEnd_1345321 : Nat := 4983230072969 + 3 ^ 40 * 1345321 * 2
def baseEnd_1345321 : Nat := 690796307587436159100487

theorem tailTrace_1345321 : CollatzResearch.WordTrace tailWord_1345321 prefixEnd_1345321 690796307587436159100487 := by
  unfold tailWord_1345321
  simp only [CollatzResearch.WordTrace]
  refine ⟨49067887959139254379579817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32711925306092836253053211 49067887959139254379579817)
  ·
    refine ⟨36800915969354440784684863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49067887959139254379579817 36800915969354440784684863)
    ·
      refine ⟨55201373954031661177027295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36800915969354440784684863 55201373954031661177027295)
      ·
        refine ⟨82802060931047491765540943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55201373954031661177027295 82802060931047491765540943)
        ·
          refine ⟨124203091396571237648311415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82802060931047491765540943 124203091396571237648311415)
          ·
            refine ⟨186304637094856856472467123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124203091396571237648311415 186304637094856856472467123)
            ·
              refine ⟨279456955642285284708700685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186304637094856856472467123 279456955642285284708700685)
              ·
                refine ⟨104796358365856981765762757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279456955642285284708700685 104796358365856981765762757)
                ·
                  refine ⟨19649317193598184081080517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104796358365856981765762757 19649317193598184081080517)
                  ·
                    refine ⟨3684246973799659515202597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19649317193598184081080517 3684246973799659515202597)
                    ·
                      refine ⟨690796307587436159100487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3684246973799659515202597 690796307587436159100487)
                      ·
                        rfl

theorem cell23_1345321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_1345321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345321 prefixEnd_1345321 := by exact prefixLift 1345321
  have htrace : WordTrace (prefixWord ++ tailWord_1345321) baseStart_1345321 baseEnd_1345321 := by
    simpa [prefixWord, tailWord_1345321, baseEnd_1345321] using wordTrace_append hprefix tailTrace_1345321
  have hstable : (prefixWord ++ tailWord_1345321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345321).length < 2 ^ (prefixWord ++ tailWord_1345321).sum := by decide
  have hdescent : baseEnd_1345321 < baseStart_1345321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345352 : List Nat := [2, 1, 3, 1, 1, 4, 3, 3, 1, 4]
def baseStart_1345352 : Nat := 118140960795 + 1345352 * 2 ^ 59
def prefixEnd_1345352 : Nat := 4983230072969 + 3 ^ 40 * 1345352 * 2
def baseEnd_1345352 : Nat := 230270741829241845937615

theorem tailTrace_1345352 : CollatzResearch.WordTrace tailWord_1345352 prefixEnd_1345352 230270741829241845937615 := by
  unfold tailWord_1345352
  simp only [CollatzResearch.WordTrace]
  refine ⟨24534509311013473336979155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32712679081351297782638873 24534509311013473336979155)
  ·
    refine ⟨36801763966520210005468733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24534509311013473336979155 36801763966520210005468733)
    ·
      refine ⟨13800661487445078752050775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36801763966520210005468733 13800661487445078752050775)
      ·
        refine ⟨20700992231167618128076163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13800661487445078752050775 20700992231167618128076163)
        ·
          refine ⟨31051488346751427192114245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20700992231167618128076163 31051488346751427192114245)
          ·
            refine ⟨5822154065015892598521421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31051488346751427192114245 5822154065015892598521421)
            ·
              refine ⟨2183307774380959724445533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5822154065015892598521421 2183307774380959724445533)
              ·
                refine ⟨818740415392859896667075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2183307774380959724445533 818740415392859896667075)
                ·
                  refine ⟨1228110623089289845000613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818740415392859896667075 1228110623089289845000613)
                  ·
                    refine ⟨230270741829241845937615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1228110623089289845000613 230270741829241845937615)
                    ·
                      rfl

theorem cell23_1345352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_1345352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345352 prefixEnd_1345352 := by exact prefixLift 1345352
  have htrace : WordTrace (prefixWord ++ tailWord_1345352) baseStart_1345352 baseEnd_1345352 := by
    simpa [prefixWord, tailWord_1345352, baseEnd_1345352] using wordTrace_append hprefix tailTrace_1345352
  have hstable : (prefixWord ++ tailWord_1345352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345352).length < 2 ^ (prefixWord ++ tailWord_1345352).sum := by decide
  have hdescent : baseEnd_1345352 < baseStart_1345352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345408 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 1, 6]
def baseStart_1345408 : Nat := 118140960795 + 1345408 * 2 ^ 59
def prefixEnd_1345408 : Nat := 4983230072969 + 3 ^ 40 * 1345408 * 2
def baseEnd_1345408 : Nat := 230280326801459106237529

theorem tailTrace_1345408 : CollatzResearch.WordTrace tailWord_1345408 prefixEnd_1345408 230280326801459106237529 := by
  unfold tailWord_1345408
  simp only [CollatzResearch.WordTrace]
  refine ⟨24535530554912034118998439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32714040739882712158664585 24535530554912034118998439)
  ·
    refine ⟨36803295832368051178497659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24535530554912034118998439 36803295832368051178497659)
    ·
      refine ⟨55204943748552076767746489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36803295832368051178497659 55204943748552076767746489)
      ·
        refine ⟨41403707811414057575809867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55204943748552076767746489 41403707811414057575809867)
        ·
          refine ⟨62105561717121086363714801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41403707811414057575809867 62105561717121086363714801)
          ·
            refine ⟨46579171287840814772786101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62105561717121086363714801 46579171287840814772786101)
            ·
              refine ⟨4366797308235076384948697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46579171287840814772786101 4366797308235076384948697)
              ·
                refine ⟨3275097981176307288711523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4366797308235076384948697 3275097981176307288711523)
                ·
                  refine ⟨4912646971764460933067285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275097981176307288711523 4912646971764460933067285)
                  ·
                    refine ⟨230280326801459106237529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4912646971764460933067285 230280326801459106237529)
                    ·
                      rfl

theorem cell23_1345408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 6].length) (baseStart_1345408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345408 prefixEnd_1345408 := by exact prefixLift 1345408
  have htrace : WordTrace (prefixWord ++ tailWord_1345408) baseStart_1345408 baseEnd_1345408 := by
    simpa [prefixWord, tailWord_1345408, baseEnd_1345408] using wordTrace_append hprefix tailTrace_1345408
  have hstable : (prefixWord ++ tailWord_1345408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345408).length < 2 ^ (prefixWord ++ tailWord_1345408).sum := by decide
  have hdescent : baseEnd_1345408 < baseStart_1345408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345425 : List Nat := [1, 2, 2, 1, 1, 1, 5, 4, 2, 4]
def baseStart_1345425 : Nat := 118140960795 + 1345425 * 2 ^ 59
def prefixEnd_1345425 : Nat := 4983230072969 + 3 ^ 40 * 1345425 * 2
def baseEnd_1345425 : Nat := 230283236525167917400003

theorem tailTrace_1345425 : CollatzResearch.WordTrace tailWord_1345425 prefixEnd_1345425 230283236525167917400003 := by
  unfold tailWord_1345425
  simp only [CollatzResearch.WordTrace]
  refine ⟨49071681150762480141365729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32714454100508320094243819 49071681150762480141365729)
  ·
    refine ⟨36803760863071860106024297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49071681150762480141365729 36803760863071860106024297)
    ·
      refine ⟨27602820647303895079518223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36803760863071860106024297 27602820647303895079518223)
      ·
        refine ⟨41404230970955842619277335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27602820647303895079518223 41404230970955842619277335)
        ·
          refine ⟨62106346456433763928916003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41404230970955842619277335 62106346456433763928916003)
          ·
            refine ⟨93159519684650645893374005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62106346456433763928916003 93159519684650645893374005)
            ·
              refine ⟨8733704970435998052503813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93159519684650645893374005 8733704970435998052503813)
              ·
                refine ⟨1637569681956749634844465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8733704970435998052503813 1637569681956749634844465)
                ·
                  refine ⟨1228177261467562226133349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1637569681956749634844465 1228177261467562226133349)
                  ·
                    refine ⟨230283236525167917400003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1228177261467562226133349 230283236525167917400003)
                    ·
                      rfl

theorem cell23_1345425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_1345425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345425 prefixEnd_1345425 := by exact prefixLift 1345425
  have htrace : WordTrace (prefixWord ++ tailWord_1345425) baseStart_1345425 baseEnd_1345425 := by
    simpa [prefixWord, tailWord_1345425, baseEnd_1345425] using wordTrace_append hprefix tailTrace_1345425
  have hstable : (prefixWord ++ tailWord_1345425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345425).length < 2 ^ (prefixWord ++ tailWord_1345425).sum := by decide
  have hdescent : baseEnd_1345425 < baseStart_1345425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345426 : List Nat := [3, 2, 3, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_1345426 : Nat := 118140960795 + 1345426 * 2 ^ 59
def prefixEnd_1345426 : Nat := 4983230072969 + 3 ^ 40 * 1345426 * 2
def baseEnd_1345426 : Nat := 690850223056158248287505

theorem tailTrace_1345426 : CollatzResearch.WordTrace tailWord_1345426 prefixEnd_1345426 690850223056158248287505 := by
  unfold tailWord_1345426
  simp only [CollatzResearch.WordTrace]
  refine ⟨12267929405939714328038033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32714478415839238208101421 12267929405939714328038033)
  ·
    refine ⟨9200947054454785746028525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12267929405939714328038033 9200947054454785746028525)
    ·
      refine ⟨3450355145420544654760697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9200947054454785746028525 3450355145420544654760697)
      ·
        refine ⟨2587766359065408491070523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3450355145420544654760697 2587766359065408491070523)
        ·
          refine ⟨3881649538598112736605785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2587766359065408491070523 3881649538598112736605785)
          ·
            refine ⟨2911237153948584552454339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3881649538598112736605785 2911237153948584552454339)
            ·
              refine ⟨4366855730922876828681509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911237153948584552454339 4366855730922876828681509)
              ·
                refine ⟨818785449548039405377783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4366855730922876828681509 818785449548039405377783)
                ·
                  refine ⟨1228178174322059108066675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818785449548039405377783 1228178174322059108066675)
                  ·
                    refine ⟨1842267261483088662100013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1228178174322059108066675 1842267261483088662100013)
                    ·
                      refine ⟨690850223056158248287505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1842267261483088662100013 690850223056158248287505)
                      ·
                        rfl

theorem cell23_1345426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_1345426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345426 prefixEnd_1345426 := by exact prefixLift 1345426
  have htrace : WordTrace (prefixWord ++ tailWord_1345426) baseStart_1345426 baseEnd_1345426 := by
    simpa [prefixWord, tailWord_1345426, baseEnd_1345426] using wordTrace_append hprefix tailTrace_1345426
  have hstable : (prefixWord ++ tailWord_1345426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345426).length < 2 ^ (prefixWord ++ tailWord_1345426).sum := by decide
  have hdescent : baseEnd_1345426 < baseStart_1345426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345442 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_1345442 : Nat := 118140960795 + 1345442 * 2 ^ 59
def prefixEnd_1345442 : Nat := 4983230072969 + 3 ^ 40 * 1345442 * 2
def baseEnd_1345442 : Nat := 230286146248876728562477

theorem tailTrace_1345442 : CollatzResearch.WordTrace tailWord_1345442 prefixEnd_1345442 230286146248876728562477 := by
  unfold tailWord_1345442
  simp only [CollatzResearch.WordTrace]
  refine ⟨12268075297925223011183645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32714867461133928029823053 12268075297925223011183645)
  ·
    refine ⟨4600528236721958629193867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12268075297925223011183645 4600528236721958629193867)
    ·
      refine ⟨6900792355082937943790801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4600528236721958629193867 6900792355082937943790801)
      ·
        refine ⟨5175594266312203457843101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6900792355082937943790801 5175594266312203457843101)
        ·
          refine ⟨1940847849867076296691163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5175594266312203457843101 1940847849867076296691163)
          ·
            refine ⟨2911271774800614445036745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940847849867076296691163 2911271774800614445036745)
            ·
              refine ⟨2183453831100460833777559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2911271774800614445036745 2183453831100460833777559)
              ·
                refine ⟨3275180746650691250666339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2183453831100460833777559 3275180746650691250666339)
                ·
                  refine ⟨4912771119976036875999509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275180746650691250666339 4912771119976036875999509)
                  ·
                    refine ⟨230286146248876728562477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4912771119976036875999509 230286146248876728562477)
                    ·
                      rfl

theorem cell23_1345442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_1345442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345442 prefixEnd_1345442 := by exact prefixLift 1345442
  have htrace : WordTrace (prefixWord ++ tailWord_1345442) baseStart_1345442 baseEnd_1345442 := by
    simpa [prefixWord, tailWord_1345442, baseEnd_1345442] using wordTrace_append hprefix tailTrace_1345442
  have hstable : (prefixWord ++ tailWord_1345442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345442).length < 2 ^ (prefixWord ++ tailWord_1345442).sum := by decide
  have hdescent : baseEnd_1345442 < baseStart_1345442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345465 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 1, 3, 3]
def baseStart_1345465 : Nat := 118140960795 + 1345465 * 2 ^ 59
def prefixEnd_1345465 : Nat := 4983230072969 + 3 ^ 40 * 1345465 * 2
def baseEnd_1345465 : Nat := 690870248801683595699825

theorem tailTrace_1345465 : CollatzResearch.WordTrace tailWord_1345465 prefixEnd_1345465 690870248801683595699825 := by
  unfold tailWord_1345465
  simp only [CollatzResearch.WordTrace]
  refine ⟨49073140070617566972821849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32715426713745044648547899 49073140070617566972821849)
  ·
    refine ⟨36804855052963175229616387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49073140070617566972821849 36804855052963175229616387)
    ·
      refine ⟨55207282579444762844424581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36804855052963175229616387 55207282579444762844424581)
      ·
        refine ⟨10351365483645893033329609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55207282579444762844424581 10351365483645893033329609)
        ·
          refine ⟨7763524112734419774997207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10351365483645893033329609 7763524112734419774997207)
          ·
            refine ⟨11645286169101629662495811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7763524112734419774997207 11645286169101629662495811)
            ·
              refine ⟨17467929253652444493743717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11645286169101629662495811 17467929253652444493743717)
              ·
                refine ⟨3275236735059833342576947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17467929253652444493743717 3275236735059833342576947)
                ·
                  refine ⟨4912855102589750013865421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275236735059833342576947 4912855102589750013865421)
                  ·
                    refine ⟨1842320663471156255199533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4912855102589750013865421 1842320663471156255199533)
                    ·
                      refine ⟨690870248801683595699825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1842320663471156255199533 690870248801683595699825)
                      ·
                        rfl

theorem cell23_1345465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_1345465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345465 prefixEnd_1345465 := by exact prefixLift 1345465
  have htrace : WordTrace (prefixWord ++ tailWord_1345465) baseStart_1345465 baseEnd_1345465 := by
    simpa [prefixWord, tailWord_1345465, baseEnd_1345465] using wordTrace_append hprefix tailTrace_1345465
  have hstable : (prefixWord ++ tailWord_1345465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345465).length < 2 ^ (prefixWord ++ tailWord_1345465).sum := by decide
  have hdescent : baseEnd_1345465 < baseStart_1345465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345469 : List Nat := [1, 4, 1, 2, 3, 1, 4, 1, 1, 2, 3]
def baseStart_1345469 : Nat := 118140960795 + 1345469 * 2 ^ 59
def prefixEnd_1345469 : Nat := 4983230072969 + 3 ^ 40 * 1345469 * 2
def baseEnd_1345469 : Nat := 690872302724301580049807

theorem tailTrace_1345469 : CollatzResearch.WordTrace tailWord_1345469 prefixEnd_1345469 690872302724301580049807 := by
  unfold tailWord_1345469
  simp only [CollatzResearch.WordTrace]
  refine ⟨49073285962603075655967461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32715523975068717103978307 49073285962603075655967461)
  ·
    refine ⟨9201241117988076685493899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49073285962603075655967461 9201241117988076685493899)
    ·
      refine ⟨13801861676982115028240849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9201241117988076685493899 13801861676982115028240849)
      ·
        refine ⟨10351396257736586271180637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13801861676982115028240849 10351396257736586271180637)
        ·
          refine ⟨3881773596651219851692739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10351396257736586271180637 3881773596651219851692739)
          ·
            refine ⟨5822660394976829777539109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3881773596651219851692739 5822660394976829777539109)
            ·
              refine ⟨1091748824058155583288583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5822660394976829777539109 1091748824058155583288583)
              ·
                refine ⟨1637623236087233374932875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091748824058155583288583 1637623236087233374932875)
                ·
                  refine ⟨2456434854130850062399313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637623236087233374932875 2456434854130850062399313)
                  ·
                    refine ⟨1842326140598137546799485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2456434854130850062399313 1842326140598137546799485)
                    ·
                      refine ⟨690872302724301580049807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1842326140598137546799485 690872302724301580049807)
                      ·
                        rfl

theorem cell23_1345469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_1345469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345469 prefixEnd_1345469 := by exact prefixLift 1345469
  have htrace : WordTrace (prefixWord ++ tailWord_1345469) baseStart_1345469 baseEnd_1345469 := by
    simpa [prefixWord, tailWord_1345469, baseEnd_1345469] using wordTrace_append hprefix tailTrace_1345469
  have hstable : (prefixWord ++ tailWord_1345469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345469).length < 2 ^ (prefixWord ++ tailWord_1345469).sum := by decide
  have hdescent : baseEnd_1345469 < baseStart_1345469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345488 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 4]
def baseStart_1345488 : Nat := 118140960795 + 1345488 * 2 ^ 59
def prefixEnd_1345488 : Nat := 4983230072969 + 3 ^ 40 * 1345488 * 2
def baseEnd_1345488 : Nat := 690882058856737005712219

theorem tailTrace_1345488 : CollatzResearch.WordTrace tailWord_1345488 prefixEnd_1345488 690882058856737005712219 := by
  unfold tailWord_1345488
  simp only [CollatzResearch.WordTrace]
  refine ⟨24536989474767120950454559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32715985966356161267272745 24536989474767120950454559)
  ·
    refine ⟨36805484212150681425681839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24536989474767120950454559 36805484212150681425681839)
    ·
      refine ⟨55208226318226022138522759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36805484212150681425681839 55208226318226022138522759)
      ·
        refine ⟨82812339477339033207784139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55208226318226022138522759 82812339477339033207784139)
        ·
          refine ⟨124218509216008549811676209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82812339477339033207784139 124218509216008549811676209)
          ·
            refine ⟨93163881912006412358757157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124218509216008549811676209 93163881912006412358757157)
            ·
              refine ⟨17468227858501202317266967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93163881912006412358757157 17468227858501202317266967)
              ·
                refine ⟨26202341787751803475900451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17468227858501202317266967 26202341787751803475900451)
                ·
                  refine ⟨39303512681627705213850677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26202341787751803475900451 39303512681627705213850677)
                  ·
                    refine ⟨3684704313902597363798501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39303512681627705213850677 3684704313902597363798501)
                    ·
                      refine ⟨690882058856737005712219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3684704313902597363798501 690882058856737005712219)
                      ·
                        rfl

theorem cell23_1345488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_1345488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345488 prefixEnd_1345488 := by exact prefixLift 1345488
  have htrace : WordTrace (prefixWord ++ tailWord_1345488) baseStart_1345488 baseEnd_1345488 := by
    simpa [prefixWord, tailWord_1345488, baseEnd_1345488] using wordTrace_append hprefix tailTrace_1345488
  have hstable : (prefixWord ++ tailWord_1345488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345488).length < 2 ^ (prefixWord ++ tailWord_1345488).sum := by decide
  have hdescent : baseEnd_1345488 < baseStart_1345488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345506 : List Nat := [3, 3, 3, 1, 3, 1, 2, 7]
def baseStart_1345506 : Nat := 118140960795 + 1345506 * 2 ^ 59
def prefixEnd_1345506 : Nat := 4983230072969 + 3 ^ 40 * 1345506 * 2
def baseEnd_1345506 : Nat := 25588566722537701306931

theorem tailTrace_1345506 : CollatzResearch.WordTrace tailWord_1345506 prefixEnd_1345506 25588566722537701306931 := by
  unfold tailWord_1345506
  simp only [CollatzResearch.WordTrace]
  refine ⟨12268658865867257743766093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32716423642312687316709581 12268658865867257743766093)
  ·
    refine ⟨4600747074700221653912285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12268658865867257743766093 4600747074700221653912285)
    ·
      refine ⟨1725280153012583120217107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4600747074700221653912285 1725280153012583120217107)
      ·
        refine ⟨2587920229518874680325661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1725280153012583120217107 2587920229518874680325661)
        ·
          refine ⟨970470086069578005122123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2587920229518874680325661 970470086069578005122123)
          ·
            refine ⟨1455705129104367007683185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970470086069578005122123 1455705129104367007683185)
            ·
              refine ⟨1091778846828275255762389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455705129104367007683185 1091778846828275255762389)
              ·
                refine ⟨25588566722537701306931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1091778846828275255762389 25588566722537701306931)
                ·
                  rfl

theorem cell23_1345506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 7].length) (baseStart_1345506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345506 prefixEnd_1345506 := by exact prefixLift 1345506
  have htrace : WordTrace (prefixWord ++ tailWord_1345506) baseStart_1345506 baseEnd_1345506 := by
    simpa [prefixWord, tailWord_1345506, baseEnd_1345506] using wordTrace_append hprefix tailTrace_1345506
  have hstable : (prefixWord ++ tailWord_1345506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345506).length < 2 ^ (prefixWord ++ tailWord_1345506).sum := by decide
  have hdescent : baseEnd_1345506 < baseStart_1345506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345517 : List Nat := [1, 5, 1, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_1345517 : Nat := 118140960795 + 1345517 * 2 ^ 59
def prefixEnd_1345517 : Nat := 4983230072969 + 3 ^ 40 * 1345517 * 2
def baseEnd_1345517 : Nat := 690896949795717392249587

theorem tailTrace_1345517 : CollatzResearch.WordTrace tailWord_1345517 prefixEnd_1345517 690896949795717392249587 := by
  unfold tailWord_1345517
  simp only [CollatzResearch.WordTrace]
  refine ⟨49075036666429179853714805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32716691110952786569143203 49075036666429179853714805)
  ·
    refine ⟨4600784687477735611285763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49075036666429179853714805 4600784687477735611285763)
    ·
      refine ⟨6901177031216603416928645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4600784687477735611285763 6901177031216603416928645)
      ·
        refine ⟨1293970693353113140674121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6901177031216603416928645 1293970693353113140674121)
        ·
          refine ⟨970478020014834855505591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1293970693353113140674121 970478020014834855505591)
          ·
            refine ⟨1455717030022252283258387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970478020014834855505591 1455717030022252283258387)
            ·
              refine ⟨2183575545033378424887581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455717030022252283258387 2183575545033378424887581)
              ·
                refine ⟨818840829387516909332843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2183575545033378424887581 818840829387516909332843)
                ·
                  refine ⟨1228261244081275363999265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818840829387516909332843 1228261244081275363999265)
                  ·
                    refine ⟨921195933060956522999449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1228261244081275363999265 921195933060956522999449)
                    ·
                      refine ⟨690896949795717392249587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 921195933060956522999449 690896949795717392249587)
                      ·
                        rfl

theorem cell23_1345517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_1345517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345517 prefixEnd_1345517 := by exact prefixLift 1345517
  have htrace : WordTrace (prefixWord ++ tailWord_1345517) baseStart_1345517 baseEnd_1345517 := by
    simpa [prefixWord, tailWord_1345517, baseEnd_1345517] using wordTrace_append hprefix tailTrace_1345517
  have hstable : (prefixWord ++ tailWord_1345517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345517).length < 2 ^ (prefixWord ++ tailWord_1345517).sum := by decide
  have hdescent : baseEnd_1345517 < baseStart_1345517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345528 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 9]
def baseStart_1345528 : Nat := 118140960795 + 1345528 * 2 ^ 59
def prefixEnd_1345528 : Nat := 4983230072969 + 3 ^ 40 * 1345528 * 2
def baseEnd_1345528 : Nat := 76766955342546316579115

theorem tailTrace_1345528 : CollatzResearch.WordTrace tailWord_1345528 prefixEnd_1345528 76766955342546316579115 := by
  unfold tailWord_1345528
  simp only [CollatzResearch.WordTrace]
  refine ⟨24537718934694664366182619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32716958579592885821576825 24537718934694664366182619)
  ·
    refine ⟨36806578402041996549273929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24537718934694664366182619 36806578402041996549273929)
    ·
      refine ⟨27604933801531497411955447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36806578402041996549273929 27604933801531497411955447)
      ·
        refine ⟨41407400702297246117933171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27604933801531497411955447 41407400702297246117933171)
        ·
          refine ⟨62111101053445869176899757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41407400702297246117933171 62111101053445869176899757)
          ·
            refine ⟨23291662895042200941337409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62111101053445869176899757 23291662895042200941337409)
            ·
              refine ⟨17468747171281650706003057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23291662895042200941337409 17468747171281650706003057)
              ·
                refine ⟨13101560378461238029502293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17468747171281650706003057 13101560378461238029502293)
                ·
                  refine ⟨76766955342546316579115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13101560378461238029502293 76766955342546316579115)
                  ·
                    rfl

theorem cell23_1345528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 9].length) (baseStart_1345528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345528 prefixEnd_1345528 := by exact prefixLift 1345528
  have htrace : WordTrace (prefixWord ++ tailWord_1345528) baseStart_1345528 baseEnd_1345528 := by
    simpa [prefixWord, tailWord_1345528, baseEnd_1345528] using wordTrace_append hprefix tailTrace_1345528
  have hstable : (prefixWord ++ tailWord_1345528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345528).length < 2 ^ (prefixWord ++ tailWord_1345528).sum := by decide
  have hdescent : baseEnd_1345528 < baseStart_1345528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345555 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 3]
def baseStart_1345555 : Nat := 118140960795 + 1345555 * 2 ^ 59
def prefixEnd_1345555 : Nat := 4983230072969 + 3 ^ 40 * 1345555 * 2
def baseEnd_1345555 : Nat := 690916462060588243574411

theorem tailTrace_1345555 : CollatzResearch.WordTrace tailWord_1345555 prefixEnd_1345555 690916462060588243574411 := by
  unfold tailWord_1345555
  simp only [CollatzResearch.WordTrace]
  refine ⟨49076422640291512343598119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32717615093527674895732079 49076422640291512343598119)
  ·
    refine ⟨73614633960437268515397179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49076422640291512343598119 73614633960437268515397179)
    ·
      refine ⟨110421950940655902773095769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73614633960437268515397179 110421950940655902773095769)
      ·
        refine ⟨82816463205491927079821827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110421950940655902773095769 82816463205491927079821827)
        ·
          refine ⟨124224694808237890619732741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82816463205491927079821827 124224694808237890619732741)
          ·
            refine ⟨23292130276544604491199889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124224694808237890619732741 23292130276544604491199889)
            ·
              refine ⟨17469097707408453368399917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23292130276544604491199889 17469097707408453368399917)
              ·
                refine ⟨6550911640278170013149969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17469097707408453368399917 6550911640278170013149969)
                ·
                  refine ⟨4913183730208627509862477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6550911640278170013149969 4913183730208627509862477)
                  ·
                    refine ⟨1842443898828235316198429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4913183730208627509862477 1842443898828235316198429)
                    ·
                      refine ⟨690916462060588243574411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1842443898828235316198429 690916462060588243574411)
                      ·
                        rfl

theorem cell23_1345555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 3].length) (baseStart_1345555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345555 prefixEnd_1345555 := by exact prefixLift 1345555
  have htrace : WordTrace (prefixWord ++ tailWord_1345555) baseStart_1345555 baseEnd_1345555 := by
    simpa [prefixWord, tailWord_1345555, baseEnd_1345555] using wordTrace_append hprefix tailTrace_1345555
  have hstable : (prefixWord ++ tailWord_1345555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345555).length < 2 ^ (prefixWord ++ tailWord_1345555).sum := by decide
  have hdescent : baseEnd_1345555 < baseStart_1345555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345585 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_1345585 : Nat := 118140960795 + 1345585 * 2 ^ 59
def prefixEnd_1345585 : Nat := 4983230072969 + 3 ^ 40 * 1345585 * 2
def baseEnd_1345585 : Nat := 690931866480223126199273

theorem tailTrace_1345585 : CollatzResearch.WordTrace tailWord_1345585 prefixEnd_1345585 690931866480223126199273 := by
  unfold tailWord_1345585
  simp only [CollatzResearch.WordTrace]
  refine ⟨49077516830182827467190209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32718344553455218311460139 49077516830182827467190209)
  ·
    refine ⟨36808137622637120600392657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49077516830182827467190209 36808137622637120600392657)
    ·
      refine ⟨27606103216977840450294493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36808137622637120600392657 27606103216977840450294493)
      ·
        refine ⟨10352288706366690168860435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27606103216977840450294493 10352288706366690168860435)
        ·
          refine ⟨15528433059550035253290653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10352288706366690168860435 15528433059550035253290653)
          ·
            refine ⟨5823162397331263219983995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15528433059550035253290653 5823162397331263219983995)
            ·
              refine ⟨8734743595996894829975993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5823162397331263219983995 8734743595996894829975993)
              ·
                refine ⟨6551057696997671122481995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8734743595996894829975993 6551057696997671122481995)
                ·
                  refine ⟨9826586545496506683722993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6551057696997671122481995 9826586545496506683722993)
                  ·
                    refine ⟨7369939909122380012792245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9826586545496506683722993 7369939909122380012792245)
                    ·
                      refine ⟨690931866480223126199273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7369939909122380012792245 690931866480223126199273)
                      ·
                        rfl

theorem cell23_1345585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_1345585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345585 prefixEnd_1345585 := by exact prefixLift 1345585
  have htrace : WordTrace (prefixWord ++ tailWord_1345585) baseStart_1345585 baseEnd_1345585 := by
    simpa [prefixWord, tailWord_1345585, baseEnd_1345585] using wordTrace_append hprefix tailTrace_1345585
  have hstable : (prefixWord ++ tailWord_1345585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345585).length < 2 ^ (prefixWord ++ tailWord_1345585).sum := by decide
  have hdescent : baseEnd_1345585 < baseStart_1345585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345612 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 1, 6, 2]
def baseStart_1345612 : Nat := 118140960795 + 1345612 * 2 ^ 59
def prefixEnd_1345612 : Nat := 4983230072969 + 3 ^ 40 * 1345612 * 2
def baseEnd_1345612 : Nat := 690945730457894520561649

theorem tailTrace_1345612 : CollatzResearch.WordTrace tailWord_1345612 prefixEnd_1345612 690945730457894520561649 := by
  unfold tailWord_1345612
  simp only [CollatzResearch.WordTrace]
  refine ⟨24539250800542505539211545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32719001067390007385615393 24539250800542505539211545)
  ·
    refine ⟨18404438100406879154408659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24539250800542505539211545 18404438100406879154408659)
    ·
      refine ⟨27606657150610318731612989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18404438100406879154408659 27606657150610318731612989)
      ·
        refine ⟨10352496431478869524354871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27606657150610318731612989 10352496431478869524354871)
        ·
          refine ⟨15528744647218304286532307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10352496431478869524354871 15528744647218304286532307)
          ·
            refine ⟨23293116970827456429798461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15528744647218304286532307 23293116970827456429798461)
            ·
              refine ⟨8734918864060296161174423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23293116970827456429798461 8734918864060296161174423)
              ·
                refine ⟨13102378296090444241761635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8734918864060296161174423 13102378296090444241761635)
                ·
                  refine ⟨19653567444135666362642453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13102378296090444241761635 19653567444135666362642453)
                  ·
                    refine ⟨921260973943859360748865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19653567444135666362642453 921260973943859360748865)
                    ·
                      refine ⟨690945730457894520561649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 921260973943859360748865 690945730457894520561649)
                      ·
                        rfl

theorem cell23_1345612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_1345612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345612 prefixEnd_1345612 := by exact prefixLift 1345612
  have htrace : WordTrace (prefixWord ++ tailWord_1345612) baseStart_1345612 baseEnd_1345612 := by
    simpa [prefixWord, tailWord_1345612, baseEnd_1345612] using wordTrace_append hprefix tailTrace_1345612
  have hstable : (prefixWord ++ tailWord_1345612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345612).length < 2 ^ (prefixWord ++ tailWord_1345612).sum := by decide
  have hdescent : baseEnd_1345612 < baseStart_1345612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345615 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 3]
def baseStart_1345615 : Nat := 118140960795 + 1345615 * 2 ^ 59
def prefixEnd_1345615 : Nat := 4983230072969 + 3 ^ 40 * 1345615 * 2
def baseEnd_1345615 : Nat := 690947270899858008824135

theorem tailTrace_1345615 : CollatzResearch.WordTrace tailWord_1345615 prefixEnd_1345615 690947270899858008824135 := by
  unfold tailWord_1345615
  simp only [CollatzResearch.WordTrace]
  refine ⟨49078611020074142590782299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32719074013382761727188199 49078611020074142590782299)
  ·
    refine ⟨73617916530111213886173449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49078611020074142590782299 73617916530111213886173449)
    ·
      refine ⟨55213437397583410414630087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73617916530111213886173449 55213437397583410414630087)
      ·
        refine ⟨82820156096375115621945131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55213437397583410414630087 82820156096375115621945131)
        ·
          refine ⟨124230234144562673432917697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82820156096375115621945131 124230234144562673432917697)
          ·
            refine ⟨93172675608422005074688273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124230234144562673432917697 93172675608422005074688273)
            ·
              refine ⟨69879506706316503806016205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93172675608422005074688273 69879506706316503806016205)
              ·
                refine ⟨26204815014868688927256077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69879506706316503806016205 26204815014868688927256077)
                ·
                  refine ⟨9826805630575758347721029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26204815014868688927256077 9826805630575758347721029)
                  ·
                    refine ⟨1842526055732954690197693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9826805630575758347721029 1842526055732954690197693)
                    ·
                      refine ⟨690947270899858008824135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1842526055732954690197693 690947270899858008824135)
                      ·
                        rfl

theorem cell23_1345615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 3].length) (baseStart_1345615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345615 prefixEnd_1345615 := by exact prefixLift 1345615
  have htrace : WordTrace (prefixWord ++ tailWord_1345615) baseStart_1345615 baseEnd_1345615 := by
    simpa [prefixWord, tailWord_1345615, baseEnd_1345615] using wordTrace_append hprefix tailTrace_1345615
  have hstable : (prefixWord ++ tailWord_1345615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345615).length < 2 ^ (prefixWord ++ tailWord_1345615).sum := by decide
  have hdescent : baseEnd_1345615 < baseStart_1345615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345629 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1345629 : Nat := 118140960795 + 1345629 * 2 ^ 59
def prefixEnd_1345629 : Nat := 4983230072969 + 3 ^ 40 * 1345629 * 2
def baseEnd_1345629 : Nat := 690954459629020954049071

theorem tailTrace_1345629 : CollatzResearch.WordTrace tailWord_1345629 prefixEnd_1345629 690954459629020954049071 := by
  unfold tailWord_1345629
  simp only [CollatzResearch.WordTrace]
  refine ⟨49079121642023422981791941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32719414428015615321194627 49079121642023422981791941)
  ·
    refine ⟨9202335307879391809085989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49079121642023422981791941 9202335307879391809085989)
    ·
      refine ⟨1725437870227385964203623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9202335307879391809085989 1725437870227385964203623)
      ·
        refine ⟨2588156805341078946305435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1725437870227385964203623 2588156805341078946305435)
        ·
          refine ⟨3882235208011618419458153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2588156805341078946305435 3882235208011618419458153)
          ·
            refine ⟨2911676406008713814593615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3882235208011618419458153 2911676406008713814593615)
            ·
              refine ⟨4367514609013070721890423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911676406008713814593615 4367514609013070721890423)
              ·
                refine ⟨6551271913519606082835635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4367514609013070721890423 6551271913519606082835635)
                ·
                  refine ⟨9826907870279409124253453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6551271913519606082835635 9826907870279409124253453)
                  ·
                    refine ⟨3685090451354778421595045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9826907870279409124253453 3685090451354778421595045)
                    ·
                      refine ⟨690954459629020954049071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3685090451354778421595045 690954459629020954049071)
                      ·
                        rfl

theorem cell23_1345629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1345629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345629 prefixEnd_1345629 := by exact prefixLift 1345629
  have htrace : WordTrace (prefixWord ++ tailWord_1345629) baseStart_1345629 baseEnd_1345629 := by
    simpa [prefixWord, tailWord_1345629, baseEnd_1345629] using wordTrace_append hprefix tailTrace_1345629
  have hstable : (prefixWord ++ tailWord_1345629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345629).length < 2 ^ (prefixWord ++ tailWord_1345629).sum := by decide
  have hdescent : baseEnd_1345629 < baseStart_1345629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345632 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 3]
def baseStart_1345632 : Nat := 118140960795 + 1345632 * 2 ^ 59
def prefixEnd_1345632 : Nat := 4983230072969 + 3 ^ 40 * 1345632 * 2
def baseEnd_1345632 : Nat := 690956000070984442311557

theorem tailTrace_1345632 : CollatzResearch.WordTrace tailWord_1345632 prefixEnd_1345632 690956000070984442311557 := by
  unfold tailWord_1345632
  simp only [CollatzResearch.WordTrace]
  refine ⟨24539615530506277247075575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32719487374008369662767433 24539615530506277247075575)
  ·
    refine ⟨36809423295759415870613363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24539615530506277247075575 36809423295759415870613363)
    ·
      refine ⟨55214134943639123805920045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36809423295759415870613363 55214134943639123805920045)
      ·
        refine ⟨20705300603864671427220017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55214134943639123805920045 20705300603864671427220017)
        ·
          refine ⟨15528975452898503570415013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20705300603864671427220017 15528975452898503570415013)
          ·
            refine ⟨2911682897418469419452815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15528975452898503570415013 2911682897418469419452815)
            ·
              refine ⟨4367524346127704129179223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911682897418469419452815 4367524346127704129179223)
              ·
                refine ⟨6551286519191556193768835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4367524346127704129179223 6551286519191556193768835)
                ·
                  refine ⟨9826929778787334290653253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6551286519191556193768835 9826929778787334290653253)
                  ·
                    refine ⟨1842549333522625179497485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9826929778787334290653253 1842549333522625179497485)
                    ·
                      refine ⟨690956000070984442311557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1842549333522625179497485 690956000070984442311557)
                      ·
                        rfl

theorem cell23_1345632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_1345632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345632 prefixEnd_1345632 := by exact prefixLift 1345632
  have htrace : WordTrace (prefixWord ++ tailWord_1345632) baseStart_1345632 baseEnd_1345632 := by
    simpa [prefixWord, tailWord_1345632, baseEnd_1345632] using wordTrace_append hprefix tailTrace_1345632
  have hstable : (prefixWord ++ tailWord_1345632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345632).length < 2 ^ (prefixWord ++ tailWord_1345632).sum := by decide
  have hdescent : baseEnd_1345632 < baseStart_1345632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345655 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_1345655 : Nat := 118140960795 + 1345655 * 2 ^ 59
def prefixEnd_1345655 : Nat := 4983230072969 + 3 ^ 40 * 1345655 * 2
def baseEnd_1345655 : Nat := 690967810126037852323951

theorem tailTrace_1345655 : CollatzResearch.WordTrace tailWord_1345655 prefixEnd_1345655 690967810126037852323951 := by
  unfold tailWord_1345655
  simp only [CollatzResearch.WordTrace]
  refine ⟨49080069939929229422238419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32720046626619486281492279 49080069939929229422238419)
  ·
    refine ⟨73620104909893844133357629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49080069939929229422238419 73620104909893844133357629)
    ·
      refine ⟨27607539341210191550009111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73620104909893844133357629 27607539341210191550009111)
      ·
        refine ⟨41411309011815287325013667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27607539341210191550009111 41411309011815287325013667)
        ·
          refine ⟨62116963517722930987520501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41411309011815287325013667 62116963517722930987520501)
          ·
            refine ⟨5823465329786524780080047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62116963517722930987520501 5823465329786524780080047)
            ·
              refine ⟨8735197994679787170120071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5823465329786524780080047 8735197994679787170120071)
              ·
                refine ⟨13102796992019680755180107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8735197994679787170120071 13102796992019680755180107)
                ·
                  refine ⟨19654195488029521132770161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13102796992019680755180107 19654195488029521132770161)
                  ·
                    refine ⟨14740646616022140849577621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19654195488029521132770161 14740646616022140849577621)
                    ·
                      refine ⟨690967810126037852323951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14740646616022140849577621 690967810126037852323951)
                      ·
                        rfl

theorem cell23_1345655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_1345655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345655 prefixEnd_1345655 := by exact prefixLift 1345655
  have htrace : WordTrace (prefixWord ++ tailWord_1345655) baseStart_1345655 baseEnd_1345655 := by
    simpa [prefixWord, tailWord_1345655, baseEnd_1345655] using wordTrace_append hprefix tailTrace_1345655
  have hstable : (prefixWord ++ tailWord_1345655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345655).length < 2 ^ (prefixWord ++ tailWord_1345655).sum := by decide
  have hdescent : baseEnd_1345655 < baseStart_1345655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345669 : List Nat := [1, 3, 1, 1, 5, 2, 3, 1, 6]
def baseStart_1345669 : Nat := 118140960795 + 1345669 * 2 ^ 59
def prefixEnd_1345669 : Nat := 4983230072969 + 3 ^ 40 * 1345669 * 2
def baseEnd_1345669 : Nat := 76774999872800088616543

theorem tailTrace_1345669 : CollatzResearch.WordTrace tailWord_1345669 prefixEnd_1345669 76774999872800088616543 := by
  unfold tailWord_1345669
  simp only [CollatzResearch.WordTrace]
  refine ⟨49080580561878509813248061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32720387041252339875498707 49080580561878509813248061)
  ·
    refine ⟨18405217710704441179968023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49080580561878509813248061 18405217710704441179968023)
    ·
      refine ⟨27607826566056661769952035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18405217710704441179968023 27607826566056661769952035)
      ·
        refine ⟨41411739849084992654928053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27607826566056661769952035 41411739849084992654928053)
        ·
          refine ⟨3882350610851718061399505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41411739849084992654928053 3882350610851718061399505)
          ·
            refine ⟨2911762958138788546049629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3882350610851718061399505 2911762958138788546049629)
            ·
              refine ⟨1091911109302045704768611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2911762958138788546049629 1091911109302045704768611)
              ·
                refine ⟨1637866663953068557152917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091911109302045704768611 1637866663953068557152917)
                ·
                  refine ⟨76774999872800088616543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1637866663953068557152917 76774999872800088616543)
                  ·
                    rfl

theorem cell23_1345669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 6].length) (baseStart_1345669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345669 prefixEnd_1345669 := by exact prefixLift 1345669
  have htrace : WordTrace (prefixWord ++ tailWord_1345669) baseStart_1345669 baseEnd_1345669 := by
    simpa [prefixWord, tailWord_1345669, baseEnd_1345669] using wordTrace_append hprefix tailTrace_1345669
  have hstable : (prefixWord ++ tailWord_1345669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345669).length < 2 ^ (prefixWord ++ tailWord_1345669).sum := by decide
  have hdescent : baseEnd_1345669 < baseStart_1345669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345690 : List Nat := [3, 1, 1, 5, 3, 1, 1, 3, 1, 4]
def baseStart_1345690 : Nat := 118140960795 + 1345690 * 2 ^ 59
def prefixEnd_1345690 : Nat := 4983230072969 + 3 ^ 40 * 1345690 * 2
def baseEnd_1345690 : Nat := 230328593982981738462097

theorem tailTrace_1345690 : CollatzResearch.WordTrace tailWord_1345690 prefixEnd_1345690 230328593982981738462097 := by
  unfold tailWord_1345690
  simp only [CollatzResearch.WordTrace]
  refine ⟨12270336623700607599940631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32720897663201620266508349 12270336623700607599940631)
  ·
    refine ⟨18405504935550911399910947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12270336623700607599940631 18405504935550911399910947)
    ·
      refine ⟨27608257403326367099866421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18405504935550911399910947 27608257403326367099866421)
      ·
        refine ⟨2588274131561846915612477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27608257403326367099866421 2588274131561846915612477)
        ·
          refine ⟨970602799335692593354679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2588274131561846915612477 970602799335692593354679)
          ·
            refine ⟨1455904199003538890032019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970602799335692593354679 1455904199003538890032019)
            ·
              refine ⟨2183856298505308335048029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455904199003538890032019 2183856298505308335048029)
              ·
                refine ⟨818946111939490625643011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2183856298505308335048029 818946111939490625643011)
                ·
                  refine ⟨1228419167909235938464517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818946111939490625643011 1228419167909235938464517)
                  ·
                    refine ⟨230328593982981738462097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1228419167909235938464517 230328593982981738462097)
                    ·
                      rfl

theorem cell23_1345690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_1345690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345690 prefixEnd_1345690 := by exact prefixLift 1345690
  have htrace : WordTrace (prefixWord ++ tailWord_1345690) baseStart_1345690 baseEnd_1345690 := by
    simpa [prefixWord, tailWord_1345690, baseEnd_1345690] using wordTrace_append hprefix tailTrace_1345690
  have hstable : (prefixWord ++ tailWord_1345690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345690).length < 2 ^ (prefixWord ++ tailWord_1345690).sum := by decide
  have hdescent : baseEnd_1345690 < baseStart_1345690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345713 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1345713 : Nat := 118140960795 + 1345713 * 2 ^ 59
def prefixEnd_1345713 : Nat := 4983230072969 + 3 ^ 40 * 1345713 * 2
def baseEnd_1345713 : Nat := 690997592003998625398685

theorem tailTrace_1345713 : CollatzResearch.WordTrace tailWord_1345713 prefixEnd_1345713 690997592003998625398685 := by
  unfold tailWord_1345713
  simp only [CollatzResearch.WordTrace]
  refine ⟨49082185373719105327849793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32721456915812736885233195 49082185373719105327849793)
  ·
    refine ⟨36811639030289328995887345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49082185373719105327849793 36811639030289328995887345)
    ·
      refine ⟨27608729272716996746915509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36811639030289328995887345 27608729272716996746915509)
      ·
        refine ⟨2588318369317218445023329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27608729272716996746915509 2588318369317218445023329)
        ·
          refine ⟨1941238776987913833767497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2588318369317218445023329 1941238776987913833767497)
          ·
            refine ⟨1455929082740935375325623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1941238776987913833767497 1455929082740935375325623)
            ·
              refine ⟨2183893624111403062988435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455929082740935375325623 2183893624111403062988435)
              ·
                refine ⟨3275840436167104594482653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2183893624111403062988435 3275840436167104594482653)
                ·
                  refine ⟨1228440163562664222930995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3275840436167104594482653 1228440163562664222930995)
                  ·
                    refine ⟨1842660245343996334396493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1228440163562664222930995 1842660245343996334396493)
                    ·
                      refine ⟨690997592003998625398685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1842660245343996334396493 690997592003998625398685)
                      ·
                        rfl

theorem cell23_1345713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1345713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345713 prefixEnd_1345713 := by exact prefixLift 1345713
  have htrace : WordTrace (prefixWord ++ tailWord_1345713) baseStart_1345713 baseEnd_1345713 := by
    simpa [prefixWord, tailWord_1345713, baseEnd_1345713] using wordTrace_append hprefix tailTrace_1345713
  have hstable : (prefixWord ++ tailWord_1345713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345713).length < 2 ^ (prefixWord ++ tailWord_1345713).sum := by decide
  have hdescent : baseEnd_1345713 < baseStart_1345713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345722 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_1345722 : Nat := 118140960795 + 1345722 * 2 ^ 59
def prefixEnd_1345722 : Nat := 4983230072969 + 3 ^ 40 * 1345722 * 2
def baseEnd_1345722 : Nat := 691002213329889090186143

theorem tailTrace_1345722 : CollatzResearch.WordTrace tailWord_1345722 prefixEnd_1345722 691002213329889090186143 := by
  unfold tailWord_1345722
  simp only [CollatzResearch.WordTrace]
  refine ⟨12270628407671624966231855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32721675753790999909951613 12270628407671624966231855)
  ·
    refine ⟨18405942611507437449347783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12270628407671624966231855 18405942611507437449347783)
    ·
      refine ⟨27608913917261156174021675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18405942611507437449347783 27608913917261156174021675)
      ·
        refine ⟨41413370875891734261032513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27608913917261156174021675 41413370875891734261032513)
        ·
          refine ⟨31060028156918800695774385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41413370875891734261032513 31060028156918800695774385)
          ·
            refine ⟨23295021117689100521830789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31060028156918800695774385 23295021117689100521830789)
            ·
              refine ⟨4367816459566706347843273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23295021117689100521830789 4367816459566706347843273)
              ·
                refine ⟨3275862344675029760882455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4367816459566706347843273 3275862344675029760882455)
                ·
                  refine ⟨4913793517012544641323683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275862344675029760882455 4913793517012544641323683)
                  ·
                    refine ⟨7370690275518816961985525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4913793517012544641323683 7370690275518816961985525)
                    ·
                      refine ⟨691002213329889090186143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7370690275518816961985525 691002213329889090186143)
                      ·
                        rfl

theorem cell23_1345722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_1345722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345722 prefixEnd_1345722 := by exact prefixLift 1345722
  have htrace : WordTrace (prefixWord ++ tailWord_1345722) baseStart_1345722 baseEnd_1345722 := by
    simpa [prefixWord, tailWord_1345722, baseEnd_1345722] using wordTrace_append hprefix tailTrace_1345722
  have hstable : (prefixWord ++ tailWord_1345722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345722).length < 2 ^ (prefixWord ++ tailWord_1345722).sum := by decide
  have hdescent : baseEnd_1345722 < baseStart_1345722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345742 : List Nat := [4, 1, 1, 1, 4, 1, 2, 9]
def baseStart_1345742 : Nat := 118140960795 + 1345742 * 2 ^ 59
def prefixEnd_1345742 : Nat := 4983230072969 + 3 ^ 40 * 1345742 * 2
def baseEnd_1345742 : Nat := 25593054923814037479113

theorem tailTrace_1345742 : CollatzResearch.WordTrace tailWord_1345742 prefixEnd_1345742 25593054923814037479113 := by
  unfold tailWord_1345742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6135405386326755410081935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32722162060409362187103653 6135405386326755410081935)
  ·
    refine ⟨9203108079490133115122903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6135405386326755410081935 9203108079490133115122903)
    ·
      refine ⟨13804662119235199672684355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9203108079490133115122903 13804662119235199672684355)
      ·
        refine ⟨20706993178852799509026533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13804662119235199672684355 20706993178852799509026533)
        ·
          refine ⟨3882561221034899907942475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20706993178852799509026533 3882561221034899907942475)
          ·
            refine ⟨5823841831552349861913713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3882561221034899907942475 5823841831552349861913713)
            ·
              refine ⟨4367881373664262396435285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5823841831552349861913713 4367881373664262396435285)
              ·
                refine ⟨25593054923814037479113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4367881373664262396435285 25593054923814037479113)
                ·
                  rfl

theorem cell23_1345742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_1345742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345742 prefixEnd_1345742 := by exact prefixLift 1345742
  have htrace : WordTrace (prefixWord ++ tailWord_1345742) baseStart_1345742 baseEnd_1345742 := by
    simpa [prefixWord, tailWord_1345742, baseEnd_1345742] using wordTrace_append hprefix tailTrace_1345742
  have hstable : (prefixWord ++ tailWord_1345742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345742).length < 2 ^ (prefixWord ++ tailWord_1345742).sum := by decide
  have hdescent : baseEnd_1345742 < baseStart_1345742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345755 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 1, 9]
def baseStart_1345755 : Nat := 118140960795 + 1345755 * 2 ^ 59
def prefixEnd_1345755 : Nat := 4983230072969 + 3 ^ 40 * 1345755 * 2
def baseEnd_1345755 : Nat := 230339719397162487024497

theorem tailTrace_1345755 : CollatzResearch.WordTrace tailWord_1345755 prefixEnd_1345755 230339719397162487024497 := by
  unfold tailWord_1345755
  simp only [CollatzResearch.WordTrace]
  refine ⟨49083717239566946500878719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32722478159711297667252479 49083717239566946500878719)
  ·
    refine ⟨73625575859350419751318079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49083717239566946500878719 73625575859350419751318079)
    ·
      refine ⟨110438363789025629626977119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73625575859350419751318079 110438363789025629626977119)
      ·
        refine ⟨165657545683538444440465679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110438363789025629626977119 165657545683538444440465679)
        ·
          refine ⟨248486318525307666660698519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165657545683538444440465679 248486318525307666660698519)
          ·
            refine ⟨372729477787961499991047779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248486318525307666660698519 372729477787961499991047779)
            ·
              refine ⟨559094216681942249986571669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372729477787961499991047779 559094216681942249986571669)
              ·
                refine ⟨26207541406966042968120547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 559094216681942249986571669 26207541406966042968120547)
                ·
                  refine ⟨39311312110449064452180821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26207541406966042968120547 39311312110449064452180821)
                  ·
                    refine ⟨230339719397162487024497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 39311312110449064452180821 230339719397162487024497)
                    ·
                      rfl

theorem cell23_1345755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 9].length) (baseStart_1345755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345755 prefixEnd_1345755 := by exact prefixLift 1345755
  have htrace : WordTrace (prefixWord ++ tailWord_1345755) baseStart_1345755 baseEnd_1345755 := by
    simpa [prefixWord, tailWord_1345755, baseEnd_1345755] using wordTrace_append hprefix tailTrace_1345755
  have hstable : (prefixWord ++ tailWord_1345755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345755).length < 2 ^ (prefixWord ++ tailWord_1345755).sum := by decide
  have hdescent : baseEnd_1345755 < baseStart_1345755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345763 : List Nat := [1, 1, 1, 8, 1, 1, 2, 2, 2, 4]
def baseStart_1345763 : Nat := 118140960795 + 1345763 * 2 ^ 59
def prefixEnd_1345763 : Nat := 4983230072969 + 3 ^ 40 * 1345763 * 2
def baseEnd_1345763 : Nat := 230341088678907809924485

theorem tailTrace_1345763 : CollatzResearch.WordTrace tailWord_1345763 prefixEnd_1345763 230341088678907809924485 := by
  unfold tailWord_1345763
  simp only [CollatzResearch.WordTrace]
  refine ⟨49084009023537963867169943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32722672682358642578113295 49084009023537963867169943)
  ·
    refine ⟨73626013535306945800754915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49084009023537963867169943 73626013535306945800754915)
    ·
      refine ⟨110439020302960418701132373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73626013535306945800754915 110439020302960418701132373)
      ·
        refine ⟨1294207269175317406653895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 110439020302960418701132373 1294207269175317406653895)
        ·
          refine ⟨1941310903762976109980843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294207269175317406653895 1941310903762976109980843)
          ·
            refine ⟨2911966355644464164971265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941310903762976109980843 2911966355644464164971265)
            ·
              refine ⟨2183974766733348123728449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2911966355644464164971265 2183974766733348123728449)
              ·
                refine ⟨1637981075050011092796337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2183974766733348123728449 1637981075050011092796337)
                ·
                  refine ⟨1228485806287508319597253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1637981075050011092796337 1228485806287508319597253)
                  ·
                    refine ⟨230341088678907809924485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1228485806287508319597253 230341088678907809924485)
                    ·
                      rfl

theorem cell23_1345763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 4].length) (baseStart_1345763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345763 prefixEnd_1345763 := by exact prefixLift 1345763
  have htrace : WordTrace (prefixWord ++ tailWord_1345763) baseStart_1345763 baseEnd_1345763 := by
    simpa [prefixWord, tailWord_1345763, baseEnd_1345763] using wordTrace_append hprefix tailTrace_1345763
  have hstable : (prefixWord ++ tailWord_1345763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345763).length < 2 ^ (prefixWord ++ tailWord_1345763).sum := by decide
  have hdescent : baseEnd_1345763 < baseStart_1345763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345779 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 5, 3, 2]
def baseStart_1345779 : Nat := 118140960795 + 1345779 * 2 ^ 59
def prefixEnd_1345779 : Nat := 4983230072969 + 3 ^ 40 * 1345779 * 2
def baseEnd_1345779 : Nat := 691031481727195367173381

theorem tailTrace_1345779 : CollatzResearch.WordTrace tailWord_1345779 prefixEnd_1345779 691031481727195367173381 := by
  unfold tailWord_1345779
  simp only [CollatzResearch.WordTrace]
  refine ⟨49084592591479998599752391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32723061727653332399834927 49084592591479998599752391)
  ·
    refine ⟨73626888887219997899628587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49084592591479998599752391 73626888887219997899628587)
    ·
      refine ⟨110440333330829996849442881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73626888887219997899628587 110440333330829996849442881)
      ·
        refine ⟨82830249998122497637082161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110440333330829996849442881 82830249998122497637082161)
        ·
          refine ⟨62122687498591873227811621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82830249998122497637082161 62122687498591873227811621)
          ·
            refine ⟨11648003905985976230214679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62122687498591873227811621 11648003905985976230214679)
            ·
              refine ⟨17472005858978964345322019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11648003905985976230214679 17472005858978964345322019)
              ·
                refine ⟨26208008788468446517983029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17472005858978964345322019 26208008788468446517983029)
                ·
                  refine ⟨2457000823918916861060909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26208008788468446517983029 2457000823918916861060909)
                  ·
                    refine ⟨921375308969593822897841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2457000823918916861060909 921375308969593822897841)
                    ·
                      refine ⟨691031481727195367173381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 921375308969593822897841 691031481727195367173381)
                      ·
                        rfl

theorem cell23_1345779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 3, 2].length) (baseStart_1345779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345779 prefixEnd_1345779 := by exact prefixLift 1345779
  have htrace : WordTrace (prefixWord ++ tailWord_1345779) baseStart_1345779 baseEnd_1345779 := by
    simpa [prefixWord, tailWord_1345779, baseEnd_1345779] using wordTrace_append hprefix tailTrace_1345779
  have hstable : (prefixWord ++ tailWord_1345779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345779).length < 2 ^ (prefixWord ++ tailWord_1345779).sum := by decide
  have hdescent : baseEnd_1345779 < baseStart_1345779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345786 : List Nat := [3, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3]
def baseStart_1345786 : Nat := 118140960795 + 1345786 * 2 ^ 59
def prefixEnd_1345786 : Nat := 4983230072969 + 3 ^ 40 * 1345786 * 2
def baseEnd_1345786 : Nat := 691035076091776839785849

theorem tailTrace_1345786 : CollatzResearch.WordTrace tailWord_1345786 prefixEnd_1345786 691035076091776839785849 := by
  unfold tailWord_1345786
  simp only [CollatzResearch.WordTrace]
  refine ⟨12271211975613659698814303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32723231934969759196838141 12271211975613659698814303)
  ·
    refine ⟨18406817963420489548221455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12271211975613659698814303 18406817963420489548221455)
    ·
      refine ⟨27610226945130734322332183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18406817963420489548221455 27610226945130734322332183)
      ·
        refine ⟨41415340417696101483498275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27610226945130734322332183 41415340417696101483498275)
        ·
          refine ⟨62123010626544152225247413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41415340417696101483498275 62123010626544152225247413)
          ·
            refine ⟨5824032246238514271116945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62123010626544152225247413 5824032246238514271116945)
            ·
              refine ⟨4368024184678885703337709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5824032246238514271116945 4368024184678885703337709)
              ·
                refine ⟨1638009069254582138751641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4368024184678885703337709 1638009069254582138751641)
                ·
                  refine ⟨1228506801940936604063731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1638009069254582138751641 1228506801940936604063731)
                  ·
                    refine ⟨1842760202911404906095597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1228506801940936604063731 1842760202911404906095597)
                    ·
                      refine ⟨691035076091776839785849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1842760202911404906095597 691035076091776839785849)
                      ·
                        rfl

theorem cell23_1345786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_1345786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345786 prefixEnd_1345786 := by exact prefixLift 1345786
  have htrace : WordTrace (prefixWord ++ tailWord_1345786) baseStart_1345786 baseEnd_1345786 := by
    simpa [prefixWord, tailWord_1345786, baseEnd_1345786] using wordTrace_append hprefix tailTrace_1345786
  have hstable : (prefixWord ++ tailWord_1345786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345786).length < 2 ^ (prefixWord ++ tailWord_1345786).sum := by decide
  have hdescent : baseEnd_1345786 < baseStart_1345786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345813 : List Nat := [1, 3, 2, 1, 2, 1, 6, 1, 1, 3, 2]
def baseStart_1345813 : Nat := 118140960795 + 1345813 * 2 ^ 59
def prefixEnd_1345813 : Nat := 4983230072969 + 3 ^ 40 * 1345813 * 2
def baseEnd_1345813 : Nat := 691048940069448234148225

theorem tailTrace_1345813 : CollatzResearch.WordTrace tailWord_1345813 prefixEnd_1345813 691048940069448234148225 := by
  unfold tailWord_1345813
  simp only [CollatzResearch.WordTrace]
  refine ⟨49085832673356822406490093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32723888448904548270993395 49085832673356822406490093)
  ·
    refine ⟨18407187252508808402433785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49085832673356822406490093 18407187252508808402433785)
    ·
      refine ⟨13805390439381606301825339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18407187252508808402433785 13805390439381606301825339)
      ·
        refine ⟨20708085659072409452738009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13805390439381606301825339 20708085659072409452738009)
        ·
          refine ⟨15531064244304307089553507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20708085659072409452738009 15531064244304307089553507)
          ·
            refine ⟨23296596366456460634330261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15531064244304307089553507 23296596366456460634330261)
            ·
              refine ⟨1092027954677646592234231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23296596366456460634330261 1092027954677646592234231)
              ·
                refine ⟨1638041932016469888351347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1092027954677646592234231 1638041932016469888351347)
                ·
                  refine ⟨2457062898024704832527021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1638041932016469888351347 2457062898024704832527021)
                  ·
                    refine ⟨921398586759264312197633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2457062898024704832527021 921398586759264312197633)
                    ·
                      refine ⟨691048940069448234148225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 921398586759264312197633 691048940069448234148225)
                      ·
                        rfl

theorem cell23_1345813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_1345813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345813 prefixEnd_1345813 := by exact prefixLift 1345813
  have htrace : WordTrace (prefixWord ++ tailWord_1345813) baseStart_1345813 baseEnd_1345813 := by
    simpa [prefixWord, tailWord_1345813, baseEnd_1345813] using wordTrace_append hprefix tailTrace_1345813
  have hstable : (prefixWord ++ tailWord_1345813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345813).length < 2 ^ (prefixWord ++ tailWord_1345813).sum := by decide
  have hdescent : baseEnd_1345813 < baseStart_1345813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345837 : List Nat := [1, 5, 3, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_1345837 : Nat := 118140960795 + 1345837 * 2 ^ 59
def prefixEnd_1345837 : Nat := 4983230072969 + 3 ^ 40 * 1345837 * 2
def baseEnd_1345837 : Nat := 691061263605156140248115

theorem tailTrace_1345837 : CollatzResearch.WordTrace tailWord_1345837 prefixEnd_1345837 691061263605156140248115 := by
  unfold tailWord_1345837
  simp only [CollatzResearch.WordTrace]
  refine ⟨49086708025269874505363765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32724472016846583003575843 49086708025269874505363765)
  ·
    refine ⟨4601878877369050734877853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49086708025269874505363765 4601878877369050734877853)
    ·
      refine ⟨1725704579013394025579195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4601878877369050734877853 1725704579013394025579195)
      ·
        refine ⟨2588556868520091038368793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1725704579013394025579195 2588556868520091038368793)
        ·
          refine ⟨1941417651390068278776595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2588556868520091038368793 1941417651390068278776595)
          ·
            refine ⟨2912126477085102418164893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941417651390068278776595 2912126477085102418164893)
            ·
              refine ⟨1092047428906913406811835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2912126477085102418164893 1092047428906913406811835)
              ·
                refine ⟨1638071143360370110217753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1092047428906913406811835 1638071143360370110217753)
                ·
                  refine ⟨1228553357520277582663315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1638071143360370110217753 1228553357520277582663315)
                  ·
                    refine ⟨1842830036280416373994973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1228553357520277582663315 1842830036280416373994973)
                    ·
                      refine ⟨691061263605156140248115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1842830036280416373994973 691061263605156140248115)
                      ·
                        rfl

theorem cell23_1345837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_1345837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345837 prefixEnd_1345837 := by exact prefixLift 1345837
  have htrace : WordTrace (prefixWord ++ tailWord_1345837) baseStart_1345837 baseEnd_1345837 := by
    simpa [prefixWord, tailWord_1345837, baseEnd_1345837] using wordTrace_append hprefix tailTrace_1345837
  have hstable : (prefixWord ++ tailWord_1345837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345837).length < 2 ^ (prefixWord ++ tailWord_1345837).sum := by decide
  have hdescent : baseEnd_1345837 < baseStart_1345837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345849 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 7]
def baseStart_1345849 : Nat := 118140960795 + 1345849 * 2 ^ 59
def prefixEnd_1345849 : Nat := 4983230072969 + 3 ^ 40 * 1345849 * 2
def baseEnd_1345849 : Nat := 76785269485890010366451

theorem tailTrace_1345849 : CollatzResearch.WordTrace tailWord_1345849 prefixEnd_1345849 76785269485890010366451 := by
  unfold tailWord_1345849
  simp only [CollatzResearch.WordTrace]
  refine ⟨49087145701226400554800601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32724763800817600369867067 49087145701226400554800601)
  ·
    refine ⟨36815359275919800416100451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49087145701226400554800601 36815359275919800416100451)
    ·
      refine ⟨55223038913879700624150677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36815359275919800416100451 55223038913879700624150677)
      ·
        refine ⟨2588579949088110966757063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55223038913879700624150677 2588579949088110966757063)
        ·
          refine ⟨3882869923632166450135595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2588579949088110966757063 3882869923632166450135595)
          ·
            refine ⟨5824304885448249675203393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3882869923632166450135595 5824304885448249675203393)
            ·
              refine ⟨4368228664086187256402545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5824304885448249675203393 4368228664086187256402545)
              ·
                refine ⟨3276171498064640442301909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4368228664086187256402545 3276171498064640442301909)
                ·
                  refine ⟨76785269485890010366451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3276171498064640442301909 76785269485890010366451)
                  ·
                    rfl

theorem cell23_1345849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 7].length) (baseStart_1345849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345849 prefixEnd_1345849 := by exact prefixLift 1345849
  have htrace : WordTrace (prefixWord ++ tailWord_1345849) baseStart_1345849 baseEnd_1345849 := by
    simpa [prefixWord, tailWord_1345849, baseEnd_1345849] using wordTrace_append hprefix tailTrace_1345849
  have hstable : (prefixWord ++ tailWord_1345849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345849).length < 2 ^ (prefixWord ++ tailWord_1345849).sum := by decide
  have hdescent : baseEnd_1345849 < baseStart_1345849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345879 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 2, 5]
def baseStart_1345879 : Nat := 118140960795 + 1345879 * 2 ^ 59
def prefixEnd_1345879 : Nat := 4983230072969 + 3 ^ 40 * 1345879 * 2
def baseEnd_1345879 : Nat := 230360943264214991974307

theorem tailTrace_1345879 : CollatzResearch.WordTrace tailWord_1345879 prefixEnd_1345879 230360943264214991974307 := by
  unfold tailWord_1345879
  simp only [CollatzResearch.WordTrace]
  refine ⟨49088239891117715678392691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32725493260745143785595127 49088239891117715678392691)
  ·
    refine ⟨73632359836676573517589037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49088239891117715678392691 73632359836676573517589037)
    ·
      refine ⟨27612134938753715069095889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73632359836676573517589037 27612134938753715069095889)
      ·
        refine ⟨20709101204065286301821917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27612134938753715069095889 20709101204065286301821917)
        ·
          refine ⟨7765912951524482363183219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20709101204065286301821917 7765912951524482363183219)
          ·
            refine ⟨11648869427286723544774829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7765912951524482363183219 11648869427286723544774829)
            ·
              refine ⟨4368326035232521329290561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11648869427286723544774829 4368326035232521329290561)
              ·
                refine ⟨3276244526424390996967921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4368326035232521329290561 3276244526424390996967921)
                ·
                  refine ⟨2457183394818293247725941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3276244526424390996967921 2457183394818293247725941)
                  ·
                    refine ⟨230360943264214991974307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2457183394818293247725941 230360943264214991974307)
                    ·
                      rfl

theorem cell23_1345879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_1345879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345879 prefixEnd_1345879 := by exact prefixLift 1345879
  have htrace : WordTrace (prefixWord ++ tailWord_1345879) baseStart_1345879 baseEnd_1345879 := by
    simpa [prefixWord, tailWord_1345879, baseEnd_1345879] using wordTrace_append hprefix tailTrace_1345879
  have hstable : (prefixWord ++ tailWord_1345879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345879).length < 2 ^ (prefixWord ++ tailWord_1345879).sum := by decide
  have hdescent : baseEnd_1345879 < baseStart_1345879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345919 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 3]
def baseStart_1345919 : Nat := 118140960795 + 1345919 * 2 ^ 59
def prefixEnd_1345919 : Nat := 4983230072969 + 3 ^ 40 * 1345919 * 2
def baseEnd_1345919 : Nat := 691103369018824819422737

theorem tailTrace_1345919 : CollatzResearch.WordTrace tailWord_1345919 prefixEnd_1345919 691103369018824819422737 := by
  unfold tailWord_1345919
  simp only [CollatzResearch.WordTrace]
  refine ⟨49089698810972802509848811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32726465873981868339899207 49089698810972802509848811)
  ·
    refine ⟨73634548216459203764773217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49089698810972802509848811 73634548216459203764773217)
    ·
      refine ⟨55225911162344402823579913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73634548216459203764773217 55225911162344402823579913)
      ·
        refine ⟨41419433371758302117684935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55225911162344402823579913 41419433371758302117684935)
        ·
          refine ⟨62129150057637453176527403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41419433371758302117684935 62129150057637453176527403)
          ·
            refine ⟨93193725086456179764791105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62129150057637453176527403 93193725086456179764791105)
            ·
              refine ⟨69895293814842134823593329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93193725086456179764791105 69895293814842134823593329)
              ·
                refine ⟨52421470361131601117694997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69895293814842134823593329 52421470361131601117694997)
                ·
                  refine ⟨2457256423178043802391953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52421470361131601117694997 2457256423178043802391953)
                  ·
                    refine ⟨1842942317383532851793965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2457256423178043802391953 1842942317383532851793965)
                    ·
                      refine ⟨691103369018824819422737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1842942317383532851793965 691103369018824819422737)
                      ·
                        rfl

theorem cell23_1345919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_1345919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345919 prefixEnd_1345919 := by exact prefixLift 1345919
  have htrace : WordTrace (prefixWord ++ tailWord_1345919) baseStart_1345919 baseEnd_1345919 := by
    simpa [prefixWord, tailWord_1345919, baseEnd_1345919] using wordTrace_append hprefix tailTrace_1345919
  have hstable : (prefixWord ++ tailWord_1345919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345919).length < 2 ^ (prefixWord ++ tailWord_1345919).sum := by decide
  have hdescent : baseEnd_1345919 < baseStart_1345919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345950 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_1345950 : Nat := 118140960795 + 1345950 * 2 ^ 59
def prefixEnd_1345950 : Nat := 4983230072969 + 3 ^ 40 * 1345950 * 2
def baseEnd_1345950 : Nat := 691119286919114198135095

theorem tailTrace_1345950 : CollatzResearch.WordTrace tailWord_1345950 prefixEnd_1345950 691119286919114198135095 := by
  unfold tailWord_1345950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6136353684232561850528413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32727219649240329869484869 6136353684232561850528413)
  ·
    refine ⟨2301132631587210693948155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6136353684232561850528413 2301132631587210693948155)
    ·
      refine ⟨3451698947380816040922233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2301132631587210693948155 3451698947380816040922233)
      ·
        refine ⟨2588774210535612030691675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3451698947380816040922233 2588774210535612030691675)
        ·
          refine ⟨3883161315803418046037513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2588774210535612030691675 3883161315803418046037513)
          ·
            refine ⟨2912370986852563534528135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3883161315803418046037513 2912370986852563534528135)
            ·
              refine ⟨4368556480278845301792203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2912370986852563534528135 4368556480278845301792203)
              ·
                refine ⟨6552834720418267952688305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4368556480278845301792203 6552834720418267952688305)
                ·
                  refine ⟨4914626040313700964516229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6552834720418267952688305 4914626040313700964516229)
                  ·
                    refine ⟨921492382558818930846793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4914626040313700964516229 921492382558818930846793)
                    ·
                      refine ⟨691119286919114198135095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 921492382558818930846793 691119286919114198135095)
                      ·
                        rfl

theorem cell23_1345950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_1345950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1345950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1345950 prefixEnd_1345950 := by exact prefixLift 1345950
  have htrace : WordTrace (prefixWord ++ tailWord_1345950) baseStart_1345950 baseEnd_1345950 := by
    simpa [prefixWord, tailWord_1345950, baseEnd_1345950] using wordTrace_append hprefix tailTrace_1345950
  have hstable : (prefixWord ++ tailWord_1345950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345950).length < 2 ^ (prefixWord ++ tailWord_1345950).sum := by decide
  have hdescent : baseEnd_1345950 < baseStart_1345950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346023 : List Nat := [1, 1, 5, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1346023 : Nat := 118140960795 + 1346023 * 2 ^ 59
def prefixEnd_1346023 : Nat := 4983230072969 + 3 ^ 40 * 1346023 * 2
def baseEnd_1346023 : Nat := 691156771006892412522259

theorem tailTrace_1346023 : CollatzResearch.WordTrace tailWord_1346023 prefixEnd_1346023 691156771006892412522259 := by
  unfold tailWord_1346023
  simp only [CollatzResearch.WordTrace]
  refine ⟨49093492002596028271634723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32728994668397352181089815 49093492002596028271634723)
  ·
    refine ⟨73640238003894042407452085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49093492002596028271634723 73640238003894042407452085)
    ·
      refine ⟨6903772312865066475698633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73640238003894042407452085 6903772312865066475698633)
      ·
        refine ⟨5177829234648799856773975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6903772312865066475698633 5177829234648799856773975)
        ·
          refine ⟨7766743851973199785160963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5177829234648799856773975 7766743851973199785160963)
          ·
            refine ⟨11650115777959799677741445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7766743851973199785160963 11650115777959799677741445)
            ·
              refine ⟨2184396708367462439576521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11650115777959799677741445 2184396708367462439576521)
              ·
                refine ⟨1638297531275596829682391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2184396708367462439576521 1638297531275596829682391)
                ·
                  refine ⟨2457446296913395244523587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1638297531275596829682391 2457446296913395244523587)
                  ·
                    refine ⟨3686169445370092866785381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2457446296913395244523587 3686169445370092866785381)
                    ·
                      refine ⟨691156771006892412522259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3686169445370092866785381 691156771006892412522259)
                      ·
                        rfl

theorem cell23_1346023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1346023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346023 prefixEnd_1346023 := by exact prefixLift 1346023
  have htrace : WordTrace (prefixWord ++ tailWord_1346023) baseStart_1346023 baseEnd_1346023 := by
    simpa [prefixWord, tailWord_1346023, baseEnd_1346023] using wordTrace_append hprefix tailTrace_1346023
  have hstable : (prefixWord ++ tailWord_1346023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346023).length < 2 ^ (prefixWord ++ tailWord_1346023).sum := by decide
  have hdescent : baseEnd_1346023 < baseStart_1346023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346034 : List Nat := [3, 2, 1, 4, 2, 2, 1, 3, 1, 1, 3]
def baseStart_1346034 : Nat := 118140960795 + 1346034 * 2 ^ 59
def prefixEnd_1346034 : Nat := 4983230072969 + 3 ^ 40 * 1346034 * 2
def baseEnd_1346034 : Nat := 691162419294091869484709

theorem tailTrace_1346034 : CollatzResearch.WordTrace tailWord_1346034 prefixEnd_1346034 691162419294091869484709 := by
  unfold tailWord_1346034
  simp only [CollatzResearch.WordTrace]
  refine ⟨12273473301389044287571289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32729262137037451433523437 12273473301389044287571289)
  ·
    refine ⟨9205104976041783215678467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12273473301389044287571289 9205104976041783215678467)
    ·
      refine ⟨13807657464062674823517701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9205104976041783215678467 13807657464062674823517701)
      ·
        refine ⟨2588935774511751529409569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13807657464062674823517701 2588935774511751529409569)
        ·
          refine ⟨1941701830883813647057177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2588935774511751529409569 1941701830883813647057177)
          ·
            refine ⟨1456276373162860235292883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1941701830883813647057177 1456276373162860235292883)
            ·
              refine ⟨2184414559744290352939325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456276373162860235292883 2184414559744290352939325)
              ·
                refine ⟨819155459904108882352247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2184414559744290352939325 819155459904108882352247)
                ·
                  refine ⟨1228733189856163323528371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 819155459904108882352247 1228733189856163323528371)
                  ·
                    refine ⟨1843099784784244985292557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1228733189856163323528371 1843099784784244985292557)
                    ·
                      refine ⟨691162419294091869484709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1843099784784244985292557 691162419294091869484709)
                      ·
                        rfl

theorem cell23_1346034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_1346034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346034 prefixEnd_1346034 := by exact prefixLift 1346034
  have htrace : WordTrace (prefixWord ++ tailWord_1346034) baseStart_1346034 baseEnd_1346034 := by
    simpa [prefixWord, tailWord_1346034, baseEnd_1346034] using wordTrace_append hprefix tailTrace_1346034
  have hstable : (prefixWord ++ tailWord_1346034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346034).length < 2 ^ (prefixWord ++ tailWord_1346034).sum := by decide
  have hdescent : baseEnd_1346034 < baseStart_1346034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346073 : List Nat := [1, 2, 1, 2, 1, 1, 2, 7, 2, 1, 3]
def baseStart_1346073 : Nat := 118140960795 + 1346073 * 2 ^ 59
def prefixEnd_1346073 : Nat := 4983230072969 + 3 ^ 40 * 1346073 * 2
def baseEnd_1346073 : Nat := 691182445039617216897029

theorem tailTrace_1346073 : CollatzResearch.WordTrace tailWord_1346073 prefixEnd_1346073 691182445039617216897029 := by
  unfold tailWord_1346073
  simp only [CollatzResearch.WordTrace]
  refine ⟨49095315652414886810954873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32730210434943257873969915 49095315652414886810954873)
  ·
    refine ⟨36821486739311165108216155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49095315652414886810954873 36821486739311165108216155)
    ·
      refine ⟨55232230108966747662324233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36821486739311165108216155 55232230108966747662324233)
      ·
        refine ⟨41424172581725060746743175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55232230108966747662324233 41424172581725060746743175)
        ·
          refine ⟨62136258872587591120114763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41424172581725060746743175 62136258872587591120114763)
          ·
            refine ⟨93204388308881386680172145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62136258872587591120114763 93204388308881386680172145)
            ·
              refine ⟨69903291231661040010129109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93204388308881386680172145 69903291231661040010129109)
              ·
                refine ⟨1638358388242055625237401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 69903291231661040010129109 1638358388242055625237401)
                ·
                  refine ⟨1228768791181541718928051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1638358388242055625237401 1228768791181541718928051)
                  ·
                    refine ⟨1843153186772312578392077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1228768791181541718928051 1843153186772312578392077)
                    ·
                      refine ⟨691182445039617216897029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1843153186772312578392077 691182445039617216897029)
                      ·
                        rfl

theorem cell23_1346073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_1346073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346073 prefixEnd_1346073 := by exact prefixLift 1346073
  have htrace : WordTrace (prefixWord ++ tailWord_1346073) baseStart_1346073 baseEnd_1346073 := by
    simpa [prefixWord, tailWord_1346073, baseEnd_1346073] using wordTrace_append hprefix tailTrace_1346073
  have hstable : (prefixWord ++ tailWord_1346073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346073).length < 2 ^ (prefixWord ++ tailWord_1346073).sum := by decide
  have hdescent : baseEnd_1346073 < baseStart_1346073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346079 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 8]
def baseStart_1346079 : Nat := 118140960795 + 1346079 * 2 ^ 59
def prefixEnd_1346079 : Nat := 4983230072969 + 3 ^ 40 * 1346079 * 2
def baseEnd_1346079 : Nat := 691185525923544193422001

theorem tailTrace_1346079 : CollatzResearch.WordTrace tailWord_1346079 prefixEnd_1346079 691185525923544193422001 := by
  unfold tailWord_1346079
  simp only [CollatzResearch.WordTrace]
  refine ⟨49095534490393149835673291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32730356326928766557115527 49095534490393149835673291)
  ·
    refine ⟨73643301735589724753509937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49095534490393149835673291 73643301735589724753509937)
    ·
      refine ⟨55232476301692293565132453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73643301735589724753509937 55232476301692293565132453)
      ·
        refine ⟨10356089306567305043462335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55232476301692293565132453 10356089306567305043462335)
        ·
          refine ⟨15534133959850957565193503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10356089306567305043462335 15534133959850957565193503)
          ·
            refine ⟨23301200939776436347790255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15534133959850957565193503 23301200939776436347790255)
            ·
              refine ⟨34951801409664654521685383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23301200939776436347790255 34951801409664654521685383)
              ·
                refine ⟨52427702114496981782528075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34951801409664654521685383 52427702114496981782528075)
                ·
                  refine ⟨78641553171745472673792113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52427702114496981782528075 78641553171745472673792113)
                  ·
                    refine ⟨58981164878809104505344085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78641553171745472673792113 58981164878809104505344085)
                    ·
                      refine ⟨691185525923544193422001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 58981164878809104505344085 691185525923544193422001)
                      ·
                        rfl

theorem cell23_1346079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_1346079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346079 prefixEnd_1346079 := by exact prefixLift 1346079
  have htrace : WordTrace (prefixWord ++ tailWord_1346079) baseStart_1346079 baseEnd_1346079 := by
    simpa [prefixWord, tailWord_1346079, baseEnd_1346079] using wordTrace_append hprefix tailTrace_1346079
  have hstable : (prefixWord ++ tailWord_1346079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346079).length < 2 ^ (prefixWord ++ tailWord_1346079).sum := by decide
  have hdescent : baseEnd_1346079 < baseStart_1346079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346126 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_1346126 : Nat := 118140960795 + 1346126 * 2 ^ 59
def prefixEnd_1346126 : Nat := 4983230072969 + 3 ^ 40 * 1346126 * 2
def baseEnd_1346126 : Nat := 691209659514305509534285

theorem tailTrace_1346126 : CollatzResearch.WordTrace tailWord_1346126 prefixEnd_1346126 691209659514305509534285 := by
  unfold tailWord_1346126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6137156090152859607829279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32731499147481917908422821 6137156090152859607829279)
  ·
    refine ⟨9205734135229289411743919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6137156090152859607829279 9205734135229289411743919)
    ·
      refine ⟨13808601202843934117615879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9205734135229289411743919 13808601202843934117615879)
      ·
        refine ⟨20712901804265901176423819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13808601202843934117615879 20712901804265901176423819)
        ·
          refine ⟨31069352706398851764635729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20712901804265901176423819 31069352706398851764635729)
          ·
            refine ⟨23302014529799138823476797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31069352706398851764635729 23302014529799138823476797)
            ·
              refine ⟨8738255448674677058803799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23302014529799138823476797 8738255448674677058803799)
              ·
                refine ⟨13107383173012015588205699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8738255448674677058803799 13107383173012015588205699)
                ·
                  refine ⟨19661074759518023382308549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13107383173012015588205699 19661074759518023382308549)
                  ·
                    refine ⟨3686451517409629384182853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19661074759518023382308549 3686451517409629384182853)
                    ·
                      refine ⟨691209659514305509534285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3686451517409629384182853 691209659514305509534285)
                      ·
                        rfl

theorem cell23_1346126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_1346126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346126 prefixEnd_1346126 := by exact prefixLift 1346126
  have htrace : WordTrace (prefixWord ++ tailWord_1346126) baseStart_1346126 baseEnd_1346126 := by
    simpa [prefixWord, tailWord_1346126, baseEnd_1346126] using wordTrace_append hprefix tailTrace_1346126
  have hstable : (prefixWord ++ tailWord_1346126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346126).length < 2 ^ (prefixWord ++ tailWord_1346126).sum := by decide
  have hdescent : baseEnd_1346126 < baseStart_1346126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346130 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_1346130 : Nat := 118140960795 + 1346130 * 2 ^ 59
def prefixEnd_1346130 : Nat := 4983230072969 + 3 ^ 40 * 1346130 * 2
def baseEnd_1346130 : Nat := 691211713436923493884267

theorem tailTrace_1346130 : CollatzResearch.WordTrace tailWord_1346130 prefixEnd_1346130 691211713436923493884267 := by
  unfold tailWord_1346130
  simp only [CollatzResearch.WordTrace]
  refine ⟨12274348653302096386444961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32731596408805590363853229 12274348653302096386444961)
  ·
    refine ⟨9205761489976572289833721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12274348653302096386444961 9205761489976572289833721)
    ·
      refine ⟨6904321117482429217375291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9205761489976572289833721 6904321117482429217375291)
      ·
        refine ⟨10356481676223643826062937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6904321117482429217375291 10356481676223643826062937)
        ·
          refine ⟨7767361257167732869547203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10356481676223643826062937 7767361257167732869547203)
          ·
            refine ⟨11651041885751599304320805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7767361257167732869547203 11651041885751599304320805)
            ·
              refine ⟨2184570353578424869560151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11651041885751599304320805 2184570353578424869560151)
              ·
                refine ⟨3276855530367637304340227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184570353578424869560151 3276855530367637304340227)
                ·
                  refine ⟨4915283295551455956510341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276855530367637304340227 4915283295551455956510341)
                  ·
                    refine ⟨921615617915897991845689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4915283295551455956510341 921615617915897991845689)
                    ·
                      refine ⟨691211713436923493884267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 921615617915897991845689 691211713436923493884267)
                      ·
                        rfl

theorem cell23_1346130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_1346130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346130 prefixEnd_1346130 := by exact prefixLift 1346130
  have htrace : WordTrace (prefixWord ++ tailWord_1346130) baseStart_1346130 baseEnd_1346130 := by
    simpa [prefixWord, tailWord_1346130, baseEnd_1346130] using wordTrace_append hprefix tailTrace_1346130
  have hstable : (prefixWord ++ tailWord_1346130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346130).length < 2 ^ (prefixWord ++ tailWord_1346130).sum := by decide
  have hdescent : baseEnd_1346130 < baseStart_1346130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346223 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 3]
def baseStart_1346223 : Nat := 118140960795 + 1346223 * 2 ^ 59
def prefixEnd_1346223 : Nat := 4983230072969 + 3 ^ 40 * 1346223 * 2
def baseEnd_1346223 : Nat := 691259467137791630021339

theorem tailTrace_1346223 : CollatzResearch.WordTrace tailWord_1346223 prefixEnd_1346223 691259467137791630021339 := by
  unfold tailWord_1346223
  simp only [CollatzResearch.WordTrace]
  refine ⟨49100786601871462428915323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32733857734580974952610215 49100786601871462428915323)
  ·
    refine ⟨73651179902807193643372985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49100786601871462428915323 73651179902807193643372985)
    ·
      refine ⟨55238384927105395232529739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73651179902807193643372985 55238384927105395232529739)
      ·
        refine ⟨82857577390658092848794609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55238384927105395232529739 82857577390658092848794609)
        ·
          refine ⟨62143183042993569636595957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82857577390658092848794609 62143183042993569636595957)
          ·
            refine ⟨5825923410280647153430871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62143183042993569636595957 5825923410280647153430871)
            ·
              refine ⟨8738885115420970730146307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5825923410280647153430871 8738885115420970730146307)
              ·
                refine ⟨13108327673131456095219461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8738885115420970730146307 13108327673131456095219461)
                ·
                  refine ⟨2457811438712148017853649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13108327673131456095219461 2457811438712148017853649)
                  ·
                    refine ⟨1843358579034111013390237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2457811438712148017853649 1843358579034111013390237)
                    ·
                      refine ⟨691259467137791630021339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1843358579034111013390237 691259467137791630021339)
                      ·
                        rfl

theorem cell23_1346223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 3].length) (baseStart_1346223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346223 prefixEnd_1346223 := by exact prefixLift 1346223
  have htrace : WordTrace (prefixWord ++ tailWord_1346223) baseStart_1346223 baseEnd_1346223 := by
    simpa [prefixWord, tailWord_1346223, baseEnd_1346223] using wordTrace_append hprefix tailTrace_1346223
  have hstable : (prefixWord ++ tailWord_1346223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346223).length < 2 ^ (prefixWord ++ tailWord_1346223).sum := by decide
  have hdescent : baseEnd_1346223 < baseStart_1346223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346303 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 6, 4]
def baseStart_1346303 : Nat := 118140960795 + 1346303 * 2 ^ 59
def prefixEnd_1346303 : Nat := 4983230072969 + 3 ^ 40 * 1346303 * 2
def baseEnd_1346303 : Nat := 230433515196717105673657

theorem tailTrace_1346303 : CollatzResearch.WordTrace tailWord_1346303 prefixEnd_1346303 230433515196717105673657 := by
  unfold tailWord_1346303
  simp only [CollatzResearch.WordTrace]
  refine ⟨49103704441581636091827563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32735802961054424061218375 49103704441581636091827563)
  ·
    refine ⟨73655556662372454137741345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49103704441581636091827563 73655556662372454137741345)
    ·
      refine ⟨55241667496779340603306009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73655556662372454137741345 55241667496779340603306009)
      ·
        refine ⟨41431250622584505452479507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55241667496779340603306009 41431250622584505452479507)
        ·
          refine ⟨62146875933876758178719261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41431250622584505452479507 62146875933876758178719261)
          ·
            refine ⟨23305078475203784317019723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62146875933876758178719261 23305078475203784317019723)
            ·
              refine ⟨34957617712805676475529585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23305078475203784317019723 34957617712805676475529585)
              ·
                refine ⟨26218213284604257356647189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34957617712805676475529585 26218213284604257356647189)
                ·
                  refine ⟨1228978747715824563592837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26218213284604257356647189 1228978747715824563592837)
                  ·
                    refine ⟨230433515196717105673657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1228978747715824563592837 230433515196717105673657)
                    ·
                      rfl

theorem cell23_1346303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 4].length) (baseStart_1346303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346303 prefixEnd_1346303 := by exact prefixLift 1346303
  have htrace : WordTrace (prefixWord ++ tailWord_1346303) baseStart_1346303 baseEnd_1346303 := by
    simpa [prefixWord, tailWord_1346303, baseEnd_1346303] using wordTrace_append hprefix tailTrace_1346303
  have hstable : (prefixWord ++ tailWord_1346303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346303).length < 2 ^ (prefixWord ++ tailWord_1346303).sum := by decide
  have hdescent : baseEnd_1346303 < baseStart_1346303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346323 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 4]
def baseStart_1346323 : Nat := 118140960795 + 1346323 * 2 ^ 59
def prefixEnd_1346323 : Nat := 4983230072969 + 3 ^ 40 * 1346323 * 2
def baseEnd_1346323 : Nat := 691310815203241238770879

theorem tailTrace_1346323 : CollatzResearch.WordTrace tailWord_1346323 prefixEnd_1346323 691310815203241238770879 := by
  unfold tailWord_1346323
  simp only [CollatzResearch.WordTrace]
  refine ⟨49104433901509179507555623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32736289267672786338370415 49104433901509179507555623)
  ·
    refine ⟨73656650852263769261333435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49104433901509179507555623 73656650852263769261333435)
    ·
      refine ⟨110484976278395653892000153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73656650852263769261333435 110484976278395653892000153)
      ·
        refine ⟨82863732208796740419000115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110484976278395653892000153 82863732208796740419000115)
        ·
          refine ⟨124295598313195110628500173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82863732208796740419000115 124295598313195110628500173)
          ·
            refine ⟨46610849367448166485687565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124295598313195110628500173 46610849367448166485687565)
            ·
              refine ⟨17479068512793062432132837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46610849367448166485687565 17479068512793062432132837)
              ·
                refine ⟨3277325346148699206024907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17479068512793062432132837 3277325346148699206024907)
                ·
                  refine ⟨4915988019223048809037361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277325346148699206024907 4915988019223048809037361)
                  ·
                    refine ⟨3686991014417286606778021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4915988019223048809037361 3686991014417286606778021)
                    ·
                      refine ⟨691310815203241238770879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3686991014417286606778021 691310815203241238770879)
                      ·
                        rfl

theorem cell23_1346323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_1346323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346323 prefixEnd_1346323 := by exact prefixLift 1346323
  have htrace : WordTrace (prefixWord ++ tailWord_1346323) baseStart_1346323 baseEnd_1346323 := by
    simpa [prefixWord, tailWord_1346323, baseEnd_1346323] using wordTrace_append hprefix tailTrace_1346323
  have hstable : (prefixWord ++ tailWord_1346323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346323).length < 2 ^ (prefixWord ++ tailWord_1346323).sum := by decide
  have hdescent : baseEnd_1346323 < baseStart_1346323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346327 : List Nat := [1, 1, 3, 4, 3, 1, 1, 3, 1, 1, 4]
def baseStart_1346327 : Nat := 118140960795 + 1346327 * 2 ^ 59
def prefixEnd_1346327 : Nat := 4983230072969 + 3 ^ 40 * 1346327 * 2
def baseEnd_1346327 : Nat := 691312869125859223120861

theorem tailTrace_1346327 : CollatzResearch.WordTrace tailWord_1346327 prefixEnd_1346327 691312869125859223120861 := by
  unfold tailWord_1346327
  simp only [CollatzResearch.WordTrace]
  refine ⟨49104579793494688190701235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32736386528996458793800823 49104579793494688190701235)
  ·
    refine ⟨73656869690242032286051853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49104579793494688190701235 73656869690242032286051853)
    ·
      refine ⟨27621326133840762107269445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73656869690242032286051853 27621326133840762107269445)
      ·
        refine ⟨5178998650095142895113021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27621326133840762107269445 5178998650095142895113021)
        ·
          refine ⟨1942124493785678585667383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5178998650095142895113021 1942124493785678585667383)
          ·
            refine ⟨2913186740678517878501075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1942124493785678585667383 2913186740678517878501075)
            ·
              refine ⟨4369780111017776817751613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913186740678517878501075 4369780111017776817751613)
              ·
                refine ⟨1638667541631666306656855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4369780111017776817751613 1638667541631666306656855)
                ·
                  refine ⟨2458001312447499459985283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1638667541631666306656855 2458001312447499459985283)
                  ·
                    refine ⟨3687001968671249189977925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2458001312447499459985283 3687001968671249189977925)
                    ·
                      refine ⟨691312869125859223120861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3687001968671249189977925 691312869125859223120861)
                      ·
                        rfl

theorem cell23_1346327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_1346327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346327 prefixEnd_1346327 := by exact prefixLift 1346327
  have htrace : WordTrace (prefixWord ++ tailWord_1346327) baseStart_1346327 baseEnd_1346327 := by
    simpa [prefixWord, tailWord_1346327, baseEnd_1346327] using wordTrace_append hprefix tailTrace_1346327
  have hstable : (prefixWord ++ tailWord_1346327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346327).length < 2 ^ (prefixWord ++ tailWord_1346327).sum := by decide
  have hdescent : baseEnd_1346327 < baseStart_1346327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346344 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_1346344 : Nat := 118140960795 + 1346344 * 2 ^ 59
def prefixEnd_1346344 : Nat := 4983230072969 + 3 ^ 40 * 1346344 * 2
def baseEnd_1346344 : Nat := 691321598296985656608283

theorem tailTrace_1346344 : CollatzResearch.WordTrace tailWord_1346344 prefixEnd_1346344 691321598296985656608283 := by
  unfold tailWord_1346344
  simp only [CollatzResearch.WordTrace]
  refine ⟨24552599917216550047035043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32736799889622066729380057 24552599917216550047035043)
  ·
    refine ⟨36828899875824825070552565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24552599917216550047035043 36828899875824825070552565)
    ·
      refine ⟨3452709363358577350364303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36828899875824825070552565 3452709363358577350364303)
      ·
        refine ⟨5179064045037866025546455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3452709363358577350364303 5179064045037866025546455)
        ·
          refine ⟨7768596067556799038319683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5179064045037866025546455 7768596067556799038319683)
          ·
            refine ⟨11652894101335198557479525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7768596067556799038319683 11652894101335198557479525)
            ·
              refine ⟨2184917644000349729527411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11652894101335198557479525 2184917644000349729527411)
              ·
                refine ⟨3277376466000524594291117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184917644000349729527411 3277376466000524594291117)
                ·
                  refine ⟨1229016174750196722859169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3277376466000524594291117 1229016174750196722859169)
                  ·
                    refine ⟨921762131062647542144377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1229016174750196722859169 921762131062647542144377)
                    ·
                      refine ⟨691321598296985656608283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 921762131062647542144377 691321598296985656608283)
                      ·
                        rfl

theorem cell23_1346344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_1346344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346344 prefixEnd_1346344 := by exact prefixLift 1346344
  have htrace : WordTrace (prefixWord ++ tailWord_1346344) baseStart_1346344 baseEnd_1346344 := by
    simpa [prefixWord, tailWord_1346344, baseEnd_1346344] using wordTrace_append hprefix tailTrace_1346344
  have hstable : (prefixWord ++ tailWord_1346344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346344).length < 2 ^ (prefixWord ++ tailWord_1346344).sum := by decide
  have hdescent : baseEnd_1346344 < baseStart_1346344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346357 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_1346357 : Nat := 118140960795 + 1346357 * 2 ^ 59
def prefixEnd_1346357 : Nat := 4983230072969 + 3 ^ 40 * 1346357 * 2
def baseEnd_1346357 : Nat := 691328273545494105745723

theorem tailTrace_1346357 : CollatzResearch.WordTrace tailWord_1346357 prefixEnd_1346357 691328273545494105745723 := by
  unfold tailWord_1346357
  simp only [CollatzResearch.WordTrace]
  refine ⟨49105673983386003314293325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32737115988924002209528883 49105673983386003314293325)
  ·
    refine ⟨18414627743769751242859997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49105673983386003314293325 18414627743769751242859997)
    ·
      refine ⟨6905485403913656716072499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18414627743769751242859997 6905485403913656716072499)
      ·
        refine ⟨10358228105870485074108749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6905485403913656716072499 10358228105870485074108749)
        ·
          refine ⟨3884335539701431902790781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10358228105870485074108749 3884335539701431902790781)
          ·
            refine ⟨1456625827388036963546543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3884335539701431902790781 1456625827388036963546543)
            ·
              refine ⟨2184938741082055445319815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456625827388036963546543 2184938741082055445319815)
              ·
                refine ⟨3277408111623083167979723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184938741082055445319815 3277408111623083167979723)
                ·
                  refine ⟨4916112167434624751969585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277408111623083167979723 4916112167434624751969585)
                  ·
                    refine ⟨3687084125575968563977189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4916112167434624751969585 3687084125575968563977189)
                    ·
                      refine ⟨691328273545494105745723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3687084125575968563977189 691328273545494105745723)
                      ·
                        rfl

theorem cell23_1346357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_1346357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346357 prefixEnd_1346357 := by exact prefixLift 1346357
  have htrace : WordTrace (prefixWord ++ tailWord_1346357) baseStart_1346357 baseEnd_1346357 := by
    simpa [prefixWord, tailWord_1346357, baseEnd_1346357] using wordTrace_append hprefix tailTrace_1346357
  have hstable : (prefixWord ++ tailWord_1346357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346357).length < 2 ^ (prefixWord ++ tailWord_1346357).sum := by decide
  have hdescent : baseEnd_1346357 < baseStart_1346357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346421 : List Nat := [1, 3, 4, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_1346421 : Nat := 118140960795 + 1346421 * 2 ^ 59
def prefixEnd_1346421 : Nat := 4983230072969 + 3 ^ 40 * 1346421 * 2
def baseEnd_1346421 : Nat := 691361136307381855345429

theorem tailTrace_1346421 : CollatzResearch.WordTrace tailWord_1346421 prefixEnd_1346421 691361136307381855345429 := by
  unfold tailWord_1346421
  simp only [CollatzResearch.WordTrace]
  refine ⟨49108008255154142244623117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32738672170102761496415411 49108008255154142244623117)
  ·
    refine ⟨18415503095682803341733669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49108008255154142244623117 18415503095682803341733669)
    ·
      refine ⟨3452906830440525626575063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18415503095682803341733669 3452906830440525626575063)
      ·
        refine ⟨5179360245660788439862595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3452906830440525626575063 5179360245660788439862595)
        ·
          refine ⟨7769040368491182659793893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5179360245660788439862595 7769040368491182659793893)
          ·
            refine ⟨1456695069092096748711355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7769040368491182659793893 1456695069092096748711355)
            ·
              refine ⟨2185042603638145123067033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456695069092096748711355 2185042603638145123067033)
              ·
                refine ⟨1638781952728608842300275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2185042603638145123067033 1638781952728608842300275)
                ·
                  refine ⟨2458172929092913263450413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1638781952728608842300275 2458172929092913263450413)
                  ·
                    refine ⟨921814848409842473793905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2458172929092913263450413 921814848409842473793905)
                    ·
                      refine ⟨691361136307381855345429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 921814848409842473793905 691361136307381855345429)
                      ·
                        rfl

theorem cell23_1346421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_1346421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346421 prefixEnd_1346421 := by exact prefixLift 1346421
  have htrace : WordTrace (prefixWord ++ tailWord_1346421) baseStart_1346421 baseEnd_1346421 := by
    simpa [prefixWord, tailWord_1346421, baseEnd_1346421] using wordTrace_append hprefix tailTrace_1346421
  have hstable : (prefixWord ++ tailWord_1346421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346421).length < 2 ^ (prefixWord ++ tailWord_1346421).sum := by decide
  have hdescent : baseEnd_1346421 < baseStart_1346421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346423 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 7]
def baseStart_1346423 : Nat := 118140960795 + 1346423 * 2 ^ 59
def prefixEnd_1346423 : Nat := 4983230072969 + 3 ^ 40 * 1346423 * 2
def baseEnd_1346423 : Nat := 76818018140965649724491

theorem tailTrace_1346423 : CollatzResearch.WordTrace tailWord_1346423 prefixEnd_1346423 76818018140965649724491 := by
  unfold tailWord_1346423
  simp only [CollatzResearch.WordTrace]
  refine ⟨49108081201146896586195923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32738720800764597724130615 49108081201146896586195923)
  ·
    refine ⟨73662121801720344879293885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49108081201146896586195923 73662121801720344879293885)
    ·
      refine ⟨27623295675645129329735207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73662121801720344879293885 27623295675645129329735207)
      ·
        refine ⟨41434943513467693994602811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27623295675645129329735207 41434943513467693994602811)
        ·
          refine ⟨62152415270201540991904217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41434943513467693994602811 62152415270201540991904217)
          ·
            refine ⟨46614311452651155743928163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62152415270201540991904217 46614311452651155743928163)
            ·
              refine ⟨69921467178976733615892245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46614311452651155743928163 69921467178976733615892245)
              ·
                refine ⟨3277568774014534388244949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69921467178976733615892245 3277568774014534388244949)
                ·
                  refine ⟨76818018140965649724491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3277568774014534388244949 76818018140965649724491)
                  ·
                    rfl

theorem cell23_1346423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 7].length) (baseStart_1346423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346423 prefixEnd_1346423 := by exact prefixLift 1346423
  have htrace : WordTrace (prefixWord ++ tailWord_1346423) baseStart_1346423 baseEnd_1346423 := by
    simpa [prefixWord, tailWord_1346423, baseEnd_1346423] using wordTrace_append hprefix tailTrace_1346423
  have hstable : (prefixWord ++ tailWord_1346423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346423).length < 2 ^ (prefixWord ++ tailWord_1346423).sum := by decide
  have hdescent : baseEnd_1346423 < baseStart_1346423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346483 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 1, 10]
def baseStart_1346483 : Nat := 118140960795 + 1346483 * 2 ^ 59
def prefixEnd_1346483 : Nat := 4983230072969 + 3 ^ 40 * 1346483 * 2
def baseEnd_1346483 : Nat := 230464324035986870923381

theorem tailTrace_1346483 : CollatzResearch.WordTrace tailWord_1346483 prefixEnd_1346483 230464324035986870923381 := by
  unfold tailWord_1346483
  simp only [CollatzResearch.WordTrace]
  refine ⟨49110269580929526833380103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32740179720619684555586735 49110269580929526833380103)
  ·
    refine ⟨73665404371394290250070155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49110269580929526833380103 73665404371394290250070155)
    ·
      refine ⟨110498106557091435375105233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73665404371394290250070155 110498106557091435375105233)
      ·
        refine ⟨82873579917818576531328925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110498106557091435375105233 82873579917818576531328925)
        ·
          refine ⟨31077592469181966199248347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82873579917818576531328925 31077592469181966199248347)
          ·
            refine ⟨46616388703772949298872521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31077592469181966199248347 46616388703772949298872521)
            ·
              refine ⟨34962291527829711974154391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46616388703772949298872521 34962291527829711974154391)
              ·
                refine ⟨52443437291744567961231587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34962291527829711974154391 52443437291744567961231587)
                ·
                  refine ⟨78665155937616851941847381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52443437291744567961231587 78665155937616851941847381)
                  ·
                    refine ⟨230464324035986870923381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 78665155937616851941847381 230464324035986870923381)
                    ·
                      rfl

theorem cell23_1346483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 10].length) (baseStart_1346483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346483 prefixEnd_1346483 := by exact prefixLift 1346483
  have htrace : WordTrace (prefixWord ++ tailWord_1346483) baseStart_1346483 baseEnd_1346483 := by
    simpa [prefixWord, tailWord_1346483, baseEnd_1346483] using wordTrace_append hprefix tailTrace_1346483
  have hstable : (prefixWord ++ tailWord_1346483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346483).length < 2 ^ (prefixWord ++ tailWord_1346483).sum := by decide
  have hdescent : baseEnd_1346483 < baseStart_1346483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346490 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_1346490 : Nat := 118140960795 + 1346490 * 2 ^ 59
def prefixEnd_1346490 : Nat := 4983230072969 + 3 ^ 40 * 1346490 * 2
def baseEnd_1346490 : Nat := 691396566472542085382611

theorem tailTrace_1346490 : CollatzResearch.WordTrace tailWord_1346490 prefixEnd_1346490 691396566472542085382611 := by
  unfold tailWord_1346490
  simp only [CollatzResearch.WordTrace]
  refine ⟨12277631222976041757221231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32740349927936111352589949 12277631222976041757221231)
  ·
    refine ⟨18416446834464062635831847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12277631222976041757221231 18416446834464062635831847)
    ·
      refine ⟨27624670251696093953747771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18416446834464062635831847 27624670251696093953747771)
      ·
        refine ⟨41437005377544140930621657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27624670251696093953747771 41437005377544140930621657)
        ·
          refine ⟨31077754033158105697966243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41437005377544140930621657 31077754033158105697966243)
          ·
            refine ⟨46616631049737158546949365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31077754033158105697966243 46616631049737158546949365)
            ·
              refine ⟨4370309160912858613776503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46616631049737158546949365 4370309160912858613776503)
              ·
                refine ⟨6555463741369287920664755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4370309160912858613776503 6555463741369287920664755)
                ·
                  refine ⟨9833195612053931880997133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6555463741369287920664755 9833195612053931880997133)
                  ·
                    refine ⟨3687448354520224455373925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9833195612053931880997133 3687448354520224455373925)
                    ·
                      refine ⟨691396566472542085382611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3687448354520224455373925 691396566472542085382611)
                      ·
                        rfl

theorem cell23_1346490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_1346490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346490 prefixEnd_1346490 := by exact prefixLift 1346490
  have htrace : WordTrace (prefixWord ++ tailWord_1346490) baseStart_1346490 baseEnd_1346490 := by
    simpa [prefixWord, tailWord_1346490, baseEnd_1346490] using wordTrace_append hprefix tailTrace_1346490
  have hstable : (prefixWord ++ tailWord_1346490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346490).length < 2 ^ (prefixWord ++ tailWord_1346490).sum := by decide
  have hdescent : baseEnd_1346490 < baseStart_1346490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346502 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_1346502 : Nat := 118140960795 + 1346502 * 2 ^ 59
def prefixEnd_1346502 : Nat := 4983230072969 + 3 ^ 40 * 1346502 * 2
def baseEnd_1346502 : Nat := 691402728240396038432557

theorem tailTrace_1346502 : CollatzResearch.WordTrace tailWord_1346502 prefixEnd_1346502 691402728240396038432557 := by
  unfold tailWord_1346502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1534717580245646658697555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32740641711907128718881173 1534717580245646658697555)
  ·
    refine ⟨2302076370368469988046333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1534717580245646658697555 2302076370368469988046333)
    ·
      refine ⟨863278638888176245517375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2302076370368469988046333 863278638888176245517375)
      ·
        refine ⟨1294917958332264368276063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 863278638888176245517375 1294917958332264368276063)
        ·
          refine ⟨1942376937498396552414095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294917958332264368276063 1942376937498396552414095)
          ·
            refine ⟨2913565406247594828621143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1942376937498396552414095 2913565406247594828621143)
            ·
              refine ⟨4370348109371392242931715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913565406247594828621143 4370348109371392242931715)
              ·
                refine ⟨6555522164057088364397573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4370348109371392242931715 6555522164057088364397573)
                ·
                  refine ⟨1229160405760704068324545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6555522164057088364397573 1229160405760704068324545)
                  ·
                    refine ⟨921870304320528051243409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1229160405760704068324545 921870304320528051243409)
                    ·
                      refine ⟨691402728240396038432557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 921870304320528051243409 691402728240396038432557)
                      ·
                        rfl

theorem cell23_1346502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_1346502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346502 prefixEnd_1346502 := by exact prefixLift 1346502
  have htrace : WordTrace (prefixWord ++ tailWord_1346502) baseStart_1346502 baseEnd_1346502 := by
    simpa [prefixWord, tailWord_1346502, baseEnd_1346502] using wordTrace_append hprefix tailTrace_1346502
  have hstable : (prefixWord ++ tailWord_1346502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346502).length < 2 ^ (prefixWord ++ tailWord_1346502).sum := by decide
  have hdescent : baseEnd_1346502 < baseStart_1346502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346507 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 2, 4, 2]
def baseStart_1346507 : Nat := 118140960795 + 1346507 * 2 ^ 59
def prefixEnd_1346507 : Nat := 4983230072969 + 3 ^ 40 * 1346507 * 2
def baseEnd_1346507 : Nat := 691405295643668518870033

theorem tailTrace_1346507 : CollatzResearch.WordTrace tailWord_1346507 prefixEnd_1346507 691405295643668518870033 := by
  unfold tailWord_1346507
  simp only [CollatzResearch.WordTrace]
  refine ⟨49111144932842578932253775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32740763288561719288169183 49111144932842578932253775)
  ·
    refine ⟨73666717399263868398380663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49111144932842578932253775 73666717399263868398380663)
    ·
      refine ⟨110500076098895802597570995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73666717399263868398380663 110500076098895802597570995)
      ·
        refine ⟨165750114148343703896356493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110500076098895802597570995 165750114148343703896356493)
        ·
          refine ⟨62156292805628888961133685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165750114148343703896356493 62156292805628888961133685)
          ·
            refine ⟨5827152450527708340106283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62156292805628888961133685 5827152450527708340106283)
            ·
              refine ⟨8740728675791562510159425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5827152450527708340106283 8740728675791562510159425)
              ·
                refine ⟨6555546506843671882619569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8740728675791562510159425 6555546506843671882619569)
                ·
                  refine ⟨4916659880132753911964677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6555546506843671882619569 4916659880132753911964677)
                  ·
                    refine ⟨921873727524891358493377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4916659880132753911964677 921873727524891358493377)
                    ·
                      refine ⟨691405295643668518870033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 921873727524891358493377 691405295643668518870033)
                      ·
                        rfl

theorem cell23_1346507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 4, 2].length) (baseStart_1346507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346507 prefixEnd_1346507 := by exact prefixLift 1346507
  have htrace : WordTrace (prefixWord ++ tailWord_1346507) baseStart_1346507 baseEnd_1346507 := by
    simpa [prefixWord, tailWord_1346507, baseEnd_1346507] using wordTrace_append hprefix tailTrace_1346507
  have hstable : (prefixWord ++ tailWord_1346507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346507).length < 2 ^ (prefixWord ++ tailWord_1346507).sum := by decide
  have hdescent : baseEnd_1346507 < baseStart_1346507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346594 : List Nat := [3, 3, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_1346594 : Nat := 118140960795 + 1346594 * 2 ^ 59
def prefixEnd_1346594 : Nat := 4983230072969 + 3 ^ 40 * 1346594 * 2
def baseEnd_1346594 : Nat := 230483322820203226160711

theorem tailTrace_1346594 : CollatzResearch.WordTrace tailWord_1346594 prefixEnd_1346594 230483322820203226160711 := by
  unfold tailWord_1346594
  simp only [CollatzResearch.WordTrace]
  refine ⟨12278579520881848197667709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32742878722351595193780557 12278579520881848197667709)
  ·
    refine ⟨4604467320330693074125391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12278579520881848197667709 4604467320330693074125391)
    ·
      refine ⟨6906700980496039611188087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4604467320330693074125391 6906700980496039611188087)
      ·
        refine ⟨10360051470744059416782131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6906700980496039611188087 10360051470744059416782131)
        ·
          refine ⟨15540077206116089125173197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10360051470744059416782131 15540077206116089125173197)
          ·
            refine ⟨5827528952293533421939949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15540077206116089125173197 5827528952293533421939949)
            ·
              refine ⟨2185323357110075033227481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5827528952293533421939949 2185323357110075033227481)
              ·
                refine ⟨1638992517832556274920611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2185323357110075033227481 1638992517832556274920611)
                ·
                  refine ⟨2458488776748834412380917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1638992517832556274920611 2458488776748834412380917)
                  ·
                    refine ⟨230483322820203226160711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2458488776748834412380917 230483322820203226160711)
                    ·
                      rfl

theorem cell23_1346594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_1346594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346594 prefixEnd_1346594 := by exact prefixLift 1346594
  have htrace : WordTrace (prefixWord ++ tailWord_1346594) baseStart_1346594 baseEnd_1346594 := by
    simpa [prefixWord, tailWord_1346594, baseEnd_1346594] using wordTrace_append hprefix tailTrace_1346594
  have hstable : (prefixWord ++ tailWord_1346594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346594).length < 2 ^ (prefixWord ++ tailWord_1346594).sum := by decide
  have hdescent : baseEnd_1346594 < baseStart_1346594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346597 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_1346597 : Nat := 118140960795 + 1346597 * 2 ^ 59
def prefixEnd_1346597 : Nat := 4983230072969 + 3 ^ 40 * 1346597 * 2
def baseEnd_1346597 : Nat := 691451508902573166744619

theorem tailTrace_1346597 : CollatzResearch.WordTrace tailWord_1346597 prefixEnd_1346597 691451508902573166744619 := by
  unfold tailWord_1346597
  simp only [CollatzResearch.WordTrace]
  refine ⟨49114427502516524303030045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32742951668344349535353363 49114427502516524303030045)
  ·
    refine ⟨18417910313443696613636267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49114427502516524303030045 18417910313443696613636267)
    ·
      refine ⟨27626865470165544920454401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18417910313443696613636267 27626865470165544920454401)
      ·
        refine ⟨20720149102624158690340801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27626865470165544920454401 20720149102624158690340801)
        ·
          refine ⟨15540111826968119017755601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20720149102624158690340801 15540111826968119017755601)
          ·
            refine ⟨11655083870226089263316701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15540111826968119017755601 11655083870226089263316701)
            ·
              refine ⟨4370656451334783473743763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11655083870226089263316701 4370656451334783473743763)
              ·
                refine ⟨6555984677002175210615645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4370656451334783473743763 6555984677002175210615645)
                ·
                  refine ⟨2458494253875815703980867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6555984677002175210615645 2458494253875815703980867)
                  ·
                    refine ⟨3687741380813723555971301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2458494253875815703980867 3687741380813723555971301)
                    ·
                      refine ⟨691451508902573166744619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3687741380813723555971301 691451508902573166744619)
                      ·
                        rfl

theorem cell23_1346597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_1346597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346597 prefixEnd_1346597 := by exact prefixLift 1346597
  have htrace : WordTrace (prefixWord ++ tailWord_1346597) baseStart_1346597 baseEnd_1346597 := by
    simpa [prefixWord, tailWord_1346597, baseEnd_1346597] using wordTrace_append hprefix tailTrace_1346597
  have hstable : (prefixWord ++ tailWord_1346597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346597).length < 2 ^ (prefixWord ++ tailWord_1346597).sum := by decide
  have hdescent : baseEnd_1346597 < baseStart_1346597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346620 : List Nat := [2, 2, 2, 2, 2, 13]
def baseStart_1346620 : Nat := 118140960795 + 1346620 * 2 ^ 59
def prefixEnd_1346620 : Nat := 4983230072969 + 3 ^ 40 * 1346620 * 2
def baseEnd_1346620 : Nat := 2845528061554018834391

theorem tailTrace_1346620 : CollatzResearch.WordTrace tailWord_1346620 prefixEnd_1346620 2845528061554018834391 := by
  unfold tailWord_1346620
  simp only [CollatzResearch.WordTrace]
  refine ⟨24557633190716599615558657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32743510920955466154078209 24557633190716599615558657)
  ·
    refine ⟨18418224893037449711668993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24557633190716599615558657 18418224893037449711668993)
    ·
      refine ⟨13813668669778087283751745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18418224893037449711668993 13813668669778087283751745)
      ·
        refine ⟨10360251502333565462813809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13813668669778087283751745 10360251502333565462813809)
        ·
          refine ⟨7770188626750174097110357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10360251502333565462813809 7770188626750174097110357)
          ·
            refine ⟨2845528061554018834391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 7770188626750174097110357 2845528061554018834391)
            ·
              rfl

theorem cell23_1346620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 13].length) (baseStart_1346620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346620 prefixEnd_1346620 := by exact prefixLift 1346620
  have htrace : WordTrace (prefixWord ++ tailWord_1346620) baseStart_1346620 baseEnd_1346620 := by
    simpa [prefixWord, tailWord_1346620, baseEnd_1346620] using wordTrace_append hprefix tailTrace_1346620
  have hstable : (prefixWord ++ tailWord_1346620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346620).length < 2 ^ (prefixWord ++ tailWord_1346620).sum := by decide
  have hdescent : baseEnd_1346620 < baseStart_1346620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346624 : List Nat := [2, 1, 1, 2, 2, 3, 4, 2, 2, 4]
def baseStart_1346624 : Nat := 118140960795 + 1346624 * 2 ^ 59
def prefixEnd_1346624 : Nat := 4983230072969 + 3 ^ 40 * 1346624 * 2
def baseEnd_1346624 : Nat := 230488457626748187035665

theorem tailTrace_1346624 : CollatzResearch.WordTrace tailWord_1346624 prefixEnd_1346624 230488457626748187035665 := by
  unfold tailWord_1346624
  simp only [CollatzResearch.WordTrace]
  refine ⟨24557706136709353957131463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32743608182279138609508617 24557706136709353957131463)
  ·
    refine ⟨36836559205064030935697195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24557706136709353957131463 36836559205064030935697195)
    ·
      refine ⟨55254838807596046403545793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36836559205064030935697195 55254838807596046403545793)
      ·
        refine ⟨41441129105697034802659345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55254838807596046403545793 41441129105697034802659345)
        ·
          refine ⟨31080846829272776101994509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41441129105697034802659345 31080846829272776101994509)
          ·
            refine ⟨11655317560977291038247941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31080846829272776101994509 11655317560977291038247941)
            ·
              refine ⟨2185372042683242069671489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11655317560977291038247941 2185372042683242069671489)
              ·
                refine ⟨1639029032012431552253617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2185372042683242069671489 1639029032012431552253617)
                ·
                  refine ⟨1229271774009323664190213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1639029032012431552253617 1229271774009323664190213)
                  ·
                    refine ⟨230488457626748187035665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1229271774009323664190213 230488457626748187035665)
                    ·
                      rfl

theorem cell23_1346624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 2, 4].length) (baseStart_1346624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346624 prefixEnd_1346624 := by exact prefixLift 1346624
  have htrace : WordTrace (prefixWord ++ tailWord_1346624) baseStart_1346624 baseEnd_1346624 := by
    simpa [prefixWord, tailWord_1346624, baseEnd_1346624] using wordTrace_append hprefix tailTrace_1346624
  have hstable : (prefixWord ++ tailWord_1346624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346624).length < 2 ^ (prefixWord ++ tailWord_1346624).sum := by decide
  have hdescent : baseEnd_1346624 < baseStart_1346624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346640 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 6]
def baseStart_1346640 : Nat := 118140960795 + 1346640 * 2 ^ 59
def prefixEnd_1346640 : Nat := 4983230072969 + 3 ^ 40 * 1346640 * 2
def baseEnd_1346640 : Nat := 691473588570716498506921

theorem tailTrace_1346640 : CollatzResearch.WordTrace tailWord_1346640 prefixEnd_1346640 691473588570716498506921 := by
  unfold tailWord_1346640
  simp only [CollatzResearch.WordTrace]
  refine ⟨24557997920680371323422687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32743997227573828431230249 24557997920680371323422687)
  ·
    refine ⟨36836996881020556985134031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24557997920680371323422687 36836996881020556985134031)
    ·
      refine ⟨55255495321530835477701047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36836996881020556985134031 55255495321530835477701047)
      ·
        refine ⟨82883242982296253216551571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55255495321530835477701047 82883242982296253216551571)
        ·
          refine ⟨124324864473444379824827357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82883242982296253216551571 124324864473444379824827357)
          ·
            refine ⟨46621824177541642434310259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124324864473444379824827357 46621824177541642434310259)
            ·
              refine ⟨69932736266312463651465389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46621824177541642434310259 69932736266312463651465389)
              ·
                refine ⟨26224776099867173869299521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69932736266312463651465389 26224776099867173869299521)
                ·
                  refine ⟨19668582074900380401974641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26224776099867173869299521 19668582074900380401974641)
                  ·
                    refine ⟨14751436556175285301480981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19668582074900380401974641 14751436556175285301480981)
                    ·
                      refine ⟨691473588570716498506921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14751436556175285301480981 691473588570716498506921)
                      ·
                        rfl

theorem cell23_1346640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_1346640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346640 prefixEnd_1346640 := by exact prefixLift 1346640
  have htrace : WordTrace (prefixWord ++ tailWord_1346640) baseStart_1346640 baseEnd_1346640 := by
    simpa [prefixWord, tailWord_1346640, baseEnd_1346640] using wordTrace_append hprefix tailTrace_1346640
  have hstable : (prefixWord ++ tailWord_1346640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346640).length < 2 ^ (prefixWord ++ tailWord_1346640).sum := by decide
  have hdescent : baseEnd_1346640 < baseStart_1346640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346681 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 4, 1, 3]
def baseStart_1346681 : Nat := 118140960795 + 1346681 * 2 ^ 59
def prefixEnd_1346681 : Nat := 4983230072969 + 3 ^ 40 * 1346681 * 2
def baseEnd_1346681 : Nat := 691494641277550838094233

theorem tailTrace_1346681 : CollatzResearch.WordTrace tailWord_1346681 prefixEnd_1346681 691494641277550838094233 := by
  unfold tailWord_1346681
  simp only [CollatzResearch.WordTrace]
  refine ⟨49117491234212206649087897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32744994156141471099391931 49117491234212206649087897)
  ·
    refine ⟨36838118425659154986815923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49117491234212206649087897 36838118425659154986815923)
    ·
      refine ⟨55257177638488732480223885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36838118425659154986815923 55257177638488732480223885)
      ·
        refine ⟨20721441614433274680083957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55257177638488732480223885 20721441614433274680083957)
        ·
          refine ⟨1942635151353119501257871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20721441614433274680083957 1942635151353119501257871)
          ·
            refine ⟨2913952727029679251886807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1942635151353119501257871 2913952727029679251886807)
            ·
              refine ⟨4370929090544518877830211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913952727029679251886807 4370929090544518877830211)
              ·
                refine ⟨6556393635816778316745317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4370929090544518877830211 6556393635816778316745317)
                ·
                  refine ⟨1229323806715645934389747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6556393635816778316745317 1229323806715645934389747)
                  ·
                    refine ⟨1843985710073468901584621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1229323806715645934389747 1843985710073468901584621)
                    ·
                      refine ⟨691494641277550838094233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1843985710073468901584621 691494641277550838094233)
                      ·
                        rfl

theorem cell23_1346681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_1346681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346681 prefixEnd_1346681 := by exact prefixLift 1346681
  have htrace : WordTrace (prefixWord ++ tailWord_1346681) baseStart_1346681 baseEnd_1346681 := by
    simpa [prefixWord, tailWord_1346681, baseEnd_1346681] using wordTrace_append hprefix tailTrace_1346681
  have hstable : (prefixWord ++ tailWord_1346681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346681).length < 2 ^ (prefixWord ++ tailWord_1346681).sum := by decide
  have hdescent : baseEnd_1346681 < baseStart_1346681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346697 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 2, 6]
def baseStart_1346697 : Nat := 118140960795 + 1346697 * 2 ^ 59
def prefixEnd_1346697 : Nat := 4983230072969 + 3 ^ 40 * 1346697 * 2
def baseEnd_1346697 : Nat := 230500952322674258498053

theorem tailTrace_1346697 : CollatzResearch.WordTrace tailWord_1346697 prefixEnd_1346697 230500952322674258498053 := by
  unfold tailWord_1346697
  simp only [CollatzResearch.WordTrace]
  refine ⟨49118074802154241381670345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32745383201436160921113563 49118074802154241381670345)
  ·
    refine ⟨36838556101615681036252759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49118074802154241381670345 36838556101615681036252759)
    ·
      refine ⟨55257834152423521554379139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36838556101615681036252759 55257834152423521554379139)
      ·
        refine ⟨82886751228635282331568709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55257834152423521554379139 82886751228635282331568709)
        ·
          refine ⟨15541265855369115437169133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82886751228635282331568709 15541265855369115437169133)
          ·
            refine ⟨5827974695763418288938425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15541265855369115437169133 5827974695763418288938425)
            ·
              refine ⟨4370981021822563716703819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5827974695763418288938425 4370981021822563716703819)
              ·
                refine ⟨6556471532733845575055729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4370981021822563716703819 6556471532733845575055729)
                ·
                  refine ⟨4917353649550384181291797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6556471532733845575055729 4917353649550384181291797)
                  ·
                    refine ⟨230500952322674258498053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4917353649550384181291797 230500952322674258498053)
                    ·
                      rfl

theorem cell23_1346697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_1346697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346697 prefixEnd_1346697 := by exact prefixLift 1346697
  have htrace : WordTrace (prefixWord ++ tailWord_1346697) baseStart_1346697 baseEnd_1346697 := by
    simpa [prefixWord, tailWord_1346697, baseEnd_1346697] using wordTrace_append hprefix tailTrace_1346697
  have hstable : (prefixWord ++ tailWord_1346697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346697).length < 2 ^ (prefixWord ++ tailWord_1346697).sum := by decide
  have hdescent : baseEnd_1346697 < baseStart_1346697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346698 : List Nat := [3, 1, 2, 3, 1, 1, 5, 1, 2, 1, 3]
def baseStart_1346698 : Nat := 118140960795 + 1346698 * 2 ^ 59
def prefixEnd_1346698 : Nat := 4983230072969 + 3 ^ 40 * 1346698 * 2
def baseEnd_1346698 : Nat := 691503370448677271581655

theorem tailTrace_1346698 : CollatzResearch.WordTrace tailWord_1346698 prefixEnd_1346698 691503370448677271581655 := by
  unfold tailWord_1346698
  simp only [CollatzResearch.WordTrace]
  refine ⟨12279527818787654638114187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32745407516767079034971165 12279527818787654638114187)
  ·
    refine ⟨18419291728181481957171281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12279527818787654638114187 18419291728181481957171281)
    ·
      refine ⟨13814468796136111467878461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18419291728181481957171281 13814468796136111467878461)
      ·
        refine ⟨5180425798551041800454423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13814468796136111467878461 5180425798551041800454423)
        ·
          refine ⟨7770638697826562700681635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5180425798551041800454423 7770638697826562700681635)
          ·
            refine ⟨11655958046739844051022453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7770638697826562700681635 11655958046739844051022453)
            ·
              refine ⟨1092746066881860379783355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11655958046739844051022453 1092746066881860379783355)
              ·
                refine ⟨1639119100322790569675033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1092746066881860379783355 1639119100322790569675033)
                ·
                  refine ⟨1229339325242092927256275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1639119100322790569675033 1229339325242092927256275)
                  ·
                    refine ⟨1844008987863139390884413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1229339325242092927256275 1844008987863139390884413)
                    ·
                      refine ⟨691503370448677271581655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1844008987863139390884413 691503370448677271581655)
                      ·
                        rfl

theorem cell23_1346698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_1346698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346698 prefixEnd_1346698 := by exact prefixLift 1346698
  have htrace : WordTrace (prefixWord ++ tailWord_1346698) baseStart_1346698 baseEnd_1346698 := by
    simpa [prefixWord, tailWord_1346698, baseEnd_1346698] using wordTrace_append hprefix tailTrace_1346698
  have hstable : (prefixWord ++ tailWord_1346698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346698).length < 2 ^ (prefixWord ++ tailWord_1346698).sum := by decide
  have hdescent : baseEnd_1346698 < baseStart_1346698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346704 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 1, 4, 2]
def baseStart_1346704 : Nat := 118140960795 + 1346704 * 2 ^ 59
def prefixEnd_1346704 : Nat := 4983230072969 + 3 ^ 40 * 1346704 * 2
def baseEnd_1346704 : Nat := 691506451332604248106627

theorem tailTrace_1346704 : CollatzResearch.WordTrace tailWord_1346704 prefixEnd_1346704 691506451332604248106627 := by
  unfold tailWord_1346704
  simp only [CollatzResearch.WordTrace]
  refine ⟨24559165056564440788587583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32745553408752587718116777 24559165056564440788587583)
  ·
    refine ⟨36838747584846661182881375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24559165056564440788587583 36838747584846661182881375)
    ·
      refine ⟨55258121377269991774322063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36838747584846661182881375 55258121377269991774322063)
      ·
        refine ⟨82887182065904987661483095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55258121377269991774322063 82887182065904987661483095)
        ·
          refine ⟨124330773098857481492224643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82887182065904987661483095 124330773098857481492224643)
          ·
            refine ⟨186496159648286222238336965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124330773098857481492224643 186496159648286222238336965)
            ·
              refine ⟨34968029934053666669688181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186496159648286222238336965 34968029934053666669688181)
              ·
                refine ⟨3278252806317531250283267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34968029934053666669688181 3278252806317531250283267)
                ·
                  refine ⟨4917379209476296875424901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3278252806317531250283267 4917379209476296875424901)
                  ·
                    refine ⟨922008601776805664142169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4917379209476296875424901 922008601776805664142169)
                    ·
                      refine ⟨691506451332604248106627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922008601776805664142169 691506451332604248106627)
                      ·
                        rfl

theorem cell23_1346704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 4, 2].length) (baseStart_1346704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346704 prefixEnd_1346704 := by exact prefixLift 1346704
  have htrace : WordTrace (prefixWord ++ tailWord_1346704) baseStart_1346704 baseEnd_1346704 := by
    simpa [prefixWord, tailWord_1346704, baseEnd_1346704] using wordTrace_append hprefix tailTrace_1346704
  have hstable : (prefixWord ++ tailWord_1346704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346704).length < 2 ^ (prefixWord ++ tailWord_1346704).sum := by decide
  have hdescent : baseEnd_1346704 < baseStart_1346704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346707 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 3]
def baseStart_1346707 : Nat := 118140960795 + 1346707 * 2 ^ 59
def prefixEnd_1346707 : Nat := 4983230072969 + 3 ^ 40 * 1346707 * 2
def baseEnd_1346707 : Nat := 691507991774567736369113

theorem tailTrace_1346707 : CollatzResearch.WordTrace tailWord_1346707 prefixEnd_1346707 691507991774567736369113 := by
  unfold tailWord_1346707
  simp only [CollatzResearch.WordTrace]
  refine ⟨49118439532118013089534375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32745626354745342059689583 49118439532118013089534375)
  ·
    refine ⟨73677659298177019634301563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49118439532118013089534375 73677659298177019634301563)
    ·
      refine ⟨110516488947265529451452345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73677659298177019634301563 110516488947265529451452345)
      ·
        refine ⟨82887366710449147088589259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110516488947265529451452345 82887366710449147088589259)
        ·
          refine ⟨124331050065673720632883889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82887366710449147088589259 124331050065673720632883889)
          ·
            refine ⟨93248287549255290474662917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124331050065673720632883889 93248287549255290474662917)
            ·
              refine ⟨17484053915485366963999297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93248287549255290474662917 17484053915485366963999297)
              ·
                refine ⟨13113040436614025222999473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17484053915485366963999297 13113040436614025222999473)
                ·
                  refine ⟨9834780327460518917249605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13113040436614025222999473 9834780327460518917249605)
                  ·
                    refine ⟨1844021311398847296984301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9834780327460518917249605 1844021311398847296984301)
                    ·
                      refine ⟨691507991774567736369113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1844021311398847296984301 691507991774567736369113)
                      ·
                        rfl

theorem cell23_1346707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 3].length) (baseStart_1346707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346707 prefixEnd_1346707 := by exact prefixLift 1346707
  have htrace : WordTrace (prefixWord ++ tailWord_1346707) baseStart_1346707 baseEnd_1346707 := by
    simpa [prefixWord, tailWord_1346707, baseEnd_1346707] using wordTrace_append hprefix tailTrace_1346707
  have hstable : (prefixWord ++ tailWord_1346707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346707).length < 2 ^ (prefixWord ++ tailWord_1346707).sum := by decide
  have hdescent : baseEnd_1346707 < baseStart_1346707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346721 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 6, 2, 2]
def baseStart_1346721 : Nat := 118140960795 + 1346721 * 2 ^ 59
def prefixEnd_1346721 : Nat := 4983230072969 + 3 ^ 40 * 1346721 * 2
def baseEnd_1346721 : Nat := 691515180503730681594049

theorem tailTrace_1346721 : CollatzResearch.WordTrace tailWord_1346721 prefixEnd_1346721 691515180503730681594049 := by
  unfold tailWord_1346721
  simp only [CollatzResearch.WordTrace]
  refine ⟨49118950154067293480544017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32745966769378195653696011 49118950154067293480544017)
  ·
    refine ⟨36839212615550470110408013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49118950154067293480544017 36839212615550470110408013)
    ·
      refine ⟨13814704730831426291403005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36839212615550470110408013 13814704730831426291403005)
      ·
        refine ⟨5180514274061784859276127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13814704730831426291403005 5180514274061784859276127)
        ·
          refine ⟨7770771411092677288914191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5180514274061784859276127 7770771411092677288914191)
          ·
            refine ⟨11656157116639015933371287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7770771411092677288914191 11656157116639015933371287)
            ·
              refine ⟨17484235674958523900056931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11656157116639015933371287 17484235674958523900056931)
              ·
                refine ⟨26226353512437785850085397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17484235674958523900056931 26226353512437785850085397)
                ·
                  refine ⟨1229360320895521211722753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26226353512437785850085397 1229360320895521211722753)
                  ·
                    refine ⟨922020240671640908792065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1229360320895521211722753 922020240671640908792065)
                    ·
                      refine ⟨691515180503730681594049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922020240671640908792065 691515180503730681594049)
                      ·
                        rfl

theorem cell23_1346721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_1346721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346721 prefixEnd_1346721 := by exact prefixLift 1346721
  have htrace : WordTrace (prefixWord ++ tailWord_1346721) baseStart_1346721 baseEnd_1346721 := by
    simpa [prefixWord, tailWord_1346721, baseEnd_1346721] using wordTrace_append hprefix tailTrace_1346721
  have hstable : (prefixWord ++ tailWord_1346721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346721).length < 2 ^ (prefixWord ++ tailWord_1346721).sum := by decide
  have hdescent : baseEnd_1346721 < baseStart_1346721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346724 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_1346724 : Nat := 118140960795 + 1346724 * 2 ^ 59
def prefixEnd_1346724 : Nat := 4983230072969 + 3 ^ 40 * 1346724 * 2
def baseEnd_1346724 : Nat := 691516720945694169856535

theorem tailTrace_1346724 : CollatzResearch.WordTrace tailWord_1346724 prefixEnd_1346724 691516720945694169856535 := by
  unfold tailWord_1346724
  simp only [CollatzResearch.WordTrace]
  refine ⟨24559529786528212496451613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32746039715370949995268817 24559529786528212496451613)
  ·
    refine ⟨9209823669948079686169355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24559529786528212496451613 9209823669948079686169355)
    ·
      refine ⟨13814735504922119529254033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9209823669948079686169355 13814735504922119529254033)
      ·
        refine ⟨10361051628691589646940525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13814735504922119529254033 10361051628691589646940525)
        ·
          refine ⟨3885394360759346117602697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10361051628691589646940525 3885394360759346117602697)
          ·
            refine ⟨2914045770569509588202023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3885394360759346117602697 2914045770569509588202023)
            ·
              refine ⟨4371068655854264382303035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2914045770569509588202023 4371068655854264382303035)
              ·
                refine ⟨6556602983781396573454553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4371068655854264382303035 6556602983781396573454553)
                ·
                  refine ⟨4917452237836047430090915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6556602983781396573454553 4917452237836047430090915)
                  ·
                    refine ⟨7376178356754071145136373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4917452237836047430090915 7376178356754071145136373)
                    ·
                      refine ⟨691516720945694169856535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7376178356754071145136373 691516720945694169856535)
                      ·
                        rfl

theorem cell23_1346724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_1346724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346724 prefixEnd_1346724 := by exact prefixLift 1346724
  have htrace : WordTrace (prefixWord ++ tailWord_1346724) baseStart_1346724 baseEnd_1346724 := by
    simpa [prefixWord, tailWord_1346724, baseEnd_1346724] using wordTrace_append hprefix tailTrace_1346724
  have hstable : (prefixWord ++ tailWord_1346724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346724).length < 2 ^ (prefixWord ++ tailWord_1346724).sum := by decide
  have hdescent : baseEnd_1346724 < baseStart_1346724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346757 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 6, 5]
def baseStart_1346757 : Nat := 118140960795 + 1346757 * 2 ^ 59
def prefixEnd_1346757 : Nat := 4983230072969 + 3 ^ 40 * 1346757 * 2
def baseEnd_1346757 : Nat := 230511221935764180247961

theorem tailTrace_1346757 : CollatzResearch.WordTrace tailWord_1346757 prefixEnd_1346757 230511221935764180247961 := by
  unfold tailWord_1346757
  simp only [CollatzResearch.WordTrace]
  refine ⟨49120263181936871628854525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32746842121291247752569683 49120263181936871628854525)
  ·
    refine ⟨18420098693226326860820447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49120263181936871628854525 18420098693226326860820447)
    ·
      refine ⟨27630148039839490291230671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18420098693226326860820447 27630148039839490291230671)
      ·
        refine ⟨41445222059759235436846007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27630148039839490291230671 41445222059759235436846007)
        ·
          refine ⟨62167833089638853155269011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41445222059759235436846007 62167833089638853155269011)
          ·
            refine ⟨93251749634458279732903517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62167833089638853155269011 93251749634458279732903517)
            ·
              refine ⟨34969406112921854899838819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93251749634458279732903517 34969406112921854899838819)
              ·
                refine ⟨52454109169382782349758229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34969406112921854899838819 52454109169382782349758229)
                ·
                  refine ⟨2458786367314817922644917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52454109169382782349758229 2458786367314817922644917)
                  ·
                    refine ⟨230511221935764180247961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2458786367314817922644917 230511221935764180247961)
                    ·
                      rfl

theorem cell23_1346757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_1346757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346757 prefixEnd_1346757 := by exact prefixLift 1346757
  have htrace : WordTrace (prefixWord ++ tailWord_1346757) baseStart_1346757 baseEnd_1346757 := by
    simpa [prefixWord, tailWord_1346757, baseEnd_1346757] using wordTrace_append hprefix tailTrace_1346757
  have hstable : (prefixWord ++ tailWord_1346757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346757).length < 2 ^ (prefixWord ++ tailWord_1346757).sum := by decide
  have hdescent : baseEnd_1346757 < baseStart_1346757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346807 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_1346807 : Nat := 118140960795 + 1346807 * 2 ^ 59
def prefixEnd_1346807 : Nat := 4983230072969 + 3 ^ 40 * 1346807 * 2
def baseEnd_1346807 : Nat := 691559339840017345118653

theorem tailTrace_1346807 : CollatzResearch.WordTrace tailWord_1346807 prefixEnd_1346807 691559339840017345118653 := by
  unfold tailWord_1346807
  simp only [CollatzResearch.WordTrace]
  refine ⟨49122086831755730168174675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32748057887837153445449783 49122086831755730168174675)
  ·
    refine ⟨73683130247633595252262013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49122086831755730168174675 73683130247633595252262013)
    ·
      refine ⟨27631173842862598219598255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73683130247633595252262013 27631173842862598219598255)
      ·
        refine ⟨41446760764293897329397383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27631173842862598219598255 41446760764293897329397383)
        ·
          refine ⟨62170141146440845994096075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41446760764293897329397383 62170141146440845994096075)
          ·
            refine ⟨93255211719661268991144113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62170141146440845994096075 93255211719661268991144113)
            ·
              refine ⟨69941408789745951743358085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93255211719661268991144113 69941408789745951743358085)
              ·
                refine ⟨13114014148077365951879641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69941408789745951743358085 13114014148077365951879641)
                ·
                  refine ⟨9835510611058024463909731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13114014148077365951879641 9835510611058024463909731)
                  ·
                    refine ⟨14753265916587036695864597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9835510611058024463909731 14753265916587036695864597)
                    ·
                      refine ⟨691559339840017345118653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14753265916587036695864597 691559339840017345118653)
                      ·
                        rfl

theorem cell23_1346807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_1346807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346807 prefixEnd_1346807 := by exact prefixLift 1346807
  have htrace : WordTrace (prefixWord ++ tailWord_1346807) baseStart_1346807 baseEnd_1346807 := by
    simpa [prefixWord, tailWord_1346807, baseEnd_1346807] using wordTrace_append hprefix tailTrace_1346807
  have hstable : (prefixWord ++ tailWord_1346807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346807).length < 2 ^ (prefixWord ++ tailWord_1346807).sum := by decide
  have hdescent : baseEnd_1346807 < baseStart_1346807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346851 : List Nat := [1, 1, 1, 4, 2, 5, 1, 2, 6]
def baseStart_1346851 : Nat := 118140960795 + 1346851 * 2 ^ 59
def prefixEnd_1346851 : Nat := 4983230072969 + 3 ^ 40 * 1346851 * 2
def baseEnd_1346851 : Nat := 76842436998757241440939

theorem tailTrace_1346851 : CollatzResearch.WordTrace tailWord_1346851 prefixEnd_1346851 76842436998757241440939 := by
  unfold tailWord_1346851
  simp only [CollatzResearch.WordTrace]
  refine ⟨49123691643596325682776407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32749127762397550455184271 49123691643596325682776407)
  ·
    refine ⟨73685537465394488524164611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49123691643596325682776407 73685537465394488524164611)
    ·
      refine ⟨110528306198091732786246917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73685537465394488524164611 110528306198091732786246917)
      ·
        refine ⟨20724057412142199897421297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110528306198091732786246917 20724057412142199897421297)
        ·
          refine ⟨15543043059106649923065973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20724057412142199897421297 15543043059106649923065973)
          ·
            refine ⟨1457160286791248430287435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15543043059106649923065973 1457160286791248430287435)
            ·
              refine ⟨2185740430186872645431153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457160286791248430287435 2185740430186872645431153)
              ·
                refine ⟨1639305322640154484073365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2185740430186872645431153 1639305322640154484073365)
                ·
                  refine ⟨76842436998757241440939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1639305322640154484073365 76842436998757241440939)
                  ·
                    rfl

theorem cell23_1346851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 6].length) (baseStart_1346851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346851 prefixEnd_1346851 := by exact prefixLift 1346851
  have htrace : WordTrace (prefixWord ++ tailWord_1346851) baseStart_1346851 baseEnd_1346851 := by
    simpa [prefixWord, tailWord_1346851, baseEnd_1346851] using wordTrace_append hprefix tailTrace_1346851
  have hstable : (prefixWord ++ tailWord_1346851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346851).length < 2 ^ (prefixWord ++ tailWord_1346851).sum := by decide
  have hdescent : baseEnd_1346851 < baseStart_1346851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346857 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 7]
def baseStart_1346857 : Nat := 118140960795 + 1346857 * 2 ^ 59
def prefixEnd_1346857 : Nat := 4983230072969 + 3 ^ 40 * 1346857 * 2
def baseEnd_1346857 : Nat := 691585013872742149493423

theorem tailTrace_1346857 : CollatzResearch.WordTrace tailWord_1346857 prefixEnd_1346857 691585013872742149493423 := by
  unfold tailWord_1346857
  simp only [CollatzResearch.WordTrace]
  refine ⟨49123910481574588707494825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32749273654383059138329883 49123910481574588707494825)
  ·
    refine ⟨36842932861180941530621119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49123910481574588707494825 36842932861180941530621119)
    ·
      refine ⟨55264399291771412295931679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36842932861180941530621119 55264399291771412295931679)
      ·
        refine ⟨82896598937657118443897519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55264399291771412295931679 82896598937657118443897519)
        ·
          refine ⟨124344898406485677665846279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82896598937657118443897519 124344898406485677665846279)
          ·
            refine ⟨186517347609728516498769419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124344898406485677665846279 186517347609728516498769419)
            ·
              refine ⟨279776021414592774748154129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186517347609728516498769419 279776021414592774748154129)
              ·
                refine ⟨209832016060944581061115597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279776021414592774748154129 209832016060944581061115597)
                ·
                  refine ⟨78687006022854217897918349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209832016060944581061115597 78687006022854217897918349)
                  ·
                    refine ⟨29507627258570331711719381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78687006022854217897918349 29507627258570331711719381)
                    ·
                      refine ⟨691585013872742149493423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29507627258570331711719381 691585013872742149493423)
                      ·
                        rfl

theorem cell23_1346857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_1346857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346857 prefixEnd_1346857 := by exact prefixLift 1346857
  have htrace : WordTrace (prefixWord ++ tailWord_1346857) baseStart_1346857 baseEnd_1346857 := by
    simpa [prefixWord, tailWord_1346857, baseEnd_1346857] using wordTrace_append hprefix tailTrace_1346857
  have hstable : (prefixWord ++ tailWord_1346857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346857).length < 2 ^ (prefixWord ++ tailWord_1346857).sum := by decide
  have hdescent : baseEnd_1346857 < baseStart_1346857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346868 : List Nat := [2, 5, 1, 1, 1, 1, 5, 1, 6]
def baseStart_1346868 : Nat := 118140960795 + 1346868 * 2 ^ 59
def prefixEnd_1346868 : Nat := 4983230072969 + 3 ^ 40 * 1346868 * 2
def baseEnd_1346868 : Nat := 76843406906660178495097

theorem tailTrace_1346868 : CollatzResearch.WordTrace tailWord_1346868 prefixEnd_1346868 76843406906660178495097 := by
  unfold tailWord_1346868
  simp only [CollatzResearch.WordTrace]
  refine ⟨24562155842267368793072629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32749541123023158390763505 24562155842267368793072629)
  ·
    refine ⟨2302702110212565824350559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24562155842267368793072629 2302702110212565824350559)
    ·
      refine ⟨3454053165318848736525839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2302702110212565824350559 3454053165318848736525839)
      ·
        refine ⟨5181079747978273104788759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3454053165318848736525839 5181079747978273104788759)
        ·
          refine ⟨7771619621967409657183139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5181079747978273104788759 7771619621967409657183139)
          ·
            refine ⟨11657429432951114485774709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7771619621967409657183139 11657429432951114485774709)
            ·
              refine ⟨1092884009339166983041379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11657429432951114485774709 1092884009339166983041379)
              ·
                refine ⟨1639326014008750474562069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1092884009339166983041379 1639326014008750474562069)
                ·
                  refine ⟨76843406906660178495097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1639326014008750474562069 76843406906660178495097)
                  ·
                    rfl

theorem cell23_1346868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_1346868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346868 prefixEnd_1346868 := by exact prefixLift 1346868
  have htrace : WordTrace (prefixWord ++ tailWord_1346868) baseStart_1346868 baseEnd_1346868 := by
    simpa [prefixWord, tailWord_1346868, baseEnd_1346868] using wordTrace_append hprefix tailTrace_1346868
  have hstable : (prefixWord ++ tailWord_1346868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346868).length < 2 ^ (prefixWord ++ tailWord_1346868).sum := by decide
  have hdescent : baseEnd_1346868 < baseStart_1346868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346878 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_1346878 : Nat := 118140960795 + 1346878 * 2 ^ 59
def prefixEnd_1346878 : Nat := 4983230072969 + 3 ^ 40 * 1346878 * 2
def baseEnd_1346878 : Nat := 691595796966486567330827

theorem tailTrace_1346878 : CollatzResearch.WordTrace tailWord_1346878 prefixEnd_1346878 691595796966486567330827 := by
  unfold tailWord_1346878
  simp only [CollatzResearch.WordTrace]
  refine ⟨6140584551812313661751161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32749784276332339529339525 6140584551812313661751161)
  ·
    refine ⟨4605438413859235246313371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6140584551812313661751161 4605438413859235246313371)
    ·
      refine ⟨6908157620788852869470057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4605438413859235246313371 6908157620788852869470057)
      ·
        refine ⟨5181118215591639652102543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6908157620788852869470057 5181118215591639652102543)
        ·
          refine ⟨7771677323387459478153815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5181118215591639652102543 7771677323387459478153815)
          ·
            refine ⟨11657515985081189217230723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7771677323387459478153815 11657515985081189217230723)
            ·
              refine ⟨17486273977621783825846085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11657515985081189217230723 17486273977621783825846085)
              ·
                refine ⟨3278676370804084467346141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17486273977621783825846085 3278676370804084467346141)
                ·
                  refine ⟨1229503639051531675254803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3278676370804084467346141 1229503639051531675254803)
                  ·
                    refine ⟨1844255458577297512882205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1229503639051531675254803 1844255458577297512882205)
                    ·
                      refine ⟨691595796966486567330827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1844255458577297512882205 691595796966486567330827)
                      ·
                        rfl

theorem cell23_1346878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_1346878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346878 prefixEnd_1346878 := by exact prefixLift 1346878
  have htrace : WordTrace (prefixWord ++ tailWord_1346878) baseStart_1346878 baseEnd_1346878 := by
    simpa [prefixWord, tailWord_1346878, baseEnd_1346878] using wordTrace_append hprefix tailTrace_1346878
  have hstable : (prefixWord ++ tailWord_1346878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346878).length < 2 ^ (prefixWord ++ tailWord_1346878).sum := by decide
  have hdescent : baseEnd_1346878 < baseStart_1346878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346894 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_1346894 : Nat := 118140960795 + 1346894 * 2 ^ 59
def prefixEnd_1346894 : Nat := 4983230072969 + 3 ^ 40 * 1346894 * 2
def baseEnd_1346894 : Nat := 230534670885652834910251

theorem tailTrace_1346894 : CollatzResearch.WordTrace tailWord_1346894 prefixEnd_1346894 230534670885652834910251 := by
  unfold tailWord_1346894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6140657497805068003323967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32750173321627029351061157 6140657497805068003323967)
  ·
    refine ⟨9210986246707602004985951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6140657497805068003323967 9210986246707602004985951)
    ·
      refine ⟨13816479370061403007478927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9210986246707602004985951 13816479370061403007478927)
      ·
        refine ⟨20724719055092104511218391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13816479370061403007478927 20724719055092104511218391)
        ·
          refine ⟨31087078582638156766827587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20724719055092104511218391 31087078582638156766827587)
          ·
            refine ⟨46630617873957235150241381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31087078582638156766827587 46630617873957235150241381)
            ·
              refine ⟨8743240851366981590670259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46630617873957235150241381 8743240851366981590670259)
              ·
                refine ⟨13114861277050472386005389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8743240851366981590670259 13114861277050472386005389)
                ·
                  refine ⟨4918072978893927144752021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13114861277050472386005389 4918072978893927144752021)
                  ·
                    refine ⟨230534670885652834910251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4918072978893927144752021 230534670885652834910251)
                    ·
                      rfl

theorem cell23_1346894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_1346894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346894 prefixEnd_1346894 := by exact prefixLift 1346894
  have htrace : WordTrace (prefixWord ++ tailWord_1346894) baseStart_1346894 baseEnd_1346894 := by
    simpa [prefixWord, tailWord_1346894, baseEnd_1346894] using wordTrace_append hprefix tailTrace_1346894
  have hstable : (prefixWord ++ tailWord_1346894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346894).length < 2 ^ (prefixWord ++ tailWord_1346894).sum := by decide
  have hdescent : baseEnd_1346894 < baseStart_1346894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346911 : List Nat := [1, 1, 2, 3, 1, 2, 1, 6, 2, 4]
def baseStart_1346911 : Nat := 118140960795 + 1346911 * 2 ^ 59
def prefixEnd_1346911 : Nat := 4983230072969 + 3 ^ 40 * 1346911 * 2
def baseEnd_1346911 : Nat := 230537580609361646072725

theorem tailTrace_1346911 : CollatzResearch.WordTrace tailWord_1346911 prefixEnd_1346911 230537580609361646072725 := by
  unfold tailWord_1346911
  simp only [CollatzResearch.WordTrace]
  refine ⟨49125880023378955929960587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32750586682252637286640391 49125880023378955929960587)
  ·
    refine ⟨73688820035068433894940881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49125880023378955929960587 73688820035068433894940881)
    ·
      refine ⟨55266615026301325421205661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73688820035068433894940881 55266615026301325421205661)
      ·
        refine ⟨20724980634862997032952123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55266615026301325421205661 20724980634862997032952123)
        ·
          refine ⟨31087470952294495549428185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20724980634862997032952123 31087470952294495549428185)
          ·
            refine ⟨23315603214220871662071139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31087470952294495549428185 23315603214220871662071139)
            ·
              refine ⟨34973404821331307493106709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23315603214220871662071139 34973404821331307493106709)
              ·
                refine ⟨1639378350999905038739377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34973404821331307493106709 1639378350999905038739377)
                ·
                  refine ⟨1229533763249928779054533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1639378350999905038739377 1229533763249928779054533)
                  ·
                    refine ⟨230537580609361646072725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1229533763249928779054533 230537580609361646072725)
                    ·
                      rfl

theorem cell23_1346911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 4].length) (baseStart_1346911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346911 prefixEnd_1346911 := by exact prefixLift 1346911
  have htrace : WordTrace (prefixWord ++ tailWord_1346911) baseStart_1346911 baseEnd_1346911 := by
    simpa [prefixWord, tailWord_1346911, baseEnd_1346911] using wordTrace_append hprefix tailTrace_1346911
  have hstable : (prefixWord ++ tailWord_1346911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346911).length < 2 ^ (prefixWord ++ tailWord_1346911).sum := by decide
  have hdescent : baseEnd_1346911 < baseStart_1346911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346912 : List Nat := [2, 1, 1, 3, 4, 2, 3, 2, 1, 1, 3]
def baseStart_1346912 : Nat := 118140960795 + 1346912 * 2 ^ 59
def prefixEnd_1346912 : Nat := 4983230072969 + 3 ^ 40 * 1346912 * 2
def baseEnd_1346912 : Nat := 691613255308739434305671

theorem tailTrace_1346912 : CollatzResearch.WordTrace tailWord_1346912 prefixEnd_1346912 691613255308739434305671 := by
  unfold tailWord_1346912
  simp only [CollatzResearch.WordTrace]
  refine ⟨24562958248187666550373495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32750610997583555400497993 24562958248187666550373495)
  ·
    refine ⟨36844437372281499825560243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24562958248187666550373495 36844437372281499825560243)
    ·
      refine ⟨55266656058422249738340365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36844437372281499825560243 55266656058422249738340365)
      ·
        refine ⟨20724996021908343651877637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55266656058422249738340365 20724996021908343651877637)
        ·
          refine ⟨3885936754107814434727057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20724996021908343651877637 3885936754107814434727057)
          ·
            refine ⟨2914452565580860826045293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3885936754107814434727057 2914452565580860826045293)
            ·
              refine ⟨1092919712092822809766985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2914452565580860826045293 1092919712092822809766985)
              ·
                refine ⟨819689784069617107325239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1092919712092822809766985 819689784069617107325239)
                ·
                  refine ⟨1229534676104425660987859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 819689784069617107325239 1229534676104425660987859)
                  ·
                    refine ⟨1844302014156638491481789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1229534676104425660987859 1844302014156638491481789)
                    ·
                      refine ⟨691613255308739434305671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1844302014156638491481789 691613255308739434305671)
                      ·
                        rfl

theorem cell23_1346912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_1346912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346912 prefixEnd_1346912 := by exact prefixLift 1346912
  have htrace : WordTrace (prefixWord ++ tailWord_1346912) baseStart_1346912 baseEnd_1346912 := by
    simpa [prefixWord, tailWord_1346912, baseEnd_1346912] using wordTrace_append hprefix tailTrace_1346912
  have hstable : (prefixWord ++ tailWord_1346912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346912).length < 2 ^ (prefixWord ++ tailWord_1346912).sum := by decide
  have hdescent : baseEnd_1346912 < baseStart_1346912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346924 : List Nat := [2, 2, 1, 1, 5, 1, 1, 10]
def baseStart_1346924 : Nat := 118140960795 + 1346924 * 2 ^ 59
def prefixEnd_1346924 : Nat := 4983230072969 + 3 ^ 40 * 1346924 * 2
def baseEnd_1346924 : Nat := 25615533965799755087245

theorem tailTrace_1346924 : CollatzResearch.WordTrace tailWord_1346924 prefixEnd_1346924 25615533965799755087245 := by
  unfold tailWord_1346924
  simp only [CollatzResearch.WordTrace]
  refine ⟨24563177086165929575091913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32750902781554572766789217 24563177086165929575091913)
  ·
    refine ⟨18422382814624447181318935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24563177086165929575091913 18422382814624447181318935)
    ·
      refine ⟨27633574221936670771978403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18422382814624447181318935 27633574221936670771978403)
      ·
        refine ⟨41450361332905006157967605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27633574221936670771978403 41450361332905006157967605)
        ·
          refine ⟨3885971374959844327309463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41450361332905006157967605 3885971374959844327309463)
          ·
            refine ⟨5828957062439766490964195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3885971374959844327309463 5828957062439766490964195)
            ·
              refine ⟨8743435593659649736446293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5828957062439766490964195 8743435593659649736446293)
              ·
                refine ⟨25615533965799755087245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8743435593659649736446293 25615533965799755087245)
                ·
                  rfl

theorem cell23_1346924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 10].length) (baseStart_1346924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346924 prefixEnd_1346924 := by exact prefixLift 1346924
  have htrace : WordTrace (prefixWord ++ tailWord_1346924) baseStart_1346924 baseEnd_1346924 := by
    simpa [prefixWord, tailWord_1346924, baseEnd_1346924] using wordTrace_append hprefix tailTrace_1346924
  have hstable : (prefixWord ++ tailWord_1346924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346924).length < 2 ^ (prefixWord ++ tailWord_1346924).sum := by decide
  have hdescent : baseEnd_1346924 < baseStart_1346924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346951 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_1346951 : Nat := 118140960795 + 1346951 * 2 ^ 59
def prefixEnd_1346951 : Nat := 4983230072969 + 3 ^ 40 * 1346951 * 2
def baseEnd_1346951 : Nat := 691633281054264781717991

theorem tailTrace_1346951 : CollatzResearch.WordTrace tailWord_1346951 prefixEnd_1346951 691633281054264781717991 := by
  unfold tailWord_1346951
  simp only [CollatzResearch.WordTrace]
  refine ⟨49127338943234042761416707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32751559295489361840944471 49127338943234042761416707)
  ·
    refine ⟨73691008414851064142125061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49127338943234042761416707 73691008414851064142125061)
    ·
      refine ⟨13817064077784574526648449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73691008414851064142125061 13817064077784574526648449)
      ·
        refine ⟨10362798058338430894986337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13817064077784574526648449 10362798058338430894986337)
        ·
          refine ⟨7772098543753823171239753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10362798058338430894986337 7772098543753823171239753)
          ·
            refine ⟨5829073907815367378429815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7772098543753823171239753 5829073907815367378429815)
            ·
              refine ⟨8743610861723051067644723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5829073907815367378429815 8743610861723051067644723)
              ·
                refine ⟨13115416292584576601467085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8743610861723051067644723 13115416292584576601467085)
                ·
                  refine ⟨4918281109719216225550157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13115416292584576601467085 4918281109719216225550157)
                  ·
                    refine ⟨1844355416144706084581309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4918281109719216225550157 1844355416144706084581309)
                    ·
                      refine ⟨691633281054264781717991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1844355416144706084581309 691633281054264781717991)
                      ·
                        rfl

theorem cell23_1346951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_1346951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346951 prefixEnd_1346951 := by exact prefixLift 1346951
  have htrace : WordTrace (prefixWord ++ tailWord_1346951) baseStart_1346951 baseEnd_1346951 := by
    simpa [prefixWord, tailWord_1346951, baseEnd_1346951] using wordTrace_append hprefix tailTrace_1346951
  have hstable : (prefixWord ++ tailWord_1346951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346951).length < 2 ^ (prefixWord ++ tailWord_1346951).sum := by decide
  have hdescent : baseEnd_1346951 < baseStart_1346951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346962 : List Nat := [3, 2, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_1346962 : Nat := 118140960795 + 1346962 * 2 ^ 59
def prefixEnd_1346962 : Nat := 4983230072969 + 3 ^ 40 * 1346962 * 2
def baseEnd_1346962 : Nat := 230546309780488079560147

theorem tailTrace_1346962 : CollatzResearch.WordTrace tailWord_1346962 prefixEnd_1346962 230546309780488079560147 := by
  unfold tailWord_1346962
  simp only [CollatzResearch.WordTrace]
  refine ⟨12281935036548547910016785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32751826764129461093378093 12281935036548547910016785)
  ·
    refine ⟨9211451277411410932512589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12281935036548547910016785 9211451277411410932512589)
    ·
      refine ⟨3454294229029279099692221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9211451277411410932512589 3454294229029279099692221)
      ·
        refine ⟨1295360335885979662384583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3454294229029279099692221 1295360335885979662384583)
        ·
          refine ⟨1943040503828969493576875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1295360335885979662384583 1943040503828969493576875)
          ·
            refine ⟨2914560755743454240365313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943040503828969493576875 2914560755743454240365313)
            ·
              refine ⟨2185920566807590680273985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2914560755743454240365313 2185920566807590680273985)
              ·
                refine ⟨1639440425105693010205489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2185920566807590680273985 1639440425105693010205489)
                ·
                  refine ⟨1229580318829269757654117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1639440425105693010205489 1229580318829269757654117)
                  ·
                    refine ⟨230546309780488079560147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1229580318829269757654117 230546309780488079560147)
                    ·
                      rfl

theorem cell23_1346962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_1346962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346962 prefixEnd_1346962 := by exact prefixLift 1346962
  have htrace : WordTrace (prefixWord ++ tailWord_1346962) baseStart_1346962 baseEnd_1346962 := by
    simpa [prefixWord, tailWord_1346962, baseEnd_1346962] using wordTrace_append hprefix tailTrace_1346962
  have hstable : (prefixWord ++ tailWord_1346962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346962).length < 2 ^ (prefixWord ++ tailWord_1346962).sum := by decide
  have hdescent : baseEnd_1346962 < baseStart_1346962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346969 : List Nat := [1, 2, 1, 2, 1, 7, 2, 2, 1, 2, 2]
def baseStart_1346969 : Nat := 118140960795 + 1346969 * 2 ^ 59
def prefixEnd_1346969 : Nat := 4983230072969 + 3 ^ 40 * 1346969 * 2
def baseEnd_1346969 : Nat := 691642523706045711292909

theorem tailTrace_1346969 : CollatzResearch.WordTrace tailWord_1346969 prefixEnd_1346969 691642523706045711292909 := by
  unfold tailWord_1346969
  simp only [CollatzResearch.WordTrace]
  refine ⟨49127995457168831835571961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32751996971445887890381307 49127995457168831835571961)
  ·
    refine ⟨36845996592876623876678971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49127995457168831835571961 36845996592876623876678971)
    ·
      refine ⟨55268994889314935815018457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36845996592876623876678971 55268994889314935815018457)
      ·
        refine ⟨41451746166986201861263843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55268994889314935815018457 41451746166986201861263843)
        ·
          refine ⟨62177619250479302791895765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41451746166986201861263843 62177619250479302791895765)
          ·
            refine ⟨1457287951183108659185057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 62177619250479302791895765 1457287951183108659185057)
            ·
              refine ⟨1092965963387331494388793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1457287951183108659185057 1092965963387331494388793)
              ·
                refine ⟨819724472540498620791595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1092965963387331494388793 819724472540498620791595)
                ·
                  refine ⟨1229586708810747931187393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 819724472540498620791595 1229586708810747931187393)
                  ·
                    refine ⟨922190031608060948390545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1229586708810747931187393 922190031608060948390545)
                    ·
                      refine ⟨691642523706045711292909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922190031608060948390545 691642523706045711292909)
                      ·
                        rfl

theorem cell23_1346969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 1, 2, 2].length) (baseStart_1346969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1346969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1346969 prefixEnd_1346969 := by exact prefixLift 1346969
  have htrace : WordTrace (prefixWord ++ tailWord_1346969) baseStart_1346969 baseEnd_1346969 := by
    simpa [prefixWord, tailWord_1346969, baseEnd_1346969] using wordTrace_append hprefix tailTrace_1346969
  have hstable : (prefixWord ++ tailWord_1346969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346969).length < 2 ^ (prefixWord ++ tailWord_1346969).sum := by decide
  have hdescent : baseEnd_1346969 < baseStart_1346969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347008 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 1, 4, 2]
def baseStart_1347008 : Nat := 118140960795 + 1347008 * 2 ^ 59
def prefixEnd_1347008 : Nat := 4983230072969 + 3 ^ 40 * 1347008 * 2
def baseEnd_1347008 : Nat := 691662549451571058705229

theorem tailTrace_1347008 : CollatzResearch.WordTrace tailWord_1347008 prefixEnd_1347008 691662549451571058705229 := by
  unfold tailWord_1347008
  simp only [CollatzResearch.WordTrace]
  refine ⟨24564708952013770748120839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32752945269351694330827785 24564708952013770748120839)
  ·
    refine ⟨36847063428020656122181259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24564708952013770748120839 36847063428020656122181259)
    ·
      refine ⟨55270595142030984183271889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36847063428020656122181259 55270595142030984183271889)
      ·
        refine ⟨41452946356523238137453917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55270595142030984183271889 41452946356523238137453917)
        ·
          refine ⟨15544854883696214301545219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41452946356523238137453917 15544854883696214301545219)
          ·
            refine ⟨23317282325544321452317829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15544854883696214301545219 23317282325544321452317829)
            ·
              refine ⟨4371990436039560272309593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23317282325544321452317829 4371990436039560272309593)
              ·
                refine ⟨3278992827029670204232195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4371990436039560272309593 3278992827029670204232195)
                ·
                  refine ⟨4918489240544505306348293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3278992827029670204232195 4918489240544505306348293)
                  ·
                    refine ⟨922216732602094744940305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4918489240544505306348293 922216732602094744940305)
                    ·
                      refine ⟨691662549451571058705229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922216732602094744940305 691662549451571058705229)
                      ·
                        rfl

theorem cell23_1347008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 4, 2].length) (baseStart_1347008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347008 prefixEnd_1347008 := by exact prefixLift 1347008
  have htrace : WordTrace (prefixWord ++ tailWord_1347008) baseStart_1347008 baseEnd_1347008 := by
    simpa [prefixWord, tailWord_1347008, baseEnd_1347008] using wordTrace_append hprefix tailTrace_1347008
  have hstable : (prefixWord ++ tailWord_1347008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347008).length < 2 ^ (prefixWord ++ tailWord_1347008).sum := by decide
  have hdescent : baseEnd_1347008 < baseStart_1347008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347012 : List Nat := [2, 3, 3, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_1347012 : Nat := 118140960795 + 1347012 * 2 ^ 59
def prefixEnd_1347012 : Nat := 4983230072969 + 3 ^ 40 * 1347012 * 2
def baseEnd_1347012 : Nat := 691664603374189043055211

theorem tailTrace_1347012 : CollatzResearch.WordTrace tailWord_1347012 prefixEnd_1347012 691664603374189043055211 := by
  unfold tailWord_1347012
  simp only [CollatzResearch.WordTrace]
  refine ⟨24564781898006525089693645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32753042530675366786258193 24564781898006525089693645)
  ·
    refine ⟨9211793211752446908635117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24564781898006525089693645 9211793211752446908635117)
    ·
      refine ⟨3454422454407167590738169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9211793211752446908635117 3454422454407167590738169)
      ·
        refine ⟨2590816840805375693053627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3454422454407167590738169 2590816840805375693053627)
        ·
          refine ⟨3886225261208063539580441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590816840805375693053627 3886225261208063539580441)
          ·
            refine ⟨2914668945906047654685331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3886225261208063539580441 2914668945906047654685331)
            ·
              refine ⟨4372003418859071482027997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2914668945906047654685331 4372003418859071482027997)
              ·
                refine ⟨1639501282072151805760499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4372003418859071482027997 1639501282072151805760499)
                ·
                  refine ⟨2459251923108227708640749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639501282072151805760499 2459251923108227708640749)
                  ·
                    refine ⟨922219471165585390740281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459251923108227708640749 922219471165585390740281)
                    ·
                      refine ⟨691664603374189043055211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922219471165585390740281 691664603374189043055211)
                      ·
                        rfl

theorem cell23_1347012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_1347012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347012 prefixEnd_1347012 := by exact prefixLift 1347012
  have htrace : WordTrace (prefixWord ++ tailWord_1347012) baseStart_1347012 baseEnd_1347012 := by
    simpa [prefixWord, tailWord_1347012, baseEnd_1347012] using wordTrace_append hprefix tailTrace_1347012
  have hstable : (prefixWord ++ tailWord_1347012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347012).length < 2 ^ (prefixWord ++ tailWord_1347012).sum := by decide
  have hdescent : baseEnd_1347012 < baseStart_1347012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347024 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 7]
def baseStart_1347024 : Nat := 118140960795 + 1347024 * 2 ^ 59
def prefixEnd_1347024 : Nat := 4983230072969 + 3 ^ 40 * 1347024 * 2
def baseEnd_1347024 : Nat := 691670765142042996105155

theorem tailTrace_1347024 : CollatzResearch.WordTrace tailWord_1347024 prefixEnd_1347024 691670765142042996105155 := by
  unfold tailWord_1347024
  simp only [CollatzResearch.WordTrace]
  refine ⟨24565000735984788114412063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32753334314646384152549417 24565000735984788114412063)
  ·
    refine ⟨36847501103977182171618095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24565000735984788114412063 36847501103977182171618095)
    ·
      refine ⟨55271251655965773257427143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36847501103977182171618095 55271251655965773257427143)
      ·
        refine ⟨82906877483948659886140715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55271251655965773257427143 82906877483948659886140715)
        ·
          refine ⟨124360316225922989829211073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82906877483948659886140715 124360316225922989829211073)
          ·
            refine ⟨93270237169442242371908305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124360316225922989829211073 93270237169442242371908305)
            ·
              refine ⟨69952677877081681778931229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93270237169442242371908305 69952677877081681778931229)
              ·
                refine ⟨26232254203905630667099211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69952677877081681778931229 26232254203905630667099211)
                ·
                  refine ⟨39348381305858446000648817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26232254203905630667099211 39348381305858446000648817)
                  ·
                    refine ⟨29511285979393834500486613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39348381305858446000648817 29511285979393834500486613)
                    ·
                      refine ⟨691670765142042996105155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29511285979393834500486613 691670765142042996105155)
                      ·
                        rfl

theorem cell23_1347024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_1347024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347024 prefixEnd_1347024 := by exact prefixLift 1347024
  have htrace : WordTrace (prefixWord ++ tailWord_1347024) baseStart_1347024 baseEnd_1347024 := by
    simpa [prefixWord, tailWord_1347024, baseEnd_1347024] using wordTrace_append hprefix tailTrace_1347024
  have hstable : (prefixWord ++ tailWord_1347024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347024).length < 2 ^ (prefixWord ++ tailWord_1347024).sum := by decide
  have hdescent : baseEnd_1347024 < baseStart_1347024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347098 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2]
def baseStart_1347098 : Nat := 118140960795 + 1347098 * 2 ^ 59
def prefixEnd_1347098 : Nat := 4983230072969 + 3 ^ 40 * 1347098 * 2
def baseEnd_1347098 : Nat := 691708762710475706579815

theorem tailTrace_1347098 : CollatzResearch.WordTrace tailWord_1347098 prefixEnd_1347098 691708762710475706579815 := by
  unfold tailWord_1347098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12283175118425371716754487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32755133649134324578011965 12283175118425371716754487)
  ·
    refine ⟨18424762677638057575131731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12283175118425371716754487 18424762677638057575131731)
    ·
      refine ⟨27637144016457086362697597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18424762677638057575131731 27637144016457086362697597)
      ·
        refine ⟨10363929006171407386011599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27637144016457086362697597 10363929006171407386011599)
        ·
          refine ⟨15545893509257111079017399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10363929006171407386011599 15545893509257111079017399)
          ·
            refine ⟨23318840263885666618526099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15545893509257111079017399 23318840263885666618526099)
            ·
              refine ⟨34978260395828499927789149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23318840263885666618526099 34978260395828499927789149)
              ·
                refine ⟨13116847648435687472920931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34978260395828499927789149 13116847648435687472920931)
                ·
                  refine ⟨19675271472653531209381397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13116847648435687472920931 19675271472653531209381397)
                  ·
                    refine ⟨922278350280634275439753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19675271472653531209381397 922278350280634275439753)
                    ·
                      refine ⟨691708762710475706579815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922278350280634275439753 691708762710475706579815)
                      ·
                        rfl

theorem cell23_1347098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_1347098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347098 prefixEnd_1347098 := by exact prefixLift 1347098
  have htrace : WordTrace (prefixWord ++ tailWord_1347098) baseStart_1347098 baseEnd_1347098 := by
    simpa [prefixWord, tailWord_1347098, baseEnd_1347098] using wordTrace_append hprefix tailTrace_1347098
  have hstable : (prefixWord ++ tailWord_1347098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347098).length < 2 ^ (prefixWord ++ tailWord_1347098).sum := by decide
  have hdescent : baseEnd_1347098 < baseStart_1347098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347141 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_1347141 : Nat := 118140960795 + 1347141 * 2 ^ 59
def prefixEnd_1347141 : Nat := 4983230072969 + 3 ^ 40 * 1347141 * 2
def baseEnd_1347141 : Nat := 691730842378619038342117

theorem tailTrace_1347141 : CollatzResearch.WordTrace tailWord_1347141 prefixEnd_1347141 691730842378619038342117 := by
  unfold tailWord_1347141
  simp only [CollatzResearch.WordTrace]
  refine ⟨49134268812545705210833277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32756179208363803473888851 49134268812545705210833277)
  ·
    refine ⟨18425350804704639454062479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49134268812545705210833277 18425350804704639454062479)
    ·
      refine ⟨27638026207056959181093719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18425350804704639454062479 27638026207056959181093719)
      ·
        refine ⟨41457039310585438771640579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27638026207056959181093719 41457039310585438771640579)
        ·
          refine ⟨62185558965878158157460869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41457039310585438771640579 62185558965878158157460869)
          ·
            refine ⟨11659792306102154654523913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62185558965878158157460869 11659792306102154654523913)
            ·
              refine ⟨8744844229576615990892935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11659792306102154654523913 8744844229576615990892935)
              ·
                refine ⟨13117266344364923986339403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8744844229576615990892935 13117266344364923986339403)
                ·
                  refine ⟨19675899516547385979509105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13117266344364923986339403 19675899516547385979509105)
                  ·
                    refine ⟨14756924637410539484631829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19675899516547385979509105 14756924637410539484631829)
                    ·
                      refine ⟨691730842378619038342117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14756924637410539484631829 691730842378619038342117)
                      ·
                        rfl

theorem cell23_1347141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_1347141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347141 prefixEnd_1347141 := by exact prefixLift 1347141
  have htrace : WordTrace (prefixWord ++ tailWord_1347141) baseStart_1347141 baseEnd_1347141 := by
    simpa [prefixWord, tailWord_1347141, baseEnd_1347141] using wordTrace_append hprefix tailTrace_1347141
  have hstable : (prefixWord ++ tailWord_1347141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347141).length < 2 ^ (prefixWord ++ tailWord_1347141).sum := by decide
  have hdescent : baseEnd_1347141 < baseStart_1347141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347168 : List Nat := [2, 1, 1, 3, 2, 1, 1, 6, 1, 5]
def baseStart_1347168 : Nat := 118140960795 + 1347168 * 2 ^ 59
def prefixEnd_1347168 : Nat := 4983230072969 + 3 ^ 40 * 1347168 * 2
def baseEnd_1347168 : Nat := 230581568785430144234831

theorem tailTrace_1347168 : CollatzResearch.WordTrace tailWord_1347168 prefixEnd_1347168 230581568785430144234831 := by
  unfold tailWord_1347168
  simp only [CollatzResearch.WordTrace]
  refine ⟨24567626791723944411033079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32756835722298592548044105 24567626791723944411033079)
  ·
    refine ⟨36851440187585916616549619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24567626791723944411033079 36851440187585916616549619)
    ·
      refine ⟨55277160281378874924824429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36851440187585916616549619 55277160281378874924824429)
      ·
        refine ⟨20728935105517078096809161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55277160281378874924824429 20728935105517078096809161)
        ·
          refine ⟨15546701329137808572606871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20728935105517078096809161 15546701329137808572606871)
          ·
            refine ⟨23320051993706712858910307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15546701329137808572606871 23320051993706712858910307)
            ·
              refine ⟨34980077990560069288365461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23320051993706712858910307 34980077990560069288365461)
              ·
                refine ⟨1639691155807503247892131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34980077990560069288365461 1639691155807503247892131)
                ·
                  refine ⟨2459536733711254871838197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639691155807503247892131 2459536733711254871838197)
                  ·
                    refine ⟨230581568785430144234831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2459536733711254871838197 230581568785430144234831)
                    ·
                      rfl

theorem cell23_1347168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 1, 5].length) (baseStart_1347168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347168 prefixEnd_1347168 := by exact prefixLift 1347168
  have htrace : WordTrace (prefixWord ++ tailWord_1347168) baseStart_1347168 baseEnd_1347168 := by
    simpa [prefixWord, tailWord_1347168, baseEnd_1347168] using wordTrace_append hprefix tailTrace_1347168
  have hstable : (prefixWord ++ tailWord_1347168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347168).length < 2 ^ (prefixWord ++ tailWord_1347168).sum := by decide
  have hdescent : baseEnd_1347168 < baseStart_1347168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347211 : List Nat := [1, 1, 1, 1, 4, 1, 4, 10]
def baseStart_1347211 : Nat := 118140960795 + 1347211 * 2 ^ 59
def prefixEnd_1347211 : Nat := 4983230072969 + 3 ^ 40 * 1347211 * 2
def baseEnd_1347211 : Nat := 25620992074979028313585

theorem tailTrace_1347211 : CollatzResearch.WordTrace tailWord_1347211 prefixEnd_1347211 25620992074979028313585 := by
  unfold tailWord_1347211
  simp only [CollatzResearch.WordTrace]
  refine ⟨49136821922292107165881487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32757881281528071443920991 49136821922292107165881487)
  ·
    refine ⟨73705232883438160748822231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49136821922292107165881487 73705232883438160748822231)
    ·
      refine ⟨110557849325157241123233347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73705232883438160748822231 110557849325157241123233347)
      ·
        refine ⟨165836773987735861684850021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110557849325157241123233347 165836773987735861684850021)
        ·
          refine ⟨31094395122700474065909379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165836773987735861684850021 31094395122700474065909379)
          ·
            refine ⟨46641592684050711098864069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31094395122700474065909379 46641592684050711098864069)
            ·
              refine ⟨8745298628259508331037013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46641592684050711098864069 8745298628259508331037013)
              ·
                refine ⟨25620992074979028313585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8745298628259508331037013 25620992074979028313585)
                ·
                  rfl

theorem cell23_1347211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 10].length) (baseStart_1347211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347211 prefixEnd_1347211 := by exact prefixLift 1347211
  have htrace : WordTrace (prefixWord ++ tailWord_1347211) baseStart_1347211 baseEnd_1347211 := by
    simpa [prefixWord, tailWord_1347211, baseEnd_1347211] using wordTrace_append hprefix tailTrace_1347211
  have hstable : (prefixWord ++ tailWord_1347211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347211).length < 2 ^ (prefixWord ++ tailWord_1347211).sum := by decide
  have hdescent : baseEnd_1347211 < baseStart_1347211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347272 : List Nat := [2, 1, 3, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_1347272 : Nat := 118140960795 + 1347272 * 2 ^ 59
def prefixEnd_1347272 : Nat := 4983230072969 + 3 ^ 40 * 1347272 * 2
def baseEnd_1347272 : Nat := 691798108344358025804015

theorem tailTrace_1347272 : CollatzResearch.WordTrace tailWord_1347272 prefixEnd_1347272 691798108344358025804015 := by
  unfold tailWord_1347272
  simp only [CollatzResearch.WordTrace]
  refine ⟨24569523387535557291926035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32759364516714076389234713 24569523387535557291926035)
  ·
    refine ⟨36854285081303335937889053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24569523387535557291926035 36854285081303335937889053)
    ·
      refine ⟨13820356905488750976708395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36854285081303335937889053 13820356905488750976708395)
      ·
        refine ⟨20730535358233126465062593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13820356905488750976708395 20730535358233126465062593)
        ·
          refine ⟨15547901518674844848796945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20730535358233126465062593 15547901518674844848796945)
          ·
            refine ⟨11660926139006133636597709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15547901518674844848796945 11660926139006133636597709)
            ·
              refine ⟨4372847302127300113724141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11660926139006133636597709 4372847302127300113724141)
              ·
                refine ⟨1639817738297737542646553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4372847302127300113724141 1639817738297737542646553)
                ·
                  refine ⟨1229863303723303156984915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1639817738297737542646553 1229863303723303156984915)
                  ·
                    refine ⟨1844794955584954735477373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1229863303723303156984915 1844794955584954735477373)
                    ·
                      refine ⟨691798108344358025804015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1844794955584954735477373 691798108344358025804015)
                      ·
                        rfl

theorem cell23_1347272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_1347272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347272 prefixEnd_1347272 := by exact prefixLift 1347272
  have htrace : WordTrace (prefixWord ++ tailWord_1347272) baseStart_1347272 baseEnd_1347272 := by
    simpa [prefixWord, tailWord_1347272, baseEnd_1347272] using wordTrace_append hprefix tailTrace_1347272
  have hstable : (prefixWord ++ tailWord_1347272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347272).length < 2 ^ (prefixWord ++ tailWord_1347272).sum := by decide
  have hdescent : baseEnd_1347272 < baseStart_1347272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347276 : List Nat := [2, 2, 1, 5, 3, 1, 1, 2, 1, 2, 3]
def baseStart_1347276 : Nat := 118140960795 + 1347276 * 2 ^ 59
def prefixEnd_1347276 : Nat := 4983230072969 + 3 ^ 40 * 1347276 * 2
def baseEnd_1347276 : Nat := 691800162266976010153997

theorem tailTrace_1347276 : CollatzResearch.WordTrace tailWord_1347276 prefixEnd_1347276 691800162266976010153997 := by
  unfold tailWord_1347276
  simp only [CollatzResearch.WordTrace]
  refine ⟨24569596333528311633498841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32759461778037748844665121 24569596333528311633498841)
  ·
    refine ⟨18427197250146233725124131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24569596333528311633498841 18427197250146233725124131)
    ·
      refine ⟨27640795875219350587686197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18427197250146233725124131 27640795875219350587686197)
      ·
        refine ⟨2591324613301814117595581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27640795875219350587686197 2591324613301814117595581)
        ·
          refine ⟨971746729988180294098343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2591324613301814117595581 971746729988180294098343)
          ·
            refine ⟨1457620094982270441147515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971746729988180294098343 1457620094982270441147515)
            ·
              refine ⟨2186430142473405661721273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457620094982270441147515 2186430142473405661721273)
              ·
                refine ⟨1639822606855054246290955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186430142473405661721273 1639822606855054246290955)
                ·
                  refine ⟨2459733910282581369436433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639822606855054246290955 2459733910282581369436433)
                  ·
                    refine ⟨1844800432711936027077325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2459733910282581369436433 1844800432711936027077325)
                    ·
                      refine ⟨691800162266976010153997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1844800432711936027077325 691800162266976010153997)
                      ·
                        rfl

theorem cell23_1347276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_1347276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347276 prefixEnd_1347276 := by exact prefixLift 1347276
  have htrace : WordTrace (prefixWord ++ tailWord_1347276) baseStart_1347276 baseEnd_1347276 := by
    simpa [prefixWord, tailWord_1347276, baseEnd_1347276] using wordTrace_append hprefix tailTrace_1347276
  have hstable : (prefixWord ++ tailWord_1347276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347276).length < 2 ^ (prefixWord ++ tailWord_1347276).sum := by decide
  have hdescent : baseEnd_1347276 < baseStart_1347276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347316 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_1347316 : Nat := 118140960795 + 1347316 * 2 ^ 59
def prefixEnd_1347316 : Nat := 4983230072969 + 3 ^ 40 * 1347316 * 2
def baseEnd_1347316 : Nat := 691820701493155853653813

theorem tailTrace_1347316 : CollatzResearch.WordTrace tailWord_1347316 prefixEnd_1347316 691820701493155853653813 := by
  unfold tailWord_1347316
  simp only [CollatzResearch.WordTrace]
  refine ⟨24570325793455855049226901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32760434391274473398969201 24570325793455855049226901)
  ·
    refine ⟨1151734021568243205432511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24570325793455855049226901 1151734021568243205432511)
    ·
      refine ⟨1727601032352364808148767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1151734021568243205432511 1727601032352364808148767)
      ·
        refine ⟨2591401548528547212223151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1727601032352364808148767 2591401548528547212223151)
        ·
          refine ⟨3887102322792820818334727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591401548528547212223151 3887102322792820818334727)
          ·
            refine ⟨5830653484189231227502091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3887102322792820818334727 5830653484189231227502091)
            ·
              refine ⟨8745980226283846841253137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5830653484189231227502091 8745980226283846841253137)
              ·
                refine ⟨6559485169712885130939853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8745980226283846841253137 6559485169712885130939853)
                ·
                  refine ⟨2459806938642331924102445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6559485169712885130939853 2459806938642331924102445)
                  ·
                    refine ⟨922427601990874471538417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459806938642331924102445 922427601990874471538417)
                    ·
                      refine ⟨691820701493155853653813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922427601990874471538417 691820701493155853653813)
                      ·
                        rfl

theorem cell23_1347316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_1347316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347316 prefixEnd_1347316 := by exact prefixLift 1347316
  have htrace : WordTrace (prefixWord ++ tailWord_1347316) baseStart_1347316 baseEnd_1347316 := by
    simpa [prefixWord, tailWord_1347316, baseEnd_1347316] using wordTrace_append hprefix tailTrace_1347316
  have hstable : (prefixWord ++ tailWord_1347316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347316).length < 2 ^ (prefixWord ++ tailWord_1347316).sum := by decide
  have hdescent : baseEnd_1347316 < baseStart_1347316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347329 : List Nat := [1, 2, 4, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_1347329 : Nat := 118140960795 + 1347329 * 2 ^ 59
def prefixEnd_1347329 : Nat := 4983230072969 + 3 ^ 40 * 1347329 * 2
def baseEnd_1347329 : Nat := 691827376741664302791253

theorem tailTrace_1347329 : CollatzResearch.WordTrace tailWord_1347329 prefixEnd_1347329 691827376741664302791253 := by
  unfold tailWord_1347329
  simp only [CollatzResearch.WordTrace]
  refine ⟨49141125735864613318677041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32760750490576408879118027 49141125735864613318677041)
  ·
    refine ⟨36855844301898459989007781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49141125735864613318677041 36855844301898459989007781)
    ·
      refine ⟨6910470806605961247938959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36855844301898459989007781 6910470806605961247938959)
      ·
        refine ⟨10365706209908941871908439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6910470806605961247938959 10365706209908941871908439)
        ·
          refine ⟨15548559314863412807862659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10365706209908941871908439 15548559314863412807862659)
          ·
            refine ⟨23322838972295119211793989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15548559314863412807862659 23322838972295119211793989)
            ·
              refine ⟨4373032307305334852211373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23322838972295119211793989 4373032307305334852211373)
              ·
                refine ⟨1639887115239500569579265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4373032307305334852211373 1639887115239500569579265)
                ·
                  refine ⟨1229915336429625427184449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1639887115239500569579265 1229915336429625427184449)
                  ·
                    refine ⟨922436502322219070388337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1229915336429625427184449 922436502322219070388337)
                    ·
                      refine ⟨691827376741664302791253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922436502322219070388337 691827376741664302791253)
                      ·
                        rfl

theorem cell23_1347329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_1347329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347329 prefixEnd_1347329 := by exact prefixLift 1347329
  have htrace : WordTrace (prefixWord ++ tailWord_1347329) baseStart_1347329 baseEnd_1347329 := by
    simpa [prefixWord, tailWord_1347329, baseEnd_1347329] using wordTrace_append hprefix tailTrace_1347329
  have hstable : (prefixWord ++ tailWord_1347329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347329).length < 2 ^ (prefixWord ++ tailWord_1347329).sum := by decide
  have hdescent : baseEnd_1347329 < baseStart_1347329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347355 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 4, 5, 2]
def baseStart_1347355 : Nat := 118140960795 + 1347355 * 2 ^ 59
def prefixEnd_1347355 : Nat := 4983230072969 + 3 ^ 40 * 1347355 * 2
def baseEnd_1347355 : Nat := 691840727238681201066133

theorem tailTrace_1347355 : CollatzResearch.WordTrace tailWord_1347355 prefixEnd_1347355 691840727238681201066133 := by
  unfold tailWord_1347355
  simp only [CollatzResearch.WordTrace]
  refine ⟨49142074033770419759123519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32761382689180279839415679 49142074033770419759123519)
  ·
    refine ⟨73713111050655629638685279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49142074033770419759123519 73713111050655629638685279)
    ·
      refine ⟨110569666575983444458027919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73713111050655629638685279 110569666575983444458027919)
      ·
        refine ⟨165854499863975166687041879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110569666575983444458027919 165854499863975166687041879)
        ·
          refine ⟨248781749795962750030562819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165854499863975166687041879 248781749795962750030562819)
          ·
            refine ⟨373172624693944125045844229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248781749795962750030562819 373172624693944125045844229)
            ·
              refine ⟨69969867130114523446095793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 373172624693944125045844229 69969867130114523446095793)
              ·
                refine ⟨52477400347585892584571845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69969867130114523446095793 52477400347585892584571845)
                ·
                  refine ⟨9839512565172354859607221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52477400347585892584571845 9839512565172354859607221)
                  ·
                    refine ⟨922454302984908268088177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9839512565172354859607221 922454302984908268088177)
                    ·
                      refine ⟨691840727238681201066133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922454302984908268088177 691840727238681201066133)
                      ·
                        rfl

theorem cell23_1347355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 5, 2].length) (baseStart_1347355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347355 prefixEnd_1347355 := by exact prefixLift 1347355
  have htrace : WordTrace (prefixWord ++ tailWord_1347355) baseStart_1347355 baseEnd_1347355 := by
    simpa [prefixWord, tailWord_1347355, baseEnd_1347355] using wordTrace_append hprefix tailTrace_1347355
  have hstable : (prefixWord ++ tailWord_1347355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347355).length < 2 ^ (prefixWord ++ tailWord_1347355).sum := by decide
  have hdescent : baseEnd_1347355 < baseStart_1347355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347382 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1347382 : Nat := 118140960795 + 1347382 * 2 ^ 59
def prefixEnd_1347382 : Nat := 4983230072969 + 3 ^ 40 * 1347382 * 2
def baseEnd_1347382 : Nat := 230618197072117531809503

theorem tailTrace_1347382 : CollatzResearch.WordTrace tailWord_1347382 prefixEnd_1347382 230618197072117531809503 := by
  unfold tailWord_1347382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3071441175292037710647275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32762039203115068913570933 3071441175292037710647275)
  ·
    refine ⟨4607161762938056565970913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3071441175292037710647275 4607161762938056565970913)
    ·
      refine ⟨3455371322203542424478185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4607161762938056565970913 3455371322203542424478185)
      ·
        refine ⟨2591528491652656818358639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3455371322203542424478185 2591528491652656818358639)
        ·
          refine ⟨3887292737478985227537959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591528491652656818358639 3887292737478985227537959)
          ·
            refine ⟨5830939106218477841306939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3887292737478985227537959 5830939106218477841306939)
            ·
              refine ⟨8746408659327716761960409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5830939106218477841306939 8746408659327716761960409)
              ·
                refine ⟨6559806494495787571470307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8746408659327716761960409 6559806494495787571470307)
                ·
                  refine ⟨9839709741743681357205461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6559806494495787571470307 9839709741743681357205461)
                  ·
                    refine ⟨230618197072117531809503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9839709741743681357205461 230618197072117531809503)
                    ·
                      rfl

theorem cell23_1347382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1347382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347382 prefixEnd_1347382 := by exact prefixLift 1347382
  have htrace : WordTrace (prefixWord ++ tailWord_1347382) baseStart_1347382 baseEnd_1347382 := by
    simpa [prefixWord, tailWord_1347382, baseEnd_1347382] using wordTrace_append hprefix tailTrace_1347382
  have hstable : (prefixWord ++ tailWord_1347382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347382).length < 2 ^ (prefixWord ++ tailWord_1347382).sum := by decide
  have hdescent : baseEnd_1347382 < baseStart_1347382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347425 : List Nat := [1, 2, 3, 1, 1, 1, 4, 4, 6]
def baseStart_1347425 : Nat := 118140960795 + 1347425 * 2 ^ 59
def prefixEnd_1347425 : Nat := 4983230072969 + 3 ^ 40 * 1347425 * 2
def baseEnd_1347425 : Nat := 76875185653832880798979

theorem tailTrace_1347425 : CollatzResearch.WordTrace tailWord_1347425 prefixEnd_1347425 76875185653832880798979 := by
  unfold tailWord_1347425
  simp only [CollatzResearch.WordTrace]
  refine ⟨49144627143516821714171729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32763084762344547809447819 49144627143516821714171729)
  ·
    refine ⟨36858470357637616285628797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49144627143516821714171729 36858470357637616285628797)
    ·
      refine ⟨13821926384114106107110799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36858470357637616285628797 13821926384114106107110799)
      ·
        refine ⟨20732889576171159160666199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13821926384114106107110799 20732889576171159160666199)
        ·
          refine ⟨31099334364256738740999299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20732889576171159160666199 31099334364256738740999299)
          ·
            refine ⟨46649001546385108111498949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31099334364256738740999299 46649001546385108111498949)
            ·
              refine ⟨8746687789947207770906053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46649001546385108111498949 8746687789947207770906053)
              ·
                refine ⟨1640003960615101457044885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8746687789947207770906053 1640003960615101457044885)
                ·
                  refine ⟨76875185653832880798979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1640003960615101457044885 76875185653832880798979)
                  ·
                    rfl

theorem cell23_1347425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 6].length) (baseStart_1347425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347425 prefixEnd_1347425 := by exact prefixLift 1347425
  have htrace : WordTrace (prefixWord ++ tailWord_1347425) baseStart_1347425 baseEnd_1347425 := by
    simpa [prefixWord, tailWord_1347425, baseEnd_1347425] using wordTrace_append hprefix tailTrace_1347425
  have hstable : (prefixWord ++ tailWord_1347425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347425).length < 2 ^ (prefixWord ++ tailWord_1347425).sum := by decide
  have hdescent : baseEnd_1347425 < baseStart_1347425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347479 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 2, 3, 2]
def baseStart_1347479 : Nat := 118140960795 + 1347479 * 2 ^ 59
def prefixEnd_1347479 : Nat := 4983230072969 + 3 ^ 40 * 1347479 * 2
def baseEnd_1347479 : Nat := 691904398839838715915563

theorem tailTrace_1347479 : CollatzResearch.WordTrace tailWord_1347479 prefixEnd_1347479 691904398839838715915563 := by
  unfold tailWord_1347479
  simp only [CollatzResearch.WordTrace]
  refine ⟨49146596685321188936637491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32764397790214125957758327 49146596685321188936637491)
  ·
    refine ⟨73719895027981783404956237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49146596685321188936637491 73719895027981783404956237)
    ·
      refine ⟨27644960635493168776858589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73719895027981783404956237 27644960635493168776858589)
      ·
        refine ⟨10366860238309938291321971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27644960635493168776858589 10366860238309938291321971)
        ·
          refine ⟨15550290357464907436982957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10366860238309938291321971 15550290357464907436982957)
          ·
            refine ⟨5831358884049340288868609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15550290357464907436982957 5831358884049340288868609)
            ·
              refine ⟨4373519163037005216651457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5831358884049340288868609 4373519163037005216651457)
              ·
                refine ⟨3280139372277753912488593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4373519163037005216651457 3280139372277753912488593)
                ·
                  refine ⟨2460104529208315434366445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3280139372277753912488593 2460104529208315434366445)
                  ·
                    refine ⟨922539198453118287887417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2460104529208315434366445 922539198453118287887417)
                    ·
                      refine ⟨691904398839838715915563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922539198453118287887417 691904398839838715915563)
                      ·
                        rfl

theorem cell23_1347479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_1347479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347479 prefixEnd_1347479 := by exact prefixLift 1347479
  have htrace : WordTrace (prefixWord ++ tailWord_1347479) baseStart_1347479 baseEnd_1347479 := by
    simpa [prefixWord, tailWord_1347479, baseEnd_1347479] using wordTrace_append hprefix tailTrace_1347479
  have hstable : (prefixWord ++ tailWord_1347479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347479).length < 2 ^ (prefixWord ++ tailWord_1347479).sum := by decide
  have hdescent : baseEnd_1347479 < baseStart_1347479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347480 : List Nat := [2, 1, 2, 6, 1, 2, 2, 2, 1, 4]
def baseStart_1347480 : Nat := 118140960795 + 1347480 * 2 ^ 59
def prefixEnd_1347480 : Nat := 4983230072969 + 3 ^ 40 * 1347480 * 2
def baseEnd_1347480 : Nat := 230634970773497737334353

theorem tailTrace_1347480 : CollatzResearch.WordTrace tailWord_1347480 prefixEnd_1347480 230634970773497737334353 := by
  unfold tailWord_1347480
  simp only [CollatzResearch.WordTrace]
  refine ⟨24573316579158783053711947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32764422105545044071615929 24573316579158783053711947)
  ·
    refine ⟨36859974868738174580567921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24573316579158783053711947 36859974868738174580567921)
    ·
      refine ⟨27644981151553630935425941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36859974868738174580567921 27644981151553630935425941)
      ·
        refine ⟨1295858491479076450098091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27644981151553630935425941 1295858491479076450098091)
        ·
          refine ⟨1943787737218614675147137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1295858491479076450098091 1943787737218614675147137)
          ·
            refine ⟨1457840802913961006360353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1943787737218614675147137 1457840802913961006360353)
            ·
              refine ⟨1093380602185470754770265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1457840802913961006360353 1093380602185470754770265)
              ·
                refine ⟨820035451639103066077699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1093380602185470754770265 820035451639103066077699)
                ·
                  refine ⟨1230053177458654599116549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 820035451639103066077699 1230053177458654599116549)
                  ·
                    refine ⟨230634970773497737334353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1230053177458654599116549 230634970773497737334353)
                    ·
                      rfl

theorem cell23_1347480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_1347480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347480 prefixEnd_1347480 := by exact prefixLift 1347480
  have htrace : WordTrace (prefixWord ++ tailWord_1347480) baseStart_1347480 baseEnd_1347480 := by
    simpa [prefixWord, tailWord_1347480, baseEnd_1347480] using wordTrace_append hprefix tailTrace_1347480
  have hstable : (prefixWord ++ tailWord_1347480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347480).length < 2 ^ (prefixWord ++ tailWord_1347480).sum := by decide
  have hdescent : baseEnd_1347480 < baseStart_1347480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347492 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_1347492 : Nat := 118140960795 + 1347492 * 2 ^ 59
def prefixEnd_1347492 : Nat := 4983230072969 + 3 ^ 40 * 1347492 * 2
def baseEnd_1347492 : Nat := 691911074088347165053003

theorem tailTrace_1347492 : CollatzResearch.WordTrace tailWord_1347492 prefixEnd_1347492 691911074088347165053003 := by
  unfold tailWord_1347492
  simp only [CollatzResearch.WordTrace]
  refine ⟨24573535417137046078430365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32764713889516061437907153 24573535417137046078430365)
  ·
    refine ⟨9215075781426392279411387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24573535417137046078430365 9215075781426392279411387)
    ·
      refine ⟨13822613672139588419117081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9215075781426392279411387 13822613672139588419117081)
      ·
        refine ⟨10366960254104691314337811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13822613672139588419117081 10366960254104691314337811)
        ·
          refine ⟨15550440381157036971506717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10366960254104691314337811 15550440381157036971506717)
          ·
            refine ⟨5831415142933888864315019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15550440381157036971506717 5831415142933888864315019)
            ·
              refine ⟨8747122714400833296472529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5831415142933888864315019 8747122714400833296472529)
              ·
                refine ⟨6560342035800624972354397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8747122714400833296472529 6560342035800624972354397)
                ·
                  refine ⟨2460128263425234364632899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6560342035800624972354397 2460128263425234364632899)
                  ·
                    refine ⟨3690192395137851546949349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2460128263425234364632899 3690192395137851546949349)
                    ·
                      refine ⟨691911074088347165053003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3690192395137851546949349 691911074088347165053003)
                      ·
                        rfl

theorem cell23_1347492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_1347492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347492 prefixEnd_1347492 := by exact prefixLift 1347492
  have htrace : WordTrace (prefixWord ++ tailWord_1347492) baseStart_1347492 baseEnd_1347492 := by
    simpa [prefixWord, tailWord_1347492, baseEnd_1347492] using wordTrace_append hprefix tailTrace_1347492
  have hstable : (prefixWord ++ tailWord_1347492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347492).length < 2 ^ (prefixWord ++ tailWord_1347492).sum := by decide
  have hdescent : baseEnd_1347492 < baseStart_1347492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347512 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 3, 2, 3]
def baseStart_1347512 : Nat := 118140960795 + 1347512 * 2 ^ 59
def prefixEnd_1347512 : Nat := 4983230072969 + 3 ^ 40 * 1347512 * 2
def baseEnd_1347512 : Nat := 691921343701437086802911

theorem tailTrace_1347512 : CollatzResearch.WordTrace tailWord_1347512 prefixEnd_1347512 691921343701437086802911 := by
  unfold tailWord_1347512
  simp only [CollatzResearch.WordTrace]
  refine ⟨24573900147100817786294395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32765200196134423715059193 24573900147100817786294395)
  ·
    refine ⟨36860850220651226679441593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24573900147100817786294395 36860850220651226679441593)
    ·
      refine ⟨27645637665488420009581195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36860850220651226679441593 27645637665488420009581195)
      ·
        refine ⟨41468456498232630014371793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27645637665488420009581195 41468456498232630014371793)
        ·
          refine ⟨31101342373674472510778845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41468456498232630014371793 31101342373674472510778845)
          ·
            refine ⟨11663003390127927191542067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31101342373674472510778845 11663003390127927191542067)
            ·
              refine ⟨17494505085191890787313101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11663003390127927191542067 17494505085191890787313101)
              ·
                refine ⟨6560439406946959045242413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17494505085191890787313101 6560439406946959045242413)
                ·
                  refine ⟨2460164777605109641965905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6560439406946959045242413 2460164777605109641965905)
                  ·
                    refine ⟨1845123583203832231474429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2460164777605109641965905 1845123583203832231474429)
                    ·
                      refine ⟨691921343701437086802911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1845123583203832231474429 691921343701437086802911)
                      ·
                        rfl

theorem cell23_1347512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_1347512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347512 prefixEnd_1347512 := by exact prefixLift 1347512
  have htrace : WordTrace (prefixWord ++ tailWord_1347512) baseStart_1347512 baseEnd_1347512 := by
    simpa [prefixWord, tailWord_1347512, baseEnd_1347512] using wordTrace_append hprefix tailTrace_1347512
  have hstable : (prefixWord ++ tailWord_1347512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347512).length < 2 ^ (prefixWord ++ tailWord_1347512).sum := by decide
  have hdescent : baseEnd_1347512 < baseStart_1347512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347620 : List Nat := [2, 3, 1, 4, 2, 2, 1, 2, 1, 3, 2]
def baseStart_1347620 : Nat := 118140960795 + 1347620 * 2 ^ 59
def prefixEnd_1347620 : Nat := 4983230072969 + 3 ^ 40 * 1347620 * 2
def baseEnd_1347620 : Nat := 691976799612122664252415

theorem tailTrace_1347620 : CollatzResearch.WordTrace tailWord_1347620 prefixEnd_1347620 691976799612122664252415 := by
  unfold tailWord_1347620
  simp only [CollatzResearch.WordTrace]
  refine ⟨24575869688905185008760157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32767826251873580011680209 24575869688905185008760157)
  ·
    refine ⟨9215951133339444378285059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24575869688905185008760157 9215951133339444378285059)
    ·
      refine ⟨13823926700009166567427589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9215951133339444378285059 13823926700009166567427589)
      ·
        refine ⟨2591986256251718731392673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13823926700009166567427589 2591986256251718731392673)
        ·
          refine ⟨1943989692188789048544505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2591986256251718731392673 1943989692188789048544505)
          ·
            refine ⟨1457992269141591786408379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1943989692188789048544505 1457992269141591786408379)
            ·
              refine ⟨2186988403712387679612569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457992269141591786408379 2186988403712387679612569)
              ·
                refine ⟨1640241302784290759709427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186988403712387679612569 1640241302784290759709427)
                ·
                  refine ⟨2460361954176436139564141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640241302784290759709427 2460361954176436139564141)
                  ·
                    refine ⟨922635732816163552336553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2460361954176436139564141 922635732816163552336553)
                    ·
                      refine ⟨691976799612122664252415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922635732816163552336553 691976799612122664252415)
                      ·
                        rfl

theorem cell23_1347620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_1347620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347620 prefixEnd_1347620 := by exact prefixLift 1347620
  have htrace : WordTrace (prefixWord ++ tailWord_1347620) baseStart_1347620 baseEnd_1347620 := by
    simpa [prefixWord, tailWord_1347620, baseEnd_1347620] using wordTrace_append hprefix tailTrace_1347620
  have hstable : (prefixWord ++ tailWord_1347620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347620).length < 2 ^ (prefixWord ++ tailWord_1347620).sum := by decide
  have hdescent : baseEnd_1347620 < baseStart_1347620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347666 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_1347666 : Nat := 118140960795 + 1347666 * 2 ^ 59
def prefixEnd_1347666 : Nat := 4983230072969 + 3 ^ 40 * 1347666 * 2
def baseEnd_1347666 : Nat := 692000419722229484277203

theorem tailTrace_1347666 : CollatzResearch.WordTrace tailWord_1347666 prefixEnd_1347666 692000419722229484277203 := by
  unfold tailWord_1347666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12288354283910929968423713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32768944757095813249129901 12288354283910929968423713)
  ·
    refine ⟨9216265712933197476317785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12288354283910929968423713 9216265712933197476317785)
    ·
      refine ⟨6912199284699898107238339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9216265712933197476317785 6912199284699898107238339)
      ·
        refine ⟨10368298927049847160857509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6912199284699898107238339 10368298927049847160857509)
        ·
          refine ⟨1944056048821846342660783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10368298927049847160857509 1944056048821846342660783)
          ·
            refine ⟨2916084073232769513991175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944056048821846342660783 2916084073232769513991175)
            ·
              refine ⟨4374126109849154270986763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916084073232769513991175 4374126109849154270986763)
              ·
                refine ⟨6561189164773731406480145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4374126109849154270986763 6561189164773731406480145)
                ·
                  refine ⟨4920891873580298554860109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6561189164773731406480145 4920891873580298554860109)
                  ·
                    refine ⟨1845334452592611958072541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4920891873580298554860109 1845334452592611958072541)
                    ·
                      refine ⟨692000419722229484277203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1845334452592611958072541 692000419722229484277203)
                      ·
                        rfl

theorem cell23_1347666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_1347666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347666 prefixEnd_1347666 := by exact prefixLift 1347666
  have htrace : WordTrace (prefixWord ++ tailWord_1347666) baseStart_1347666 baseEnd_1347666 := by
    simpa [prefixWord, tailWord_1347666, baseEnd_1347666] using wordTrace_append hprefix tailTrace_1347666
  have hstable : (prefixWord ++ tailWord_1347666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347666).length < 2 ^ (prefixWord ++ tailWord_1347666).sum := by decide
  have hdescent : baseEnd_1347666 < baseStart_1347666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347689 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 1, 6, 2]
def baseStart_1347689 : Nat := 118140960795 + 1347689 * 2 ^ 59
def prefixEnd_1347689 : Nat := 4983230072969 + 3 ^ 40 * 1347689 * 2
def baseEnd_1347689 : Nat := 692012229777282894289597

theorem tailTrace_1347689 : CollatzResearch.WordTrace tailWord_1347689 prefixEnd_1347689 692012229777282894289597 := by
  unfold tailWord_1347689
  simp only [CollatzResearch.WordTrace]
  refine ⟨49154256014560394801782121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32769504009706929867854747 49154256014560394801782121)
  ·
    refine ⟨36865692010920296101336591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49154256014560394801782121 36865692010920296101336591)
    ·
      refine ⟨55298538016380444152004887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36865692010920296101336591 55298538016380444152004887)
      ·
        refine ⟨82947807024570666228007331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55298538016380444152004887 82947807024570666228007331)
        ·
          refine ⟨124421710536855999342010997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82947807024570666228007331 124421710536855999342010997)
          ·
            refine ⟨11664535362830249938313531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124421710536855999342010997 11664535362830249938313531)
            ·
              refine ⟨17496803044245374907470297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11664535362830249938313531 17496803044245374907470297)
              ·
                refine ⟨13122602283184031180602723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17496803044245374907470297 13122602283184031180602723)
                ·
                  refine ⟨19683903424776046770904085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13122602283184031180602723 19683903424776046770904085)
                  ·
                    refine ⟨922682973036377192386129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19683903424776046770904085 922682973036377192386129)
                    ·
                      refine ⟨692012229777282894289597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922682973036377192386129 692012229777282894289597)
                      ·
                        rfl

theorem cell23_1347689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 6, 2].length) (baseStart_1347689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347689 prefixEnd_1347689 := by exact prefixLift 1347689
  have htrace : WordTrace (prefixWord ++ tailWord_1347689) baseStart_1347689 baseEnd_1347689 := by
    simpa [prefixWord, tailWord_1347689, baseEnd_1347689] using wordTrace_append hprefix tailTrace_1347689
  have hstable : (prefixWord ++ tailWord_1347689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347689).length < 2 ^ (prefixWord ++ tailWord_1347689).sum := by decide
  have hdescent : baseEnd_1347689 < baseStart_1347689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347716 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_1347716 : Nat := 118140960795 + 1347716 * 2 ^ 59
def prefixEnd_1347716 : Nat := 4983230072969 + 3 ^ 40 * 1347716 * 2
def baseEnd_1347716 : Nat := 230675364584984762883991

theorem tailTrace_1347716 : CollatzResearch.WordTrace tailWord_1347716 prefixEnd_1347716 230675364584984762883991 := by
  unfold tailWord_1347716
  simp only [CollatzResearch.WordTrace]
  refine ⟨24577620392731289206507501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32770160523641718942010001 24577620392731289206507501)
  ·
    refine ⟨9216607647274233452440313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24577620392731289206507501 9216607647274233452440313)
    ·
      refine ⟨6912455735455675089330235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9216607647274233452440313 6912455735455675089330235)
      ·
        refine ⟨10368683603183512633995353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6912455735455675089330235 10368683603183512633995353)
        ·
          refine ⟨7776512702387634475496515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10368683603183512633995353 7776512702387634475496515)
          ·
            refine ⟨11664769053581451713244773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7776512702387634475496515 11664769053581451713244773)
            ·
              refine ⟨2187144197546522196233395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11664769053581451713244773 2187144197546522196233395)
              ·
                refine ⟨3280716296319783294350093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187144197546522196233395 3280716296319783294350093)
                ·
                  refine ⟨1230268611119918735381285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3280716296319783294350093 1230268611119918735381285)
                  ·
                    refine ⟨230675364584984762883991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1230268611119918735381285 230675364584984762883991)
                    ·
                      rfl

theorem cell23_1347716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_1347716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347716 prefixEnd_1347716 := by exact prefixLift 1347716
  have htrace : WordTrace (prefixWord ++ tailWord_1347716) baseStart_1347716 baseEnd_1347716 := by
    simpa [prefixWord, tailWord_1347716, baseEnd_1347716] using wordTrace_append hprefix tailTrace_1347716
  have hstable : (prefixWord ++ tailWord_1347716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347716).length < 2 ^ (prefixWord ++ tailWord_1347716).sum := by decide
  have hdescent : baseEnd_1347716 < baseStart_1347716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347816 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_1347816 : Nat := 118140960795 + 1347816 * 2 ^ 59
def prefixEnd_1347816 : Nat := 4983230072969 + 3 ^ 40 * 1347816 * 2
def baseEnd_1347816 : Nat := 692077441820403897401513

theorem tailTrace_1347816 : CollatzResearch.WordTrace tailWord_1347816 prefixEnd_1347816 692077441820403897401513 := by
  unfold tailWord_1347816
  simp only [CollatzResearch.WordTrace]
  refine ⟨24579444042550147745827651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32772592056733530327770201 24579444042550147745827651)
  ·
    refine ⟨36869166063825221618741477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24579444042550147745827651 36869166063825221618741477)
    ·
      refine ⟨6912968636967229053514027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36869166063825221618741477 6912968636967229053514027)
      ·
        refine ⟨10369452955450843580271041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6912968636967229053514027 10369452955450843580271041)
        ·
          refine ⟨7777089716588132685203281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10369452955450843580271041 7777089716588132685203281)
          ·
            refine ⟨5832817287441099513902461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7777089716588132685203281 5832817287441099513902461)
            ·
              refine ⟨2187306482790412317713423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5832817287441099513902461 2187306482790412317713423)
              ·
                refine ⟨3280959724185618476570135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187306482790412317713423 3280959724185618476570135)
                ·
                  refine ⟨4921439586278427714855203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3280959724185618476570135 4921439586278427714855203)
                  ·
                    refine ⟨7382159379417641572282805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4921439586278427714855203 7382159379417641572282805)
                    ·
                      refine ⟨692077441820403897401513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7382159379417641572282805 692077441820403897401513)
                      ·
                        rfl

theorem cell23_1347816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_1347816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347816 prefixEnd_1347816 := by exact prefixLift 1347816
  have htrace : WordTrace (prefixWord ++ tailWord_1347816) baseStart_1347816 baseEnd_1347816 := by
    simpa [prefixWord, tailWord_1347816, baseEnd_1347816] using wordTrace_append hprefix tailTrace_1347816
  have hstable : (prefixWord ++ tailWord_1347816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347816).length < 2 ^ (prefixWord ++ tailWord_1347816).sum := by decide
  have hdescent : baseEnd_1347816 < baseStart_1347816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347823 : List Nat := [1, 1, 2, 1, 6, 2, 2, 2, 2, 4]
def baseStart_1347823 : Nat := 118140960795 + 1347823 * 2 ^ 59
def prefixEnd_1347823 : Nat := 4983230072969 + 3 ^ 40 * 1347823 * 2
def baseEnd_1347823 : Nat := 230693678728328456671327

theorem tailTrace_1347823 : CollatzResearch.WordTrace tailWord_1347823 prefixEnd_1347823 230693678728328456671327 := by
  unfold tailWord_1347823
  simp only [CollatzResearch.WordTrace]
  refine ⟨49159143396074935687160123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32772762264049957124773415 49159143396074935687160123)
  ·
    refine ⟨73738715094112403530740185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49159143396074935687160123 73738715094112403530740185)
    ·
      refine ⟨55304036320584302648055139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73738715094112403530740185 55304036320584302648055139)
      ·
        refine ⟨82956054480876453972082709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55304036320584302648055139 82956054480876453972082709)
        ·
          refine ⟨3888565053791083779941377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82956054480876453972082709 3888565053791083779941377)
          ·
            refine ⟨2916423790343312834956033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3888565053791083779941377 2916423790343312834956033)
            ·
              refine ⟨2187317842757484626217025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2916423790343312834956033 2187317842757484626217025)
              ·
                refine ⟨1640488382068113469662769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187317842757484626217025 1640488382068113469662769)
                ·
                  refine ⟨1230366286551085102247077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1640488382068113469662769 1230366286551085102247077)
                  ·
                    refine ⟨230693678728328456671327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1230366286551085102247077 230693678728328456671327)
                    ·
                      rfl

theorem cell23_1347823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 4].length) (baseStart_1347823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347823 prefixEnd_1347823 := by exact prefixLift 1347823
  have htrace : WordTrace (prefixWord ++ tailWord_1347823) baseStart_1347823 baseEnd_1347823 := by
    simpa [prefixWord, tailWord_1347823, baseEnd_1347823] using wordTrace_append hprefix tailTrace_1347823
  have hstable : (prefixWord ++ tailWord_1347823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347823).length < 2 ^ (prefixWord ++ tailWord_1347823).sum := by decide
  have hdescent : baseEnd_1347823 < baseStart_1347823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347836 : List Nat := [2, 2, 2, 1, 4, 3, 1, 8]
def baseStart_1347836 : Nat := 118140960795 + 1347836 * 2 ^ 59
def prefixEnd_1347836 : Nat := 4983230072969 + 3 ^ 40 * 1347836 * 2
def baseEnd_1347836 : Nat := 25632878201240511820423

theorem tailTrace_1347836 : CollatzResearch.WordTrace tailWord_1347836 prefixEnd_1347836 25632878201240511820423 := by
  unfold tailWord_1347836
  simp only [CollatzResearch.WordTrace]
  refine ⟨24579808772513919453691681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32773078363351892604922241 24579808772513919453691681)
  ·
    refine ⟨18434856579385439590268761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24579808772513919453691681 18434856579385439590268761)
    ·
      refine ⟨13826142434539079692701571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18434856579385439590268761 13826142434539079692701571)
      ·
        refine ⟨20739213651808619539052357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13826142434539079692701571 20739213651808619539052357)
        ·
          refine ⟨3888602559714116163572317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20739213651808619539052357 3888602559714116163572317)
          ·
            refine ⟨1458225959892793561339619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3888602559714116163572317 1458225959892793561339619)
            ·
              refine ⟨2187338939839190342009429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458225959892793561339619 2187338939839190342009429)
              ·
                refine ⟨25632878201240511820423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2187338939839190342009429 25632878201240511820423)
                ·
                  rfl

theorem cell23_1347836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 8].length) (baseStart_1347836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347836 prefixEnd_1347836 := by exact prefixLift 1347836
  have htrace : WordTrace (prefixWord ++ tailWord_1347836) baseStart_1347836 baseEnd_1347836 := by
    simpa [prefixWord, tailWord_1347836, baseEnd_1347836] using wordTrace_append hprefix tailTrace_1347836
  have hstable : (prefixWord ++ tailWord_1347836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347836).length < 2 ^ (prefixWord ++ tailWord_1347836).sum := by decide
  have hdescent : baseEnd_1347836 < baseStart_1347836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347847 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 3, 2, 2]
def baseStart_1347847 : Nat := 118140960795 + 1347847 * 2 ^ 59
def prefixEnd_1347847 : Nat := 4983230072969 + 3 ^ 40 * 1347847 * 2
def baseEnd_1347847 : Nat := 692093359720693276113871

theorem tailTrace_1347847 : CollatzResearch.WordTrace tailWord_1347847 prefixEnd_1347847 692093359720693276113871 := by
  unfold tailWord_1347847
  simp only [CollatzResearch.WordTrace]
  refine ⟨49160018747987987786033795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32773345831991991857355863 49160018747987987786033795)
  ·
    refine ⟨73740028121981981679050693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49160018747987987786033795 73740028121981981679050693)
    ·
      refine ⟨13826255272871621564822005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73740028121981981679050693 13826255272871621564822005)
      ·
        refine ⟨1296211431831714521702063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13826255272871621564822005 1296211431831714521702063)
        ·
          refine ⟨1944317147747571782553095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1296211431831714521702063 1944317147747571782553095)
          ·
            refine ⟨2916475721621357673829643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944317147747571782553095 2916475721621357673829643)
            ·
              refine ⟨4374713582432036510744465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916475721621357673829643 4374713582432036510744465)
              ·
                refine ⟨3281035186824027383058349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4374713582432036510744465 3281035186824027383058349)
                ·
                  refine ⟨1230388195059010268646881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3281035186824027383058349 1230388195059010268646881)
                  ·
                    refine ⟨922791146294257701485161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1230388195059010268646881 922791146294257701485161)
                    ·
                      refine ⟨692093359720693276113871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922791146294257701485161 692093359720693276113871)
                      ·
                        rfl

theorem cell23_1347847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_1347847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347847 prefixEnd_1347847 := by exact prefixLift 1347847
  have htrace : WordTrace (prefixWord ++ tailWord_1347847) baseStart_1347847 baseEnd_1347847 := by
    simpa [prefixWord, tailWord_1347847, baseEnd_1347847] using wordTrace_append hprefix tailTrace_1347847
  have hstable : (prefixWord ++ tailWord_1347847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347847).length < 2 ^ (prefixWord ++ tailWord_1347847).sum := by decide
  have hdescent : baseEnd_1347847 < baseStart_1347847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347880 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_1347880 : Nat := 118140960795 + 1347880 * 2 ^ 59
def prefixEnd_1347880 : Nat := 4983230072969 + 3 ^ 40 * 1347880 * 2
def baseEnd_1347880 : Nat := 692110304582291647001219

theorem tailTrace_1347880 : CollatzResearch.WordTrace tailWord_1347880 prefixEnd_1347880 692110304582291647001219 := by
  unfold tailWord_1347880
  simp only [CollatzResearch.WordTrace]
  refine ⟨24580611178434217210992547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32774148237912289614656729 24580611178434217210992547)
  ·
    refine ⟨36870916767651325816488821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24580611178434217210992547 36870916767651325816488821)
    ·
      refine ⟨3456648446967311795295827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36870916767651325816488821 3456648446967311795295827)
      ·
        refine ⟨5184972670450967692943741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3456648446967311795295827 5184972670450967692943741)
        ·
          refine ⟨1944364751419112884853903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5184972670450967692943741 1944364751419112884853903)
          ·
            refine ⟨2916547127128669327280855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944364751419112884853903 2916547127128669327280855)
            ·
              refine ⟨4374820690693003990921283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916547127128669327280855 4374820690693003990921283)
              ·
                refine ⟨6562231036039505986381925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4374820690693003990921283 6562231036039505986381925)
                ·
                  refine ⟨1230418319257407372446611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6562231036039505986381925 1230418319257407372446611)
                  ·
                    refine ⟨1845627478886111058669917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1230418319257407372446611 1845627478886111058669917)
                    ·
                      refine ⟨692110304582291647001219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1845627478886111058669917 692110304582291647001219)
                      ·
                        rfl

theorem cell23_1347880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_1347880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347880 prefixEnd_1347880 := by exact prefixLift 1347880
  have htrace : WordTrace (prefixWord ++ tailWord_1347880) baseStart_1347880 baseEnd_1347880 := by
    simpa [prefixWord, tailWord_1347880, baseEnd_1347880] using wordTrace_append hprefix tailTrace_1347880
  have hstable : (prefixWord ++ tailWord_1347880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347880).length < 2 ^ (prefixWord ++ tailWord_1347880).sum := by decide
  have hdescent : baseEnd_1347880 < baseStart_1347880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347897 : List Nat := [1, 2, 1, 6, 1, 2, 3, 1, 2, 1, 3]
def baseStart_1347897 : Nat := 118140960795 + 1347897 * 2 ^ 59
def prefixEnd_1347897 : Nat := 4983230072969 + 3 ^ 40 * 1347897 * 2
def baseEnd_1347897 : Nat := 692119033753418080488641

theorem tailTrace_1347897 : CollatzResearch.WordTrace tailWord_1347897 prefixEnd_1347897 692119033753418080488641 := by
  unfold tailWord_1347897
  simp only [CollatzResearch.WordTrace]
  refine ⟨49161842397806846325353945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32774561598537897550235963 49161842397806846325353945)
  ·
    refine ⟨36871381798355134744015459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49161842397806846325353945 36871381798355134744015459)
    ·
      refine ⟨55307072697532702116023189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36871381798355134744015459 55307072697532702116023189)
      ·
        refine ⟨2592519032696845411688587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55307072697532702116023189 2592519032696845411688587)
        ·
          refine ⟨3888778549045268117532881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2592519032696845411688587 3888778549045268117532881)
          ·
            refine ⟨2916583911783951088149661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3888778549045268117532881 2916583911783951088149661)
            ·
              refine ⟨1093718966918981658056123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2916583911783951088149661 1093718966918981658056123)
              ·
                refine ⟨1640578450378472487084185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093718966918981658056123 1640578450378472487084185)
                ·
                  refine ⟨1230433837783854365313139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1640578450378472487084185 1230433837783854365313139)
                  ·
                    refine ⟨1845650756675781547969709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1230433837783854365313139 1845650756675781547969709)
                    ·
                      refine ⟨692119033753418080488641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1845650756675781547969709 692119033753418080488641)
                      ·
                        rfl

theorem cell23_1347897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_1347897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347897 prefixEnd_1347897 := by exact prefixLift 1347897
  have htrace : WordTrace (prefixWord ++ tailWord_1347897) baseStart_1347897 baseEnd_1347897 := by
    simpa [prefixWord, tailWord_1347897, baseEnd_1347897] using wordTrace_append hprefix tailTrace_1347897
  have hstable : (prefixWord ++ tailWord_1347897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347897).length < 2 ^ (prefixWord ++ tailWord_1347897).sum := by decide
  have hdescent : baseEnd_1347897 < baseStart_1347897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347943 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 7]
def baseStart_1347943 : Nat := 118140960795 + 1347943 * 2 ^ 59
def prefixEnd_1347943 : Nat := 4983230072969 + 3 ^ 40 * 1347943 * 2
def baseEnd_1347943 : Nat := 76904739318169433390381

theorem tailTrace_1347943 : CollatzResearch.WordTrace tailWord_1347943 prefixEnd_1347943 76904739318169433390381 := by
  unfold tailWord_1347943
  simp only [CollatzResearch.WordTrace]
  refine ⟨49163520155640196181528483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32775680103760130787685655 49163520155640196181528483)
  ·
    refine ⟨73745280233460294272292725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49163520155640196181528483 73745280233460294272292725)
    ·
      refine ⟨6913620021886902588027443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73745280233460294272292725 6913620021886902588027443)
      ·
        refine ⟨10370430032830353882041165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6913620021886902588027443 10370430032830353882041165)
        ·
          refine ⟨3888911262311382705765437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10370430032830353882041165 3888911262311382705765437)
          ·
            refine ⟨1458341723366768514662039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3888911262311382705765437 1458341723366768514662039)
            ·
              refine ⟨2187512585050152771993059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458341723366768514662039 2187512585050152771993059)
              ·
                refine ⟨3281268877575229157989589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187512585050152771993059 3281268877575229157989589)
                ·
                  refine ⟨76904739318169433390381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3281268877575229157989589 76904739318169433390381)
                  ·
                    rfl

theorem cell23_1347943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 7].length) (baseStart_1347943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347943 prefixEnd_1347943 := by exact prefixLift 1347943
  have htrace : WordTrace (prefixWord ++ tailWord_1347943) baseStart_1347943 baseEnd_1347943 := by
    simpa [prefixWord, tailWord_1347943, baseEnd_1347943] using wordTrace_append hprefix tailTrace_1347943
  have hstable : (prefixWord ++ tailWord_1347943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347943).length < 2 ^ (prefixWord ++ tailWord_1347943).sum := by decide
  have hdescent : baseEnd_1347943 < baseStart_1347943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347954 : List Nat := [3, 2, 1, 2, 1, 5, 2, 1, 2, 2, 2]
def baseStart_1347954 : Nat := 118140960795 + 1347954 * 2 ^ 59
def prefixEnd_1347954 : Nat := 4983230072969 + 3 ^ 40 * 1347954 * 2
def baseEnd_1347954 : Nat := 692148302150724357475879

theorem tailTrace_1347954 : CollatzResearch.WordTrace tailWord_1347954 prefixEnd_1347954 692148302150724357475879 := by
  unfold tailWord_1347954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12290980339650086265044729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32775947572400230040119277 12290980339650086265044729)
  ·
    refine ⟨9218235254737564698783547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12290980339650086265044729 9218235254737564698783547)
    ·
      refine ⟨13827352882106347048175321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9218235254737564698783547 13827352882106347048175321)
      ·
        refine ⟨10370514661579760286131491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13827352882106347048175321 10370514661579760286131491)
        ·
          refine ⟨15555771992369640429197237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10370514661579760286131491 15555771992369640429197237)
          ·
            refine ⟨1458353624284653790237241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15555771992369640429197237 1458353624284653790237241)
            ·
              refine ⟨1093765218213490342677931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1458353624284653790237241 1093765218213490342677931)
              ·
                refine ⟨1640647827320235514016897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093765218213490342677931 1640647827320235514016897)
                ·
                  refine ⟨1230485870490176635512673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1640647827320235514016897 1230485870490176635512673)
                  ·
                    refine ⟨922864402867632476634505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1230485870490176635512673 922864402867632476634505)
                    ·
                      refine ⟨692148302150724357475879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922864402867632476634505 692148302150724357475879)
                      ·
                        rfl

theorem cell23_1347954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_1347954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347954 prefixEnd_1347954 := by exact prefixLift 1347954
  have htrace : WordTrace (prefixWord ++ tailWord_1347954) baseStart_1347954 baseEnd_1347954 := by
    simpa [prefixWord, tailWord_1347954, baseEnd_1347954] using wordTrace_append hprefix tailTrace_1347954
  have hstable : (prefixWord ++ tailWord_1347954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347954).length < 2 ^ (prefixWord ++ tailWord_1347954).sum := by decide
  have hdescent : baseEnd_1347954 < baseStart_1347954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347993 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 2, 4, 2]
def baseStart_1347993 : Nat := 118140960795 + 1347993 * 2 ^ 59
def prefixEnd_1347993 : Nat := 4983230072969 + 3 ^ 40 * 1347993 * 2
def baseEnd_1347993 : Nat := 692168327896249704888199

theorem tailTrace_1347993 : CollatzResearch.WordTrace tailWord_1347993 prefixEnd_1347993 692168327896249704888199 := by
  unfold tailWord_1347993
  simp only [CollatzResearch.WordTrace]
  refine ⟨49165343805459054720848633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32776895870306036480565755 49165343805459054720848633)
  ·
    refine ⟨36874007854094291040636475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49165343805459054720848633 36874007854094291040636475)
    ·
      refine ⟨55311011781141436560954713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36874007854094291040636475 55311011781141436560954713)
      ·
        refine ⟨41483258835856077420716035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55311011781141436560954713 41483258835856077420716035)
        ·
          refine ⟨62224888253784116131074053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41483258835856077420716035 62224888253784116131074053)
          ·
            refine ⟨11667166547584521774576385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62224888253784116131074053 11667166547584521774576385)
            ·
              refine ⟨8750374910688391330932289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11667166547584521774576385 8750374910688391330932289)
              ·
                refine ⟨6562781183016293498199217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8750374910688391330932289 6562781183016293498199217)
                ·
                  refine ⟨4922085887262220123649413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6562781183016293498199217 4922085887262220123649413)
                  ·
                    refine ⟨922891103861666273184265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4922085887262220123649413 922891103861666273184265)
                    ·
                      refine ⟨692168327896249704888199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922891103861666273184265 692168327896249704888199)
                      ·
                        rfl

theorem cell23_1347993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 4, 2].length) (baseStart_1347993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1347993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1347993 prefixEnd_1347993 := by exact prefixLift 1347993
  have htrace : WordTrace (prefixWord ++ tailWord_1347993) baseStart_1347993 baseEnd_1347993 := by
    simpa [prefixWord, tailWord_1347993, baseEnd_1347993] using wordTrace_append hprefix tailTrace_1347993
  have hstable : (prefixWord ++ tailWord_1347993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347993).length < 2 ^ (prefixWord ++ tailWord_1347993).sum := by decide
  have hdescent : baseEnd_1347993 < baseStart_1347993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348030 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_1348030 : Nat := 118140960795 + 1348030 * 2 ^ 59
def prefixEnd_1348030 : Nat := 4983230072969 + 3 ^ 40 * 1348030 * 2
def baseEnd_1348030 : Nat := 692187326680466060125529

theorem tailTrace_1348030 : CollatzResearch.WordTrace tailWord_1348030 prefixEnd_1348030 692187326680466060125529 := by
  unfold tailWord_1348030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6145836663290626254993193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32777795537550006693297029 6145836663290626254993193)
  ·
    refine ⟨4609377497467969691244895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6145836663290626254993193 4609377497467969691244895)
    ·
      refine ⟨6914066246201954536867343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4609377497467969691244895 6914066246201954536867343)
      ·
        refine ⟨10371099369302931805301015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6914066246201954536867343 10371099369302931805301015)
        ·
          refine ⟨15556649053954397707951523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10371099369302931805301015 15556649053954397707951523)
          ·
            refine ⟨23334973580931596561927285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15556649053954397707951523 23334973580931596561927285)
            ·
              refine ⟨2187653773212337177680683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23334973580931596561927285 2187653773212337177680683)
              ·
                refine ⟨3281480659818505766521025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187653773212337177680683 3281480659818505766521025)
                ·
                  refine ⟨2461110494863879324890769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3281480659818505766521025 2461110494863879324890769)
                  ·
                    refine ⟨1845832871147909493668077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2461110494863879324890769 1845832871147909493668077)
                    ·
                      refine ⟨692187326680466060125529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1845832871147909493668077 692187326680466060125529)
                      ·
                        rfl

theorem cell23_1348030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_1348030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348030 prefixEnd_1348030 := by exact prefixLift 1348030
  have htrace : WordTrace (prefixWord ++ tailWord_1348030) baseStart_1348030 baseEnd_1348030 := by
    simpa [prefixWord, tailWord_1348030, baseEnd_1348030] using wordTrace_append hprefix tailTrace_1348030
  have hstable : (prefixWord ++ tailWord_1348030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348030).length < 2 ^ (prefixWord ++ tailWord_1348030).sum := by decide
  have hdescent : baseEnd_1348030 < baseStart_1348030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348043 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 7, 1, 3]
def baseStart_1348043 : Nat := 118140960795 + 1348043 * 2 ^ 59
def prefixEnd_1348043 : Nat := 4983230072969 + 3 ^ 40 * 1348043 * 2
def baseEnd_1348043 : Nat := 692194001928974509262969

theorem tailTrace_1348043 : CollatzResearch.WordTrace tailWord_1348043 prefixEnd_1348043 692194001928974509262969 := by
  unfold tailWord_1348043
  simp only [CollatzResearch.WordTrace]
  refine ⟨49167167455277913260168783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32778111636851942173445855 49167167455277913260168783)
  ·
    refine ⟨73750751182916869890253175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49167167455277913260168783 73750751182916869890253175)
    ·
      refine ⟨110626126774375304835379763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73750751182916869890253175 110626126774375304835379763)
      ·
        refine ⟨165939190161562957253069645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110626126774375304835379763 165939190161562957253069645)
        ·
          refine ⟨62227196310586108969901117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165939190161562957253069645 62227196310586108969901117)
          ·
            refine ⟨23335198616469790863712919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62227196310586108969901117 23335198616469790863712919)
            ·
              refine ⟨35002797924704686295569379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23335198616469790863712919 35002797924704686295569379)
              ·
                refine ⟨52504196887057029443354069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35002797924704686295569379 52504196887057029443354069)
                ·
                  refine ⟨1230567114540399127578611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 52504196887057029443354069 1230567114540399127578611)
                  ·
                    refine ⟨1845850671810598691367917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1230567114540399127578611 1845850671810598691367917)
                    ·
                      refine ⟨692194001928974509262969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1845850671810598691367917 692194001928974509262969)
                      ·
                        rfl

theorem cell23_1348043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 1, 3].length) (baseStart_1348043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348043 prefixEnd_1348043 := by exact prefixLift 1348043
  have htrace : WordTrace (prefixWord ++ tailWord_1348043) baseStart_1348043 baseEnd_1348043 := by
    simpa [prefixWord, tailWord_1348043, baseEnd_1348043] using wordTrace_append hprefix tailTrace_1348043
  have hstable : (prefixWord ++ tailWord_1348043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348043).length < 2 ^ (prefixWord ++ tailWord_1348043).sum := by decide
  have hdescent : baseEnd_1348043 < baseStart_1348043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348050 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 8]
def baseStart_1348050 : Nat := 118140960795 + 1348050 * 2 ^ 59
def prefixEnd_1348050 : Nat := 4983230072969 + 3 ^ 40 * 1348050 * 2
def baseEnd_1348050 : Nat := 76910844032617331319493

theorem tailTrace_1348050 : CollatzResearch.WordTrace tailWord_1348050 prefixEnd_1348050 76910844032617331319493 := by
  unfold tailWord_1348050
  simp only [CollatzResearch.WordTrace]
  refine ⟨12291855691563138363918401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32778281844168368970449069 12291855691563138363918401)
  ·
    refine ⟨9218891768672353772938801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12291855691563138363918401 9218891768672353772938801)
    ·
      refine ⟨6914168826504265329704101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9218891768672353772938801 6914168826504265329704101)
      ·
        refine ⟨1296406654969549749319519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6914168826504265329704101 1296406654969549749319519)
        ·
          refine ⟨1944609982454324623979279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1296406654969549749319519 1944609982454324623979279)
          ·
            refine ⟨2916914973681486935968919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944609982454324623979279 2916914973681486935968919)
            ·
              refine ⟨4375372460522230403953379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916914973681486935968919 4375372460522230403953379)
              ·
                refine ⟨6563058690783345605930069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4375372460522230403953379 6563058690783345605930069)
                ·
                  refine ⟨76910844032617331319493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6563058690783345605930069 76910844032617331319493)
                  ·
                    rfl

theorem cell23_1348050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_1348050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348050 prefixEnd_1348050 := by exact prefixLift 1348050
  have htrace : WordTrace (prefixWord ++ tailWord_1348050) baseStart_1348050 baseEnd_1348050 := by
    simpa [prefixWord, tailWord_1348050, baseEnd_1348050] using wordTrace_append hprefix tailTrace_1348050
  have hstable : (prefixWord ++ tailWord_1348050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348050).length < 2 ^ (prefixWord ++ tailWord_1348050).sum := by decide
  have hdescent : baseEnd_1348050 < baseStart_1348050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348077 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1348077 : Nat := 118140960795 + 1348077 * 2 ^ 59
def prefixEnd_1348077 : Nat := 4983230072969 + 3 ^ 40 * 1348077 * 2
def baseEnd_1348077 : Nat := 692211460271227376237813

theorem tailTrace_1348077 : CollatzResearch.WordTrace tailWord_1348077 prefixEnd_1348077 692211460271227376237813 := by
  unfold tailWord_1348077
  simp only [CollatzResearch.WordTrace]
  refine ⟨49168407537154737066906485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32778938358103158044604323 49168407537154737066906485)
  ·
    refine ⟨4609538206608256600022483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49168407537154737066906485 4609538206608256600022483)
    ·
      refine ⟨6914307309912384900033725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4609538206608256600022483 6914307309912384900033725)
      ·
        refine ⟨2592865241217144337512647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6914307309912384900033725 2592865241217144337512647)
        ·
          refine ⟨3889297861825716506268971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2592865241217144337512647 3889297861825716506268971)
          ·
            refine ⟨5833946792738574759403457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3889297861825716506268971 5833946792738574759403457)
            ·
              refine ⟨4375460094553931069552593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5833946792738574759403457 4375460094553931069552593)
              ·
                refine ⟨3281595070915448302164445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4375460094553931069552593 3281595070915448302164445)
                ·
                  refine ⟨1230598151593293113311667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3281595070915448302164445 1230598151593293113311667)
                  ·
                    refine ⟨1845897227389939669967501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1230598151593293113311667 1845897227389939669967501)
                    ·
                      refine ⟨692211460271227376237813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1845897227389939669967501 692211460271227376237813)
                      ·
                        rfl

theorem cell23_1348077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1348077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348077 prefixEnd_1348077 := by exact prefixLift 1348077
  have htrace : WordTrace (prefixWord ++ tailWord_1348077) baseStart_1348077 baseEnd_1348077 := by
    simpa [prefixWord, tailWord_1348077, baseEnd_1348077] using wordTrace_append hprefix tailTrace_1348077
  have hstable : (prefixWord ++ tailWord_1348077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348077).length < 2 ^ (prefixWord ++ tailWord_1348077).sum := by decide
  have hdescent : baseEnd_1348077 < baseStart_1348077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348083 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 2, 6, 2]
def baseStart_1348083 : Nat := 118140960795 + 1348083 * 2 ^ 59
def prefixEnd_1348083 : Nat := 4983230072969 + 3 ^ 40 * 1348083 * 2
def baseEnd_1348083 : Nat := 692214541155154352762785

theorem tailTrace_1348083 : CollatzResearch.WordTrace tailWord_1348083 prefixEnd_1348083 692214541155154352762785 := by
  unfold tailWord_1348083
  simp only [CollatzResearch.WordTrace]
  refine ⟨49168626375133000091624903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32779084250088666727749935 49168626375133000091624903)
  ·
    refine ⟨73752939562699500137437355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49168626375133000091624903 73752939562699500137437355)
    ·
      refine ⟨110629409344049250206156033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73752939562699500137437355 110629409344049250206156033)
      ·
        refine ⟨82972057008036937654617025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110629409344049250206156033 82972057008036937654617025)
        ·
          refine ⟨62229042756027703240962769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82972057008036937654617025 62229042756027703240962769)
          ·
            refine ⟨46671782067020777430722077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62229042756027703240962769 46671782067020777430722077)
            ·
              refine ⟨17501918275132791536520779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46671782067020777430722077 17501918275132791536520779)
              ·
                refine ⟨26252877412699187304781169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17501918275132791536520779 26252877412699187304781169)
                ·
                  refine ⟨19689658059524390478585877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26252877412699187304781169 19689658059524390478585877)
                  ·
                    refine ⟨922952721540205803683713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19689658059524390478585877 922952721540205803683713)
                    ·
                      refine ⟨692214541155154352762785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 922952721540205803683713 692214541155154352762785)
                      ·
                        rfl

theorem cell23_1348083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 6, 2].length) (baseStart_1348083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348083 prefixEnd_1348083 := by exact prefixLift 1348083
  have htrace : WordTrace (prefixWord ++ tailWord_1348083) baseStart_1348083 baseEnd_1348083 := by
    simpa [prefixWord, tailWord_1348083, baseEnd_1348083] using wordTrace_append hprefix tailTrace_1348083
  have hstable : (prefixWord ++ tailWord_1348083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348083).length < 2 ^ (prefixWord ++ tailWord_1348083).sum := by decide
  have hdescent : baseEnd_1348083 < baseStart_1348083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348093 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_1348093 : Nat := 118140960795 + 1348093 * 2 ^ 59
def prefixEnd_1348093 : Nat := 4983230072969 + 3 ^ 40 * 1348093 * 2
def baseEnd_1348093 : Nat := 230739891987233104545913

theorem tailTrace_1348093 : CollatzResearch.WordTrace tailWord_1348093 prefixEnd_1348093 230739891987233104545913 := by
  unfold tailWord_1348093
  simp only [CollatzResearch.WordTrace]
  refine ⟨49168991105096771799488933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32779327403397847866325955 49168991105096771799488933)
  ·
    refine ⟨9219185832205644712404175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49168991105096771799488933 9219185832205644712404175)
    ·
      refine ⟨13828778748308467068606263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9219185832205644712404175 13828778748308467068606263)
      ·
        refine ⟨20743168122462700602909395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13828778748308467068606263 20743168122462700602909395)
        ·
          refine ⟨31114752183694050904364093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20743168122462700602909395 31114752183694050904364093)
          ·
            refine ⟨11668032068885269089136535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31114752183694050904364093 11668032068885269089136535)
            ·
              refine ⟨17502048103327903633704803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11668032068885269089136535 17502048103327903633704803)
              ·
                refine ⟨26253072154991855450557205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17502048103327903633704803 26253072154991855450557205)
                ·
                  refine ⟨1230612757265243224244869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26253072154991855450557205 1230612757265243224244869)
                  ·
                    refine ⟨230739891987233104545913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1230612757265243224244869 230739891987233104545913)
                    ·
                      rfl

theorem cell23_1348093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_1348093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348093 prefixEnd_1348093 := by exact prefixLift 1348093
  have htrace : WordTrace (prefixWord ++ tailWord_1348093) baseStart_1348093 baseEnd_1348093 := by
    simpa [prefixWord, tailWord_1348093, baseEnd_1348093] using wordTrace_append hprefix tailTrace_1348093
  have hstable : (prefixWord ++ tailWord_1348093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348093).length < 2 ^ (prefixWord ++ tailWord_1348093).sum := by decide
  have hdescent : baseEnd_1348093 < baseStart_1348093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348110 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_1348110 : Nat := 118140960795 + 1348110 * 2 ^ 59
def prefixEnd_1348110 : Nat := 4983230072969 + 3 ^ 40 * 1348110 * 2
def baseEnd_1348110 : Nat := 230742801710941915708387

theorem tailTrace_1348110 : CollatzResearch.WordTrace tailWord_1348110 prefixEnd_1348110 230742801710941915708387 := by
  unfold tailWord_1348110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6146201393254397962857223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32779740764023455801905189 6146201393254397962857223)
  ·
    refine ⟨9219302089881596944285835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6146201393254397962857223 9219302089881596944285835)
    ·
      refine ⟨13828953134822395416428753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9219302089881596944285835 13828953134822395416428753)
      ·
        refine ⟨10371714851116796562321565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13828953134822395416428753 10371714851116796562321565)
        ·
          refine ⟨3889393069168798710870587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10371714851116796562321565 3889393069168798710870587)
          ·
            refine ⟨5834089603753198066305881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3889393069168798710870587 5834089603753198066305881)
            ·
              refine ⟨4375567202814898549729411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5834089603753198066305881 4375567202814898549729411)
              ·
                refine ⟨6563350804222347824594117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4375567202814898549729411 6563350804222347824594117)
                ·
                  refine ⟨1230628275791690217111397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6563350804222347824594117 1230628275791690217111397)
                  ·
                    refine ⟨230742801710941915708387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1230628275791690217111397 230742801710941915708387)
                    ·
                      rfl

theorem cell23_1348110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_1348110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348110 prefixEnd_1348110 := by exact prefixLift 1348110
  have htrace : WordTrace (prefixWord ++ tailWord_1348110) baseStart_1348110 baseEnd_1348110 := by
    simpa [prefixWord, tailWord_1348110, baseEnd_1348110] using wordTrace_append hprefix tailTrace_1348110
  have hstable : (prefixWord ++ tailWord_1348110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348110).length < 2 ^ (prefixWord ++ tailWord_1348110).sum := by decide
  have hdescent : baseEnd_1348110 < baseStart_1348110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348167 : List Nat := [1, 1, 4, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_1348167 : Nat := 118140960795 + 1348167 * 2 ^ 59
def prefixEnd_1348167 : Nat := 4983230072969 + 3 ^ 40 * 1348167 * 2
def baseEnd_1348167 : Nat := 692257673530132024112399

theorem tailTrace_1348167 : CollatzResearch.WordTrace tailWord_1348167 prefixEnd_1348167 692257673530132024112399 := by
  unfold tailWord_1348167
  simp only [CollatzResearch.WordTrace]
  refine ⟨49171690106828682437682755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32781126737885788291788503 49171690106828682437682755)
  ·
    refine ⟨73757535160243023656524133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49171690106828682437682755 73757535160243023656524133)
    ·
      refine ⟨13829537842545566935598275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73757535160243023656524133 13829537842545566935598275)
      ·
        refine ⟨20744306763818350403397413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13829537842545566935598275 20744306763818350403397413)
        ·
          refine ⟨3889557518215940700637015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20744306763818350403397413 3889557518215940700637015)
          ·
            refine ⟨5834336277323911050955523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3889557518215940700637015 5834336277323911050955523)
            ·
              refine ⟨8751504415985866576433285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5834336277323911050955523 8751504415985866576433285)
              ·
                refine ⟨1640907077997349983081241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8751504415985866576433285 1640907077997349983081241)
                ·
                  refine ⟨1230680308498012487310931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1640907077997349983081241 1230680308498012487310931)
                  ·
                    refine ⟨1846020462747018730966397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1230680308498012487310931 1846020462747018730966397)
                    ·
                      refine ⟨692257673530132024112399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1846020462747018730966397 692257673530132024112399)
                      ·
                        rfl

theorem cell23_1348167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_1348167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348167 prefixEnd_1348167 := by exact prefixLift 1348167
  have htrace : WordTrace (prefixWord ++ tailWord_1348167) baseStart_1348167 baseEnd_1348167 := by
    simpa [prefixWord, tailWord_1348167, baseEnd_1348167] using wordTrace_append hprefix tailTrace_1348167
  have hstable : (prefixWord ++ tailWord_1348167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348167).length < 2 ^ (prefixWord ++ tailWord_1348167).sum := by decide
  have hdescent : baseEnd_1348167 < baseStart_1348167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348183 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 2, 6]
def baseStart_1348183 : Nat := 118140960795 + 1348183 * 2 ^ 59
def prefixEnd_1348183 : Nat := 4983230072969 + 3 ^ 40 * 1348183 * 2
def baseEnd_1348183 : Nat := 230755296406867987170775

theorem tailTrace_1348183 : CollatzResearch.WordTrace tailWord_1348183 prefixEnd_1348183 230755296406867987170775 := by
  unfold tailWord_1348183
  simp only [CollatzResearch.WordTrace]
  refine ⟨49172273674770717170265203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32781515783180478113510135 49172273674770717170265203)
  ·
    refine ⟨73758410512156075755397805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49172273674770717170265203 73758410512156075755397805)
    ·
      refine ⟨27659403942058528408274177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73758410512156075755397805 27659403942058528408274177)
      ·
        refine ⟨20744552956543896306205633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27659403942058528408274177 20744552956543896306205633)
        ·
          refine ⟨15558414717407922229654225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20744552956543896306205633 15558414717407922229654225)
          ·
            refine ⟨11668811038055941672240669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15558414717407922229654225 11668811038055941672240669)
            ·
              refine ⟨4375804139270978127090251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11668811038055941672240669 4375804139270978127090251)
              ·
                refine ⟨6563706208906467190635377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4375804139270978127090251 6563706208906467190635377)
                ·
                  refine ⟨4922779656679850392976533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6563706208906467190635377 4922779656679850392976533)
                  ·
                    refine ⟨230755296406867987170775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4922779656679850392976533 230755296406867987170775)
                    ·
                      rfl

theorem cell23_1348183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_1348183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348183 prefixEnd_1348183 := by exact prefixLift 1348183
  have htrace : WordTrace (prefixWord ++ tailWord_1348183) baseStart_1348183 baseEnd_1348183 := by
    simpa [prefixWord, tailWord_1348183, baseEnd_1348183] using wordTrace_append hprefix tailTrace_1348183
  have hstable : (prefixWord ++ tailWord_1348183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348183).length < 2 ^ (prefixWord ++ tailWord_1348183).sum := by decide
  have hdescent : baseEnd_1348183 < baseStart_1348183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348224 : List Nat := [2, 1, 1, 2, 1, 5, 3, 2, 2, 2, 2]
def baseStart_1348224 : Nat := 118140960795 + 1348224 * 2 ^ 59
def prefixEnd_1348224 : Nat := 4983230072969 + 3 ^ 40 * 1348224 * 2
def baseEnd_1348224 : Nat := 692286941927438301099637

theorem tailTrace_1348224 : CollatzResearch.WordTrace tailWord_1348224 prefixEnd_1348224 692286941927438301099637 := by
  unfold tailWord_1348224
  simp only [CollatzResearch.WordTrace]
  refine ⟨24586884533811090586253863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32782512711748120781671817 24586884533811090586253863)
  ·
    refine ⟨36880326800716635879380795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24586884533811090586253863 36880326800716635879380795)
    ·
      refine ⟨55320490201074953819071193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36880326800716635879380795 55320490201074953819071193)
      ·
        refine ⟨41490367650806215364303395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55320490201074953819071193 41490367650806215364303395)
        ·
          refine ⟨62235551476209323046455093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41490367650806215364303395 62235551476209323046455093)
          ·
            refine ⟨5834582950894624035605165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62235551476209323046455093 5834582950894624035605165)
            ·
              refine ⟨2187968606585484013351937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5834582950894624035605165 2187968606585484013351937)
              ·
                refine ⟨1640976454939113010013953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187968606585484013351937 1640976454939113010013953)
                ·
                  refine ⟨1230732341204334757510465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1640976454939113010013953 1230732341204334757510465)
                  ·
                    refine ⟨923049255903251068132849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1230732341204334757510465 923049255903251068132849)
                    ·
                      refine ⟨692286941927438301099637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 923049255903251068132849 692286941927438301099637)
                      ·
                        rfl

theorem cell23_1348224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 2, 2, 2].length) (baseStart_1348224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348224 prefixEnd_1348224 := by exact prefixLift 1348224
  have htrace : WordTrace (prefixWord ++ tailWord_1348224) baseStart_1348224 baseEnd_1348224 := by
    simpa [prefixWord, tailWord_1348224, baseEnd_1348224] using wordTrace_append hprefix tailTrace_1348224
  have hstable : (prefixWord ++ tailWord_1348224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348224).length < 2 ^ (prefixWord ++ tailWord_1348224).sum := by decide
  have hdescent : baseEnd_1348224 < baseStart_1348224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348243 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 4, 5]
def baseStart_1348243 : Nat := 118140960795 + 1348243 * 2 ^ 59
def prefixEnd_1348243 : Nat := 4983230072969 + 3 ^ 40 * 1348243 * 2
def baseEnd_1348243 : Nat := 230765566019957908920683

theorem tailTrace_1348243 : CollatzResearch.WordTrace tailWord_1348243 prefixEnd_1348243 230765566019957908920683 := by
  unfold tailWord_1348243
  simp only [CollatzResearch.WordTrace]
  refine ⟨49174462054553347417449383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32782974703035564944966255 49174462054553347417449383)
  ·
    refine ⟨73761693081830021126174075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49174462054553347417449383 73761693081830021126174075)
    ·
      refine ⟨110642539622745031689261113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73761693081830021126174075 110642539622745031689261113)
      ·
        refine ⟨82981904717058773766945835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110642539622745031689261113 82981904717058773766945835)
        ·
          refine ⟨124472857075588160650418753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82981904717058773766945835 124472857075588160650418753)
          ·
            refine ⟨93354642806691120487814065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124472857075588160650418753 93354642806691120487814065)
            ·
              refine ⟨70015982105018340365860549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93354642806691120487814065 70015982105018340365860549)
              ·
                refine ⟨13127996644690938818598853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70015982105018340365860549 13127996644690938818598853)
                ·
                  refine ⟨2461499370879551028487285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13127996644690938818598853 2461499370879551028487285)
                  ·
                    refine ⟨230765566019957908920683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2461499370879551028487285 230765566019957908920683)
                    ·
                      rfl

theorem cell23_1348243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 5].length) (baseStart_1348243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348243 prefixEnd_1348243 := by exact prefixLift 1348243
  have htrace : WordTrace (prefixWord ++ tailWord_1348243) baseStart_1348243 baseEnd_1348243 := by
    simpa [prefixWord, tailWord_1348243, baseEnd_1348243] using wordTrace_append hprefix tailTrace_1348243
  have hstable : (prefixWord ++ tailWord_1348243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348243).length < 2 ^ (prefixWord ++ tailWord_1348243).sum := by decide
  have hdescent : baseEnd_1348243 < baseStart_1348243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348260 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_1348260 : Nat := 118140960795 + 1348260 * 2 ^ 59
def prefixEnd_1348260 : Nat := 4983230072969 + 3 ^ 40 * 1348260 * 2
def baseEnd_1348260 : Nat := 230768475743666720083157

theorem tailTrace_1348260 : CollatzResearch.WordTrace tailWord_1348260 prefixEnd_1348260 230768475743666720083157 := by
  unfold tailWord_1348260
  simp only [CollatzResearch.WordTrace]
  refine ⟨24587541047745879660409117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32783388063661172880545489 24587541047745879660409117)
  ·
    refine ⟨9220327892904704872653419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24587541047745879660409117 9220327892904704872653419)
    ·
      refine ⟨13830491839357057308980129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9220327892904704872653419 13830491839357057308980129)
      ·
        refine ⟨10372868879517792981735097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13830491839357057308980129 10372868879517792981735097)
        ·
          refine ⟨7779651659638344736301323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10372868879517792981735097 7779651659638344736301323)
          ·
            refine ⟨11669477489457517104451985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7779651659638344736301323 11669477489457517104451985)
            ·
              refine ⟨8752108117093137828338989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11669477489457517104451985 8752108117093137828338989)
              ·
                refine ⟨3282040543909926685627121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8752108117093137828338989 3282040543909926685627121)
                ·
                  refine ⟨2461530407932445014220341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3282040543909926685627121 2461530407932445014220341)
                  ·
                    refine ⟨230768475743666720083157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2461530407932445014220341 230768475743666720083157)
                    ·
                      rfl

theorem cell23_1348260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_1348260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348260 prefixEnd_1348260 := by exact prefixLift 1348260
  have htrace : WordTrace (prefixWord ++ tailWord_1348260) baseStart_1348260 baseEnd_1348260 := by
    simpa [prefixWord, tailWord_1348260, baseEnd_1348260] using wordTrace_append hprefix tailTrace_1348260
  have hstable : (prefixWord ++ tailWord_1348260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348260).length < 2 ^ (prefixWord ++ tailWord_1348260).sum := by decide
  have hdescent : baseEnd_1348260 < baseStart_1348260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348277 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 2, 5]
def baseStart_1348277 : Nat := 118140960795 + 1348277 * 2 ^ 59
def prefixEnd_1348277 : Nat := 4983230072969 + 3 ^ 40 * 1348277 * 2
def baseEnd_1348277 : Nat := 230771385467375531245631

theorem tailTrace_1348277 : CollatzResearch.WordTrace tailWord_1348277 prefixEnd_1348277 230771385467375531245631 := by
  unfold tailWord_1348277
  simp only [CollatzResearch.WordTrace]
  refine ⟨49175702136430171224187085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32783801424286780816124723 49175702136430171224187085)
  ·
    refine ⟨18440888301161314209070157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49175702136430171224187085 18440888301161314209070157)
    ·
      refine ⟨6915333112935492828401309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18440888301161314209070157 6915333112935492828401309)
      ·
        refine ⟨2593249917350809810650491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6915333112935492828401309 2593249917350809810650491)
        ·
          refine ⟨3889874876026214715975737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2593249917350809810650491 3889874876026214715975737)
          ·
            refine ⟨2917406157019661036981803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3889874876026214715975737 2917406157019661036981803)
            ·
              refine ⟨4376109235529491555472705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2917406157019661036981803 4376109235529491555472705)
              ·
                refine ⟨3282081926647118666604529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4376109235529491555472705 3282081926647118666604529)
                ·
                  refine ⟨2461561444985338999953397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3282081926647118666604529 2461561444985338999953397)
                  ·
                    refine ⟨230771385467375531245631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2461561444985338999953397 230771385467375531245631)
                    ·
                      rfl

theorem cell23_1348277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_1348277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348277 prefixEnd_1348277 := by exact prefixLift 1348277
  have htrace : WordTrace (prefixWord ++ tailWord_1348277) baseStart_1348277 baseEnd_1348277 := by
    simpa [prefixWord, tailWord_1348277, baseEnd_1348277] using wordTrace_append hprefix tailTrace_1348277
  have hstable : (prefixWord ++ tailWord_1348277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348277).length < 2 ^ (prefixWord ++ tailWord_1348277).sum := by decide
  have hdescent : baseEnd_1348277 < baseStart_1348277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348357 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 4, 3, 2]
def baseStart_1348357 : Nat := 118140960795 + 1348357 * 2 ^ 59
def prefixEnd_1348357 : Nat := 4983230072969 + 3 ^ 40 * 1348357 * 2
def baseEnd_1348357 : Nat := 692355234854486280736525

theorem tailTrace_1348357 : CollatzResearch.WordTrace tailWord_1348357 prefixEnd_1348357 692355234854486280736525 := by
  unfold tailWord_1348357
  simp only [CollatzResearch.WordTrace]
  refine ⟨49178619976140344887099325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32785746650760229924732883 49178619976140344887099325)
  ·
    refine ⟨18441982491052629332662247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49178619976140344887099325 18441982491052629332662247)
    ·
      refine ⟨27662973736578943998993371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18441982491052629332662247 27662973736578943998993371)
      ·
        refine ⟨41494460604868415998490057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27662973736578943998993371 41494460604868415998490057)
        ·
          refine ⟨31120845453651311998867543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41494460604868415998490057 31120845453651311998867543)
          ·
            refine ⟨46681268180476967998301315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31120845453651311998867543 46681268180476967998301315)
            ·
              refine ⟨70021902270715451997451973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46681268180476967998301315 70021902270715451997451973)
              ·
                refine ⟨13129106675759147249522245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70021902270715451997451973 13129106675759147249522245)
                ·
                  refine ⟨2461707501704840109285421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13129106675759147249522245 2461707501704840109285421)
                  ·
                    refine ⟨923140313139315040982033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2461707501704840109285421 923140313139315040982033)
                    ·
                      refine ⟨692355234854486280736525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 923140313139315040982033 692355234854486280736525)
                      ·
                        rfl

theorem cell23_1348357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 3, 2].length) (baseStart_1348357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348357 prefixEnd_1348357 := by exact prefixLift 1348357
  have htrace : WordTrace (prefixWord ++ tailWord_1348357) baseStart_1348357 baseEnd_1348357 := by
    simpa [prefixWord, tailWord_1348357, baseEnd_1348357] using wordTrace_append hprefix tailTrace_1348357
  have hstable : (prefixWord ++ tailWord_1348357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348357).length < 2 ^ (prefixWord ++ tailWord_1348357).sum := by decide
  have hdescent : baseEnd_1348357 < baseStart_1348357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348384 : List Nat := [2, 1, 1, 5, 1, 2, 4, 1, 1, 5]
def baseStart_1348384 : Nat := 118140960795 + 1348384 * 2 ^ 59
def prefixEnd_1348384 : Nat := 4983230072969 + 3 ^ 40 * 1348384 * 2
def baseEnd_1348384 : Nat := 230789699610719225032967

theorem tailTrace_1348384 : CollatzResearch.WordTrace tailWord_1348384 prefixEnd_1348384 230789699610719225032967 := by
  unfold tailWord_1348384
  simp only [CollatzResearch.WordTrace]
  refine ⟨24589802373521264249166103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32786403164695018998888137 24589802373521264249166103)
  ·
    refine ⟨36884703560281896373749155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24589802373521264249166103 36884703560281896373749155)
    ·
      refine ⟨55327055340422844560623733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36884703560281896373749155 55327055340422844560623733)
      ·
        refine ⟨5186911438164641677558475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55327055340422844560623733 5186911438164641677558475)
        ·
          refine ⟨7780367157246962516337713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5186911438164641677558475 7780367157246962516337713)
          ·
            refine ⟨5835275367935221887253285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7780367157246962516337713 5835275367935221887253285)
            ·
              refine ⟨1094114131487854103859991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5835275367935221887253285 1094114131487854103859991)
              ·
                refine ⟨1641171197231781155789987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094114131487854103859991 1641171197231781155789987)
                ·
                  refine ⟨2461756795847671733684981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641171197231781155789987 2461756795847671733684981)
                  ·
                    refine ⟨230789699610719225032967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2461756795847671733684981 230789699610719225032967)
                    ·
                      rfl

theorem cell23_1348384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 1, 5].length) (baseStart_1348384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348384 prefixEnd_1348384 := by exact prefixLift 1348384
  have htrace : WordTrace (prefixWord ++ tailWord_1348384) baseStart_1348384 baseEnd_1348384 := by
    simpa [prefixWord, tailWord_1348384, baseEnd_1348384] using wordTrace_append hprefix tailTrace_1348384
  have hstable : (prefixWord ++ tailWord_1348384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348384).length < 2 ^ (prefixWord ++ tailWord_1348384).sum := by decide
  have hdescent : baseEnd_1348384 < baseStart_1348384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348398 : List Nat := [4, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_1348398 : Nat := 118140960795 + 1348398 * 2 ^ 59
def prefixEnd_1348398 : Nat := 4983230072969 + 3 ^ 40 * 1348398 * 2
def baseEnd_1348398 : Nat := 692376287561320620323837

theorem tailTrace_1348398 : CollatzResearch.WordTrace tailWord_1348398 prefixEnd_1348398 692376287561320620323837 := by
  unfold tailWord_1348398
  simp only [CollatzResearch.WordTrace]
  refine ⟨6147514421123976111167731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32786743579327872592894565 6147514421123976111167731)
  ·
    refine ⟨9221271631685964166751597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6147514421123976111167731 9221271631685964166751597)
    ·
      refine ⟨3457976861882236562531849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9221271631685964166751597 3457976861882236562531849)
      ·
        refine ⟨2593482646411677421898887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3457976861882236562531849 2593482646411677421898887)
        ·
          refine ⟨3890223969617516132848331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2593482646411677421898887 3890223969617516132848331)
          ·
            refine ⟨5835335954426274199272497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890223969617516132848331 5835335954426274199272497)
            ·
              refine ⟨4376501965819705649454373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5835335954426274199272497 4376501965819705649454373)
              ·
                refine ⟨820594118591194809272695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4376501965819705649454373 820594118591194809272695)
                ·
                  refine ⟨1230891177886792213909043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 820594118591194809272695 1230891177886792213909043)
                  ·
                    refine ⟨1846336766830188320863565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1230891177886792213909043 1846336766830188320863565)
                    ·
                      refine ⟨692376287561320620323837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1846336766830188320863565 692376287561320620323837)
                      ·
                        rfl

theorem cell23_1348398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_1348398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348398 prefixEnd_1348398 := by exact prefixLift 1348398
  have htrace : WordTrace (prefixWord ++ tailWord_1348398) baseStart_1348398 baseEnd_1348398 := by
    simpa [prefixWord, tailWord_1348398, baseEnd_1348398] using wordTrace_append hprefix tailTrace_1348398
  have hstable : (prefixWord ++ tailWord_1348398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348398).length < 2 ^ (prefixWord ++ tailWord_1348398).sum := by decide
  have hdescent : baseEnd_1348398 < baseStart_1348398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348400 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 4]
def baseStart_1348400 : Nat := 118140960795 + 1348400 * 2 ^ 59
def prefixEnd_1348400 : Nat := 4983230072969 + 3 ^ 40 * 1348400 * 2
def baseEnd_1348400 : Nat := 692377314522629612498827

theorem tailTrace_1348400 : CollatzResearch.WordTrace tailWord_1348400 prefixEnd_1348400 692377314522629612498827 := by
  unfold tailWord_1348400
  simp only [CollatzResearch.WordTrace]
  refine ⟨24590094157492281615457327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32786792209989708820609769 24590094157492281615457327)
  ·
    refine ⟨36885141236238422423185991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24590094157492281615457327 36885141236238422423185991)
    ·
      refine ⟨55327711854357633634778987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36885141236238422423185991 55327711854357633634778987)
      ·
        refine ⟨82991567781536450452168481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55327711854357633634778987 82991567781536450452168481)
        ·
          refine ⟨62243675836152337839126361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82991567781536450452168481 62243675836152337839126361)
          ·
            refine ⟨46682756877114253379344771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62243675836152337839126361 46682756877114253379344771)
            ·
              refine ⟨70024135315671380069017157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46682756877114253379344771 70024135315671380069017157)
              ·
                refine ⟨13129525371688383762940717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70024135315671380069017157 13129525371688383762940717)
                ·
                  refine ⟨4923572014383143911102769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13129525371688383762940717 4923572014383143911102769)
                  ·
                    refine ⟨3692679010787357933327077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4923572014383143911102769 3692679010787357933327077)
                    ·
                      refine ⟨692377314522629612498827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3692679010787357933327077 692377314522629612498827)
                      ·
                        rfl

theorem cell23_1348400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_1348400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348400 prefixEnd_1348400 := by exact prefixLift 1348400
  have htrace : WordTrace (prefixWord ++ tailWord_1348400) baseStart_1348400 baseEnd_1348400 := by
    simpa [prefixWord, tailWord_1348400, baseEnd_1348400] using wordTrace_append hprefix tailTrace_1348400
  have hstable : (prefixWord ++ tailWord_1348400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348400).length < 2 ^ (prefixWord ++ tailWord_1348400).sum := by decide
  have hdescent : baseEnd_1348400 < baseStart_1348400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348424 : List Nat := [2, 1, 3, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_1348424 : Nat := 118140960795 + 1348424 * 2 ^ 59
def prefixEnd_1348424 : Nat := 4983230072969 + 3 ^ 40 * 1348424 * 2
def baseEnd_1348424 : Nat := 692389638058337518598717

theorem tailTrace_1348424 : CollatzResearch.WordTrace tailWord_1348424 prefixEnd_1348424 692389638058337518598717 := by
  unfold tailWord_1348424
  simp only [CollatzResearch.WordTrace]
  refine ⟨24590531833448807664894163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32787375777931743553192217 24590531833448807664894163)
  ·
    refine ⟨36885797750173211497341245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24590531833448807664894163 36885797750173211497341245)
    ·
      refine ⟨13832174156314954311502967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36885797750173211497341245 13832174156314954311502967)
      ·
        refine ⟨20748261234472431467254451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13832174156314954311502967 20748261234472431467254451)
        ·
          refine ⟨31122391851708647200881677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20748261234472431467254451 31122391851708647200881677)
          ·
            refine ⟨11670896944390742700330629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31122391851708647200881677 11670896944390742700330629)
            ·
              refine ⟨2188293177073264256311993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11670896944390742700330629 2188293177073264256311993)
              ·
                refine ⟨1641219882804948192233995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2188293177073264256311993 1641219882804948192233995)
                ·
                  refine ⟨2461829824207422288350993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641219882804948192233995 2461829824207422288350993)
                  ·
                    refine ⟨1846372368155566716263245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2461829824207422288350993 1846372368155566716263245)
                    ·
                      refine ⟨692389638058337518598717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1846372368155566716263245 692389638058337518598717)
                      ·
                        rfl

theorem cell23_1348424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_1348424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348424 prefixEnd_1348424 := by exact prefixLift 1348424
  have htrace : WordTrace (prefixWord ++ tailWord_1348424) baseStart_1348424 baseEnd_1348424 := by
    simpa [prefixWord, tailWord_1348424, baseEnd_1348424] using wordTrace_append hprefix tailTrace_1348424
  have hstable : (prefixWord ++ tailWord_1348424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348424).length < 2 ^ (prefixWord ++ tailWord_1348424).sum := by decide
  have hdescent : baseEnd_1348424 < baseStart_1348424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348430 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_1348430 : Nat := 118140960795 + 1348430 * 2 ^ 59
def prefixEnd_1348430 : Nat := 4983230072969 + 3 ^ 40 * 1348430 * 2
def baseEnd_1348430 : Nat := 692392718942264495123689

theorem tailTrace_1348430 : CollatzResearch.WordTrace tailWord_1348430 prefixEnd_1348430 692392718942264495123689 := by
  unfold tailWord_1348430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6147660313109484794313343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32787521669917252236337829 6147660313109484794313343)
  ·
    refine ⟨9221490469664227191470015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6147660313109484794313343 9221490469664227191470015)
    ·
      refine ⟨13832235704496340787205023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9221490469664227191470015 13832235704496340787205023)
      ·
        refine ⟨20748353556744511180807535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13832235704496340787205023 20748353556744511180807535)
        ·
          refine ⟨31122530335116766771211303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20748353556744511180807535 31122530335116766771211303)
          ·
            refine ⟨46683795502675150156816955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31122530335116766771211303 46683795502675150156816955)
            ·
              refine ⟨70025693254012725235225433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46683795502675150156816955 70025693254012725235225433)
              ·
                refine ⟨52519269940509543926419075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70025693254012725235225433 52519269940509543926419075)
                ·
                  refine ⟨78778904910764315889628613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52519269940509543926419075 78778904910764315889628613)
                  ·
                    refine ⟨14771044670768309229305365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78778904910764315889628613 14771044670768309229305365)
                    ·
                      refine ⟨692392718942264495123689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14771044670768309229305365 692392718942264495123689)
                      ·
                        rfl

theorem cell23_1348430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_1348430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348430 prefixEnd_1348430 := by exact prefixLift 1348430
  have htrace : WordTrace (prefixWord ++ tailWord_1348430) baseStart_1348430 baseEnd_1348430 := by
    simpa [prefixWord, tailWord_1348430, baseEnd_1348430] using wordTrace_append hprefix tailTrace_1348430
  have hstable : (prefixWord ++ tailWord_1348430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348430).length < 2 ^ (prefixWord ++ tailWord_1348430).sum := by decide
  have hdescent : baseEnd_1348430 < baseStart_1348430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348437 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_1348437 : Nat := 118140960795 + 1348437 * 2 ^ 59
def prefixEnd_1348437 : Nat := 4983230072969 + 3 ^ 40 * 1348437 * 2
def baseEnd_1348437 : Nat := 692396313306845967736157

theorem tailTrace_1348437 : CollatzResearch.WordTrace tailWord_1348437 prefixEnd_1348437 692396313306845967736157 := by
  unfold tailWord_1348437
  simp only [CollatzResearch.WordTrace]
  refine ⟨49181537815850518550011565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32787691877233679033341043 49181537815850518550011565)
  ·
    refine ⟨18443076680943944456254337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49181537815850518550011565 18443076680943944456254337)
    ·
      refine ⟨13832307510707958342190753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18443076680943944456254337 13832307510707958342190753)
      ·
        refine ⟨10374230633030968756643065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13832307510707958342190753 10374230633030968756643065)
        ·
          refine ⟨7780672974773226567482299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10374230633030968756643065 7780672974773226567482299)
          ·
            refine ⟨11671009462159839851223449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7780672974773226567482299 11671009462159839851223449)
            ·
              refine ⟨8753257096619879888417587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11671009462159839851223449 8753257096619879888417587)
              ·
                refine ⟨13129885644929819832626381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8753257096619879888417587 13129885644929819832626381)
                ·
                  refine ⟨4923707116848682437234893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13129885644929819832626381 4923707116848682437234893)
                  ·
                    refine ⟨1846390168818255913963085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4923707116848682437234893 1846390168818255913963085)
                    ·
                      refine ⟨692396313306845967736157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1846390168818255913963085 692396313306845967736157)
                      ·
                        rfl

theorem cell23_1348437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_1348437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348437 prefixEnd_1348437 := by exact prefixLift 1348437
  have htrace : WordTrace (prefixWord ++ tailWord_1348437) baseStart_1348437 baseEnd_1348437 := by
    simpa [prefixWord, tailWord_1348437, baseEnd_1348437] using wordTrace_append hprefix tailTrace_1348437
  have hstable : (prefixWord ++ tailWord_1348437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348437).length < 2 ^ (prefixWord ++ tailWord_1348437).sum := by decide
  have hdescent : baseEnd_1348437 < baseStart_1348437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348455 : List Nat := [1, 1, 5, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_1348455 : Nat := 118140960795 + 1348455 * 2 ^ 59
def prefixEnd_1348455 : Nat := 4983230072969 + 3 ^ 40 * 1348455 * 2
def baseEnd_1348455 : Nat := 692405555958626897311075

theorem tailTrace_1348455 : CollatzResearch.WordTrace tailWord_1348455 prefixEnd_1348455 692405555958626897311075 := by
  unfold tailWord_1348455
  simp only [CollatzResearch.WordTrace]
  refine ⟨49182194329785307624166819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32788129553190205082777879 49182194329785307624166819)
  ·
    refine ⟨73773291494677961436250229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49182194329785307624166819 73773291494677961436250229)
    ·
      refine ⟨6916246077626058884648459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73773291494677961436250229 6916246077626058884648459)
      ·
        refine ⟨10374369116439088326972689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6916246077626058884648459 10374369116439088326972689)
        ·
          refine ⟨7780776837329316245229517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10374369116439088326972689 7780776837329316245229517)
          ·
            refine ⟨2917791313998493591961069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7780776837329316245229517 2917791313998493591961069)
            ·
              refine ⟨1094171742749435096985401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2917791313998493591961069 1094171742749435096985401)
              ·
                refine ⟨820628807062076322739051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1094171742749435096985401 820628807062076322739051)
                ·
                  refine ⟨1230943210593114484108577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 820628807062076322739051 1230943210593114484108577)
                  ·
                    refine ⟨923207407944835863081433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1230943210593114484108577 923207407944835863081433)
                    ·
                      refine ⟨692405555958626897311075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 923207407944835863081433 692405555958626897311075)
                      ·
                        rfl

theorem cell23_1348455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_1348455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348455 prefixEnd_1348455 := by exact prefixLift 1348455
  have htrace : WordTrace (prefixWord ++ tailWord_1348455) baseStart_1348455 baseEnd_1348455 := by
    simpa [prefixWord, tailWord_1348455, baseEnd_1348455] using wordTrace_append hprefix tailTrace_1348455
  have hstable : (prefixWord ++ tailWord_1348455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348455).length < 2 ^ (prefixWord ++ tailWord_1348455).sum := by decide
  have hdescent : baseEnd_1348455 < baseStart_1348455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348514 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1348514 : Nat := 118140960795 + 1348514 * 2 ^ 59
def prefixEnd_1348514 : Nat := 4983230072969 + 3 ^ 40 * 1348514 * 2
def baseEnd_1348514 : Nat := 692435851317242166473303

theorem tailTrace_1348514 : CollatzResearch.WordTrace tailWord_1348514 prefixEnd_1348514 692435851317242166473303 := by
  unfold tailWord_1348514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12296086559142890175141149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32789564157714373800376397 12296086559142890175141149)
  ·
    refine ⟨4611032459678583815677931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12296086559142890175141149 4611032459678583815677931)
    ·
      refine ⟨6916548689517875723516897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4611032459678583815677931 6916548689517875723516897)
      ·
        refine ⟨5187411517138406792637673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6916548689517875723516897 5187411517138406792637673)
        ·
          refine ⟨3890558637853805094478255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5187411517138406792637673 3890558637853805094478255)
          ·
            refine ⟨5835837956780707641717383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890558637853805094478255 5835837956780707641717383)
            ·
              refine ⟨8753756935171061462576075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5835837956780707641717383 8753756935171061462576075)
              ·
                refine ⟨13130635402756592193864113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8753756935171061462576075 13130635402756592193864113)
                ·
                  refine ⟨9847976552067444145398085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13130635402756592193864113 9847976552067444145398085)
                  ·
                    refine ⟨1846495603512645777262141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9847976552067444145398085 1846495603512645777262141)
                    ·
                      refine ⟨692435851317242166473303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1846495603512645777262141 692435851317242166473303)
                      ·
                        rfl

theorem cell23_1348514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1348514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348514 prefixEnd_1348514 := by exact prefixLift 1348514
  have htrace : WordTrace (prefixWord ++ tailWord_1348514) baseStart_1348514 baseEnd_1348514 := by
    simpa [prefixWord, tailWord_1348514, baseEnd_1348514] using wordTrace_append hprefix tailTrace_1348514
  have hstable : (prefixWord ++ tailWord_1348514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348514).length < 2 ^ (prefixWord ++ tailWord_1348514).sum := by decide
  have hdescent : baseEnd_1348514 < baseStart_1348514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348604 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_1348604 : Nat := 118140960795 + 1348604 * 2 ^ 59
def prefixEnd_1348604 : Nat := 4983230072969 + 3 ^ 40 * 1348604 * 2
def baseEnd_1348604 : Nat := 692482064576146814347889

theorem tailTrace_1348604 : CollatzResearch.WordTrace tailWord_1348604 prefixEnd_1348604 692482064576146814347889 := by
  unfold tailWord_1348604
  simp only [CollatzResearch.WordTrace]
  refine ⟨24593814403122753035670433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32791752537497004047560577 24593814403122753035670433)
  ·
    refine ⟨18445360802342064776752825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24593814403122753035670433 18445360802342064776752825)
    ·
      refine ⟨13834020601756548582564619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18445360802342064776752825 13834020601756548582564619)
      ·
        refine ⟨20751030902634822873846929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13834020601756548582564619 20751030902634822873846929)
        ·
          refine ⟨15563273176976117155385197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20751030902634822873846929 15563273176976117155385197)
          ·
            refine ⟨5836227441366043933269449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15563273176976117155385197 5836227441366043933269449)
            ·
              refine ⟨4377170581024532949952087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5836227441366043933269449 4377170581024532949952087)
              ·
                refine ⟨6565755871536799424928131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377170581024532949952087 6565755871536799424928131)
                ·
                  refine ⟨9848633807305199137392197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6565755871536799424928131 9848633807305199137392197)
                  ·
                    refine ⟨1846618838869724838261037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9848633807305199137392197 1846618838869724838261037)
                    ·
                      refine ⟨692482064576146814347889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1846618838869724838261037 692482064576146814347889)
                      ·
                        rfl

theorem cell23_1348604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_1348604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348604 prefixEnd_1348604 := by exact prefixLift 1348604
  have htrace : WordTrace (prefixWord ++ tailWord_1348604) baseStart_1348604 baseEnd_1348604 := by
    simpa [prefixWord, tailWord_1348604, baseEnd_1348604] using wordTrace_append hprefix tailTrace_1348604
  have hstable : (prefixWord ++ tailWord_1348604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348604).length < 2 ^ (prefixWord ++ tailWord_1348604).sum := by decide
  have hdescent : baseEnd_1348604 < baseStart_1348604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348641 : List Nat := [1, 2, 3, 2, 3, 1, 4, 1, 6]
def baseStart_1348641 : Nat := 118140960795 + 1348641 * 2 ^ 59
def prefixEnd_1348641 : Nat := 4983230072969 + 3 ^ 40 * 1348641 * 2
def baseEnd_1348641 : Nat := 76944562595595907731691

theorem tailTrace_1348641 : CollatzResearch.WordTrace tailWord_1348641 prefixEnd_1348641 76944562595595907731691 := by
  unfold tailWord_1348641
  simp only [CollatzResearch.WordTrace]
  refine ⟨49188978307111461390437777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32792652204740974260291851 49188978307111461390437777)
  ·
    refine ⟨36891733730333596042828333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49188978307111461390437777 36891733730333596042828333)
    ·
      refine ⟨13834400148875098516060625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36891733730333596042828333 13834400148875098516060625)
      ·
        refine ⟨10375800111656323887045469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13834400148875098516060625 10375800111656323887045469)
        ·
          refine ⟨3890925041871121457642051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10375800111656323887045469 3890925041871121457642051)
          ·
            refine ⟨5836387562806682186463077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890925041871121457642051 5836387562806682186463077)
            ·
              refine ⟨1094322668026252909961827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5836387562806682186463077 1094322668026252909961827)
              ·
                refine ⟨1641484002039379364942741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094322668026252909961827 1641484002039379364942741)
                ·
                  refine ⟨76944562595595907731691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1641484002039379364942741 76944562595595907731691)
                  ·
                    rfl

theorem cell23_1348641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 6].length) (baseStart_1348641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348641 prefixEnd_1348641 := by exact prefixLift 1348641
  have htrace : WordTrace (prefixWord ++ tailWord_1348641) baseStart_1348641 baseEnd_1348641 := by
    simpa [prefixWord, tailWord_1348641, baseEnd_1348641] using wordTrace_append hprefix tailTrace_1348641
  have hstable : (prefixWord ++ tailWord_1348641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348641).length < 2 ^ (prefixWord ++ tailWord_1348641).sum := by decide
  have hdescent : baseEnd_1348641 < baseStart_1348641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348697 : List Nat := [1, 2, 1, 2, 2, 1, 2, 12]
def baseStart_1348697 : Nat := 118140960795 + 1348697 * 2 ^ 59
def prefixEnd_1348697 : Nat := 4983230072969 + 3 ^ 40 * 1348697 * 2
def baseEnd_1348697 : Nat := 25649252528778331499443

theorem tailTrace_1348697 : CollatzResearch.WordTrace tailWord_1348697 prefixEnd_1348697 25649252528778331499443 := by
  unfold tailWord_1348697
  simp only [CollatzResearch.WordTrace]
  refine ⟨49191020794908582954476345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32794013863272388636317563 49191020794908582954476345)
  ·
    refine ⟨36893265596181437215857259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49191020794908582954476345 36893265596181437215857259)
    ·
      refine ⟨55339898394272155823785889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36893265596181437215857259 55339898394272155823785889)
      ·
        refine ⟨41504923795704116867839417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55339898394272155823785889 41504923795704116867839417)
        ·
          refine ⟨31128692846778087650879563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41504923795704116867839417 31128692846778087650879563)
          ·
            refine ⟨46693039270167131476319345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31128692846778087650879563 46693039270167131476319345)
            ·
              refine ⟨35019779452625348607239509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46693039270167131476319345 35019779452625348607239509)
              ·
                refine ⟨25649252528778331499443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 35019779452625348607239509 25649252528778331499443)
                ·
                  rfl

theorem cell23_1348697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 12].length) (baseStart_1348697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348697 prefixEnd_1348697 := by exact prefixLift 1348697
  have htrace : WordTrace (prefixWord ++ tailWord_1348697) baseStart_1348697 baseEnd_1348697 := by
    simpa [prefixWord, tailWord_1348697, baseEnd_1348697] using wordTrace_append hprefix tailTrace_1348697
  have hstable : (prefixWord ++ tailWord_1348697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348697).length < 2 ^ (prefixWord ++ tailWord_1348697).sum := by decide
  have hdescent : baseEnd_1348697 < baseStart_1348697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348702 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1348702 : Nat := 118140960795 + 1348702 * 2 ^ 59
def prefixEnd_1348702 : Nat := 4983230072969 + 3 ^ 40 * 1348702 * 2
def baseEnd_1348702 : Nat := 692532385680287430922439

theorem tailTrace_1348702 : CollatzResearch.WordTrace tailWord_1348702 prefixEnd_1348702 692532385680287430922439 := by
  unfold tailWord_1348702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6148900394986308601051045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32794135439926979205605573 6148900394986308601051045)
  ·
    refine ⟨1152918824059932862697071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6148900394986308601051045 1152918824059932862697071)
    ·
      refine ⟨1729378236089899294045607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1152918824059932862697071 1729378236089899294045607)
      ·
        refine ⟨2594067354134848941068411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1729378236089899294045607 2594067354134848941068411)
        ·
          refine ⟨3891101031202273411602617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2594067354134848941068411 3891101031202273411602617)
          ·
            refine ⟨2918325773401705058701963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3891101031202273411602617 2918325773401705058701963)
            ·
              refine ⟨4377488660102557588052945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2918325773401705058701963 4377488660102557588052945)
              ·
                refine ⟨3283116495076918191039709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4377488660102557588052945 3283116495076918191039709)
                ·
                  refine ⟨1231168685653844321639891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3283116495076918191039709 1231168685653844321639891)
                  ·
                    refine ⟨1846753028480766482459837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1231168685653844321639891 1846753028480766482459837)
                    ·
                      refine ⟨692532385680287430922439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1846753028480766482459837 692532385680287430922439)
                      ·
                        rfl

theorem cell23_1348702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1348702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348702 prefixEnd_1348702 := by exact prefixLift 1348702
  have htrace : WordTrace (prefixWord ++ tailWord_1348702) baseStart_1348702 baseEnd_1348702 := by
    simpa [prefixWord, tailWord_1348702, baseEnd_1348702] using wordTrace_append hprefix tailTrace_1348702
  have hstable : (prefixWord ++ tailWord_1348702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348702).length < 2 ^ (prefixWord ++ tailWord_1348702).sum := by decide
  have hdescent : baseEnd_1348702 < baseStart_1348702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348711 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_1348711 : Nat := 118140960795 + 1348711 * 2 ^ 59
def prefixEnd_1348711 : Nat := 4983230072969 + 3 ^ 40 * 1348711 * 2
def baseEnd_1348711 : Nat := 692537007006177895709897

theorem tailTrace_1348711 : CollatzResearch.WordTrace tailWord_1348711 prefixEnd_1348711 692537007006177895709897 := by
  unfold tailWord_1348711
  simp only [CollatzResearch.WordTrace]
  refine ⟨49191531416857863345485987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32794354277905242230323991 49191531416857863345485987)
  ·
    refine ⟨73787297125286795018228981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49191531416857863345485987 73787297125286795018228981)
    ·
      refine ⟨6917559105495637032958967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73787297125286795018228981 6917559105495637032958967)
      ·
        refine ⟨10376338658243455549438451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6917559105495637032958967 10376338658243455549438451)
        ·
          refine ⟨15564507987365183324157677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10376338658243455549438451 15564507987365183324157677)
          ·
            refine ⟨5836690495261943746559129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15564507987365183324157677 5836690495261943746559129)
            ·
              refine ⟨4377517871446457809919347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5836690495261943746559129 4377517871446457809919347)
              ·
                refine ⟨6566276807169686714879021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377517871446457809919347 6566276807169686714879021)
                ·
                  refine ⟨2462353802688632518079633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6566276807169686714879021 2462353802688632518079633)
                  ·
                    refine ⟨1846765352016474388559725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2462353802688632518079633 1846765352016474388559725)
                    ·
                      refine ⟨692537007006177895709897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1846765352016474388559725 692537007006177895709897)
                      ·
                        rfl

theorem cell23_1348711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_1348711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348711 prefixEnd_1348711 := by exact prefixLift 1348711
  have htrace : WordTrace (prefixWord ++ tailWord_1348711) baseStart_1348711 baseEnd_1348711 := by
    simpa [prefixWord, tailWord_1348711, baseEnd_1348711] using wordTrace_append hprefix tailTrace_1348711
  have hstable : (prefixWord ++ tailWord_1348711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348711).length < 2 ^ (prefixWord ++ tailWord_1348711).sum := by decide
  have hdescent : baseEnd_1348711 < baseStart_1348711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348712 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_1348712 : Nat := 118140960795 + 1348712 * 2 ^ 59
def prefixEnd_1348712 : Nat := 4983230072969 + 3 ^ 40 * 1348712 * 2
def baseEnd_1348712 : Nat := 692537520486832391797393

theorem tailTrace_1348712 : CollatzResearch.WordTrace tailWord_1348712 prefixEnd_1348712 692537520486832391797393 := by
  unfold tailWord_1348712
  simp only [CollatzResearch.WordTrace]
  refine ⟨24595783944927120258136195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32794378593236160344181593 24595783944927120258136195)
  ·
    refine ⟨36893675917390680387204293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24595783944927120258136195 36893675917390680387204293)
    ·
      refine ⟨6917564234510752572600805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36893675917390680387204293 6917564234510752572600805)
      ·
        refine ⟨1297043293970766107362651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6917564234510752572600805 1297043293970766107362651)
        ·
          refine ⟨1945564940956149161043977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1297043293970766107362651 1945564940956149161043977)
          ·
            refine ⟨1459173705717111870782983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1945564940956149161043977 1459173705717111870782983)
            ·
              refine ⟨2188760558575667806174475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459173705717111870782983 2188760558575667806174475)
              ·
                refine ⟨3283140837863501709261713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2188760558575667806174475 3283140837863501709261713)
                ·
                  refine ⟨2462355628397626281946285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3283140837863501709261713 2462355628397626281946285)
                  ·
                    refine ⟨923383360649109855729857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2462355628397626281946285 923383360649109855729857)
                    ·
                      refine ⟨692537520486832391797393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 923383360649109855729857 692537520486832391797393)
                      ·
                        rfl

theorem cell23_1348712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_1348712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348712 prefixEnd_1348712 := by exact prefixLift 1348712
  have htrace : WordTrace (prefixWord ++ tailWord_1348712) baseStart_1348712 baseEnd_1348712 := by
    simpa [prefixWord, tailWord_1348712, baseEnd_1348712] using wordTrace_append hprefix tailTrace_1348712
  have hstable : (prefixWord ++ tailWord_1348712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348712).length < 2 ^ (prefixWord ++ tailWord_1348712).sum := by decide
  have hdescent : baseEnd_1348712 < baseStart_1348712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348725 : List Nat := [1, 3, 4, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1348725 : Nat := 118140960795 + 1348725 * 2 ^ 59
def prefixEnd_1348725 : Nat := 4983230072969 + 3 ^ 40 * 1348725 * 2
def baseEnd_1348725 : Nat := 692544195735340840934833

theorem tailTrace_1348725 : CollatzResearch.WordTrace tailWord_1348725 prefixEnd_1348725 692544195735340840934833 := by
  unfold tailWord_1348725
  simp only [CollatzResearch.WordTrace]
  refine ⟨49192042038807143736495629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32794694692538095824330419 49192042038807143736495629)
  ·
    refine ⟨18447015764552678901185861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49192042038807143736495629 18447015764552678901185861)
    ·
      refine ⟨3458815455853627293972349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18447015764552678901185861 3458815455853627293972349)
      ·
        refine ⟨1297055795945110235239631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3458815455853627293972349 1297055795945110235239631)
        ·
          refine ⟨1945583693917665352859447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1297055795945110235239631 1945583693917665352859447)
          ·
            refine ⟨2918375540876498029289171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1945583693917665352859447 2918375540876498029289171)
            ·
              refine ⟨4377563311314747043933757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2918375540876498029289171 4377563311314747043933757)
              ·
                refine ⟨1641586241743030141475159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4377563311314747043933757 1641586241743030141475159)
                ·
                  refine ⟨2462379362614545212212739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641586241743030141475159 2462379362614545212212739)
                  ·
                    refine ⟨3693569043921817818319109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2462379362614545212212739 3693569043921817818319109)
                    ·
                      refine ⟨692544195735340840934833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3693569043921817818319109 692544195735340840934833)
                      ·
                        rfl

theorem cell23_1348725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1348725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348725 prefixEnd_1348725 := by exact prefixLift 1348725
  have htrace : WordTrace (prefixWord ++ tailWord_1348725) baseStart_1348725 baseEnd_1348725 := by
    simpa [prefixWord, tailWord_1348725, baseEnd_1348725] using wordTrace_append hprefix tailTrace_1348725
  have hstable : (prefixWord ++ tailWord_1348725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348725).length < 2 ^ (prefixWord ++ tailWord_1348725).sum := by decide
  have hdescent : baseEnd_1348725 < baseStart_1348725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348728 : List Nat := [2, 1, 2, 1, 1, 1, 8, 1, 1, 2, 3]
def baseStart_1348728 : Nat := 118140960795 + 1348728 * 2 ^ 59
def prefixEnd_1348728 : Nat := 4983230072969 + 3 ^ 40 * 1348728 * 2
def baseEnd_1348728 : Nat := 692545736177304329197319

theorem tailTrace_1348728 : CollatzResearch.WordTrace tailWord_1348728 prefixEnd_1348728 692545736177304329197319 := by
  unfold tailWord_1348728
  simp only [CollatzResearch.WordTrace]
  refine ⟨24596075728898137624427419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32794767638530850165903225 24596075728898137624427419)
  ·
    refine ⟨36894113593347206436641129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24596075728898137624427419 36894113593347206436641129)
    ·
      refine ⟨27670585195010404827480847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36894113593347206436641129 27670585195010404827480847)
      ·
        refine ⟨41505877792515607241221271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27670585195010404827480847 41505877792515607241221271)
        ·
          refine ⟨62258816688773410861831907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41505877792515607241221271 62258816688773410861831907)
          ·
            refine ⟨93388225033160116292747861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62258816688773410861831907 93388225033160116292747861)
            ·
              refine ⟨1094393262107345112805639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 93388225033160116292747861 1094393262107345112805639)
              ·
                refine ⟨1641589893161017669208459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094393262107345112805639 1641589893161017669208459)
                ·
                  refine ⟨2462384839741526503812689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641589893161017669208459 2462384839741526503812689)
                  ·
                    refine ⟨1846788629806144877859517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2462384839741526503812689 1846788629806144877859517)
                    ·
                      refine ⟨692545736177304329197319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1846788629806144877859517 692545736177304329197319)
                      ·
                        rfl

theorem cell23_1348728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 1, 2, 3].length) (baseStart_1348728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348728 prefixEnd_1348728 := by exact prefixLift 1348728
  have htrace : WordTrace (prefixWord ++ tailWord_1348728) baseStart_1348728 baseEnd_1348728 := by
    simpa [prefixWord, tailWord_1348728, baseEnd_1348728] using wordTrace_append hprefix tailTrace_1348728
  have hstable : (prefixWord ++ tailWord_1348728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348728).length < 2 ^ (prefixWord ++ tailWord_1348728).sum := by decide
  have hdescent : baseEnd_1348728 < baseStart_1348728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348784 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 5]
def baseStart_1348784 : Nat := 118140960795 + 1348784 * 2 ^ 59
def prefixEnd_1348784 : Nat := 4983230072969 + 3 ^ 40 * 1348784 * 2
def baseEnd_1348784 : Nat := 692574491093956110097061

theorem tailTrace_1348784 : CollatzResearch.WordTrace tailWord_1348784 prefixEnd_1348784 692574491093956110097061 := by
  unfold tailWord_1348784
  simp only [CollatzResearch.WordTrace]
  refine ⟨24597096972796698406446703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32796129297062264541928937 24597096972796698406446703)
  ·
    refine ⟨36895645459195047609670055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24597096972796698406446703 36895645459195047609670055)
    ·
      refine ⟨55343468188792571414505083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36895645459195047609670055 55343468188792571414505083)
      ·
        refine ⟨83015202283188857121757625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55343468188792571414505083 83015202283188857121757625)
        ·
          refine ⟨62261401712391642841318219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83015202283188857121757625 62261401712391642841318219)
          ·
            refine ⟨93392102568587464261977329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62261401712391642841318219 93392102568587464261977329)
            ·
              refine ⟨70044076926440598196482997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93392102568587464261977329 70044076926440598196482997)
              ·
                refine ⟨6566632211853806080920281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70044076926440598196482997 6566632211853806080920281)
                ·
                  refine ⟨4924974158890354560690211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6566632211853806080920281 4924974158890354560690211)
                  ·
                    refine ⟨7387461238335531841035317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4924974158890354560690211 7387461238335531841035317)
                    ·
                      refine ⟨692574491093956110097061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7387461238335531841035317 692574491093956110097061)
                      ·
                        rfl

theorem cell23_1348784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_1348784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348784 prefixEnd_1348784 := by exact prefixLift 1348784
  have htrace : WordTrace (prefixWord ++ tailWord_1348784) baseStart_1348784 baseEnd_1348784 := by
    simpa [prefixWord, tailWord_1348784, baseEnd_1348784] using wordTrace_append hprefix tailTrace_1348784
  have hstable : (prefixWord ++ tailWord_1348784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348784).length < 2 ^ (prefixWord ++ tailWord_1348784).sum := by decide
  have hdescent : baseEnd_1348784 < baseStart_1348784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348785 : List Nat := [1, 2, 2, 5, 1, 1, 2, 3, 1, 3, 2]
def baseStart_1348785 : Nat := 118140960795 + 1348785 * 2 ^ 59
def prefixEnd_1348785 : Nat := 4983230072969 + 3 ^ 40 * 1348785 * 2
def baseEnd_1348785 : Nat := 692575004574610606184557

theorem tailTrace_1348785 : CollatzResearch.WordTrace tailWord_1348785 prefixEnd_1348785 692575004574610606184557 := by
  unfold tailWord_1348785
  simp only [CollatzResearch.WordTrace]
  refine ⟨49194230418589773983679809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32796153612393182655786539 49194230418589773983679809)
  ·
    refine ⟨36895672813942330487759857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49194230418589773983679809 36895672813942330487759857)
    ·
      refine ⟨27671754610456747865819893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36895672813942330487759857 27671754610456747865819893)
      ·
        refine ⟨2594226994730320112420615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27671754610456747865819893 2594226994730320112420615)
        ·
          refine ⟨3891340492095480168630923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2594226994730320112420615 3891340492095480168630923)
          ·
            refine ⟨5837010738143220252946385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3891340492095480168630923 5837010738143220252946385)
            ·
              refine ⟨4377758053607415189709789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5837010738143220252946385 4377758053607415189709789)
              ·
                refine ⟨1641659270102780696141171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4377758053607415189709789 1641659270102780696141171)
                ·
                  refine ⟨2462488905154171044211757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641659270102780696141171 2462488905154171044211757)
                  ·
                    refine ⟨923433339432814141579409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2462488905154171044211757 923433339432814141579409)
                    ·
                      refine ⟨692575004574610606184557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 923433339432814141579409 692575004574610606184557)
                      ·
                        rfl

theorem cell23_1348785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_1348785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348785 prefixEnd_1348785 := by exact prefixLift 1348785
  have htrace : WordTrace (prefixWord ++ tailWord_1348785) baseStart_1348785 baseEnd_1348785 := by
    simpa [prefixWord, tailWord_1348785, baseEnd_1348785] using wordTrace_append hprefix tailTrace_1348785
  have hstable : (prefixWord ++ tailWord_1348785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348785).length < 2 ^ (prefixWord ++ tailWord_1348785).sum := by decide
  have hdescent : baseEnd_1348785 < baseStart_1348785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348841 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 3, 7, 2]
def baseStart_1348841 : Nat := 118140960795 + 1348841 * 2 ^ 59
def prefixEnd_1348841 : Nat := 4983230072969 + 3 ^ 40 * 1348841 * 2
def baseEnd_1348841 : Nat := 692603759491262387084299

theorem tailTrace_1348841 : CollatzResearch.WordTrace tailWord_1348841 prefixEnd_1348841 692603759491262387084299 := by
  unfold tailWord_1348841
  simp only [CollatzResearch.WordTrace]
  refine ⟨49196272906386895547718377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32797515270924597031812251 49196272906386895547718377)
  ·
    refine ⟨36897204679790171660788783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49196272906386895547718377 36897204679790171660788783)
    ·
      refine ⟨55345807019685257491183175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36897204679790171660788783 55345807019685257491183175)
      ·
        refine ⟨83018710529527886236774763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55345807019685257491183175 83018710529527886236774763)
        ·
          refine ⟨124528065794291829355162145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83018710529527886236774763 124528065794291829355162145)
          ·
            refine ⟨93396049345718872016371609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124528065794291829355162145 93396049345718872016371609)
            ·
              refine ⟨70047037009289154012278707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93396049345718872016371609 70047037009289154012278707)
              ·
                refine ⟨105070555513933731018418061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70047037009289154012278707 105070555513933731018418061)
                ·
                  refine ⟨39401458317725149131906773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105070555513933731018418061 39401458317725149131906773)
                  ·
                    refine ⟨923471679321683182779065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39401458317725149131906773 923471679321683182779065)
                    ·
                      refine ⟨692603759491262387084299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 923471679321683182779065 692603759491262387084299)
                      ·
                        rfl

theorem cell23_1348841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 7, 2].length) (baseStart_1348841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348841 prefixEnd_1348841 := by exact prefixLift 1348841
  have htrace : WordTrace (prefixWord ++ tailWord_1348841) baseStart_1348841 baseEnd_1348841 := by
    simpa [prefixWord, tailWord_1348841, baseEnd_1348841] using wordTrace_append hprefix tailTrace_1348841
  have hstable : (prefixWord ++ tailWord_1348841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348841).length < 2 ^ (prefixWord ++ tailWord_1348841).sum := by decide
  have hdescent : baseEnd_1348841 < baseStart_1348841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348851 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 2, 5]
def baseStart_1348851 : Nat := 118140960795 + 1348851 * 2 ^ 59
def prefixEnd_1348851 : Nat := 4983230072969 + 3 ^ 40 * 1348851 * 2
def baseEnd_1348851 : Nat := 230869631432602449319751

theorem tailTrace_1348851 : CollatzResearch.WordTrace tailWord_1348851 prefixEnd_1348851 230869631432602449319751 := by
  unfold tailWord_1348851
  simp only [CollatzResearch.WordTrace]
  refine ⟨49196637636350667255582407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32797758424233778170388271 49196637636350667255582407)
  ·
    refine ⟨73794956454526000883373611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49196637636350667255582407 73794956454526000883373611)
    ·
      refine ⟨110692434681789001325060417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73794956454526000883373611 110692434681789001325060417)
      ·
        refine ⟨83019326011341750993795313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110692434681789001325060417 83019326011341750993795313)
        ·
          refine ⟨62264494508506313245346485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83019326011341750993795313 62264494508506313245346485)
          ·
            refine ⟨5837296360172466866751233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62264494508506313245346485 5837296360172466866751233)
            ·
              refine ⟨4377972270129350150063425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5837296360172466866751233 4377972270129350150063425)
              ·
                refine ⟨3283479202597012612547569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4377972270129350150063425 3283479202597012612547569)
                ·
                  refine ⟨2462609401947759459410677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3283479202597012612547569 2462609401947759459410677)
                  ·
                    refine ⟨230869631432602449319751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2462609401947759459410677 230869631432602449319751)
                    ·
                      rfl

theorem cell23_1348851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 5].length) (baseStart_1348851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348851 prefixEnd_1348851 := by exact prefixLift 1348851
  have htrace : WordTrace (prefixWord ++ tailWord_1348851) baseStart_1348851 baseEnd_1348851 := by
    simpa [prefixWord, tailWord_1348851, baseEnd_1348851] using wordTrace_append hprefix tailTrace_1348851
  have hstable : (prefixWord ++ tailWord_1348851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348851).length < 2 ^ (prefixWord ++ tailWord_1348851).sum := by decide
  have hdescent : baseEnd_1348851 < baseStart_1348851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348864 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 2, 8]
def baseStart_1348864 : Nat := 118140960795 + 1348864 * 2 ^ 59
def prefixEnd_1348864 : Nat := 4983230072969 + 3 ^ 40 * 1348864 * 2
def baseEnd_1348864 : Nat := 230871856515438599032231

theorem tailTrace_1348864 : CollatzResearch.WordTrace tailWord_1348864 prefixEnd_1348864 230871856515438599032231 := by
  unfold tailWord_1348864
  simp only [CollatzResearch.WordTrace]
  refine ⟨24598555892651785237902823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32798074523535713650537097 24598555892651785237902823)
  ·
    refine ⟨36897833838977677856854235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24598555892651785237902823 36897833838977677856854235)
    ·
      refine ⟨55346750758466516785281353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36897833838977677856854235 55346750758466516785281353)
      ·
        refine ⟨41510063068849887588961015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55346750758466516785281353 41510063068849887588961015)
        ·
          refine ⟨62265094603274831383441523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41510063068849887588961015 62265094603274831383441523)
          ·
            refine ⟨93397641904912247075162285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62265094603274831383441523 93397641904912247075162285)
            ·
              refine ⟨35024115714342092653185857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93397641904912247075162285 35024115714342092653185857)
              ·
                refine ⟨26268086785756569489889393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35024115714342092653185857 26268086785756569489889393)
                ·
                  refine ⟨19701065089317427117417045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26268086785756569489889393 19701065089317427117417045)
                  ·
                    refine ⟨230871856515438599032231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19701065089317427117417045 230871856515438599032231)
                    ·
                      rfl

theorem cell23_1348864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_1348864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348864 prefixEnd_1348864 := by exact prefixLift 1348864
  have htrace : WordTrace (prefixWord ++ tailWord_1348864) baseStart_1348864 baseEnd_1348864 := by
    simpa [prefixWord, tailWord_1348864, baseEnd_1348864] using wordTrace_append hprefix tailTrace_1348864
  have hstable : (prefixWord ++ tailWord_1348864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348864).length < 2 ^ (prefixWord ++ tailWord_1348864).sum := by decide
  have hdescent : baseEnd_1348864 < baseStart_1348864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348888 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 2, 1, 4]
def baseStart_1348888 : Nat := 118140960795 + 1348888 * 2 ^ 59
def prefixEnd_1348888 : Nat := 4983230072969 + 3 ^ 40 * 1348888 * 2
def baseEnd_1348888 : Nat := 692627893082023703196583

theorem tailTrace_1348888 : CollatzResearch.WordTrace tailWord_1348888 prefixEnd_1348888 692627893082023703196583 := by
  unfold tailWord_1348888
  simp only [CollatzResearch.WordTrace]
  refine ⟨24598993568608311287339659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32798658091477748383119545 24598993568608311287339659)
  ·
    refine ⟨36898490352912466931009489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24598993568608311287339659 36898490352912466931009489)
    ·
      refine ⟨27673867764684350198257117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36898490352912466931009489 27673867764684350198257117)
      ·
        refine ⟨10377700411756631324346419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27673867764684350198257117 10377700411756631324346419)
        ·
          refine ⟨15566550617634946986519629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10377700411756631324346419 15566550617634946986519629)
          ·
            refine ⟨5837456481613105119944861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15566550617634946986519629 5837456481613105119944861)
            ·
              refine ⟨2189046180604914419979323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5837456481613105119944861 2189046180604914419979323)
              ·
                refine ⟨3283569270907371629968985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2189046180604914419979323 3283569270907371629968985)
                ·
                  refine ⟨2462676953180528722476739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3283569270907371629968985 2462676953180528722476739)
                  ·
                    refine ⟨3694015429770793083715109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2462676953180528722476739 3694015429770793083715109)
                    ·
                      refine ⟨692627893082023703196583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3694015429770793083715109 692627893082023703196583)
                      ·
                        rfl

theorem cell23_1348888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_1348888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348888 prefixEnd_1348888 := by exact prefixLift 1348888
  have htrace : WordTrace (prefixWord ++ tailWord_1348888) baseStart_1348888 baseEnd_1348888 := by
    simpa [prefixWord, tailWord_1348888, baseEnd_1348888] using wordTrace_append hprefix tailTrace_1348888
  have hstable : (prefixWord ++ tailWord_1348888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348888).length < 2 ^ (prefixWord ++ tailWord_1348888).sum := by decide
  have hdescent : baseEnd_1348888 < baseStart_1348888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348901 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_1348901 : Nat := 118140960795 + 1348901 * 2 ^ 59
def prefixEnd_1348901 : Nat := 4983230072969 + 3 ^ 40 * 1348901 * 2
def baseEnd_1348901 : Nat := 692634568330532152334023

theorem tailTrace_1348901 : CollatzResearch.WordTrace tailWord_1348901 prefixEnd_1348901 692634568330532152334023 := by
  unfold tailWord_1348901
  simp only [CollatzResearch.WordTrace]
  refine ⟨49198461286169525794902557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32798974190779683863268371 49198461286169525794902557)
  ·
    refine ⟨18449422982313572173088459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49198461286169525794902557 18449422982313572173088459)
    ·
      refine ⟨27674134473470358259632689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18449422982313572173088459 27674134473470358259632689)
      ·
        refine ⟨20755600855102768694724517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27674134473470358259632689 20755600855102768694724517)
        ·
          refine ⟨3891675160331769130260847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20755600855102768694724517 3891675160331769130260847)
          ·
            refine ⟨5837512740497653695391271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3891675160331769130260847 5837512740497653695391271)
            ·
              refine ⟨8756269110746480543086907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5837512740497653695391271 8756269110746480543086907)
              ·
                refine ⟨13134403666119720814630361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8756269110746480543086907 13134403666119720814630361)
                ·
                  refine ⟨9850802749589790610972771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13134403666119720814630361 9850802749589790610972771)
                  ·
                    refine ⟨14776204124384685916459157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9850802749589790610972771 14776204124384685916459157)
                    ·
                      refine ⟨692634568330532152334023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14776204124384685916459157 692634568330532152334023)
                      ·
                        rfl

theorem cell23_1348901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_1348901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348901 prefixEnd_1348901 := by exact prefixLift 1348901
  have htrace : WordTrace (prefixWord ++ tailWord_1348901) baseStart_1348901 baseEnd_1348901 := by
    simpa [prefixWord, tailWord_1348901, baseEnd_1348901] using wordTrace_append hprefix tailTrace_1348901
  have hstable : (prefixWord ++ tailWord_1348901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348901).length < 2 ^ (prefixWord ++ tailWord_1348901).sum := by decide
  have hdescent : baseEnd_1348901 < baseStart_1348901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
