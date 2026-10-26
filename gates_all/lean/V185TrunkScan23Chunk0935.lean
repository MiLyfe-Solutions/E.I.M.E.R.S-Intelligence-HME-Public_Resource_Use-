import V185TrunkScan23Chunk0934

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5533646 : List Nat := [4, 1, 1, 1, 2, 2, 3, 9]
def baseStart_5533646 : Nat := 118140960795 + 5533646 * 2 ^ 59
def prefixEnd_5533646 : Nat := 4983230072969 + 3 ^ 40 * 5533646 * 2
def baseEnd_5533646 : Nat := 105237784067768956232453

theorem tailTrace_5533646 : CollatzResearch.WordTrace tailWord_5533646 prefixEnd_5533646 105237784067768956232453 := by
  unfold tailWord_5533646
  simp only [CollatzResearch.WordTrace]
  refine ⟨25228581313819136042615599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134552433673702058893949861 25228581313819136042615599)
  ·
    refine ⟨37842871970728704063923399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25228581313819136042615599 37842871970728704063923399)
    ·
      refine ⟨56764307956093056095885099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37842871970728704063923399 56764307956093056095885099)
      ·
        refine ⟨85146461934139584143827649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56764307956093056095885099 85146461934139584143827649)
        ·
          refine ⟨63859846450604688107870737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85146461934139584143827649 63859846450604688107870737)
          ·
            refine ⟨47894884837953516080903053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63859846450604688107870737 47894884837953516080903053)
            ·
              refine ⟨17960581814232568530338645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47894884837953516080903053 17960581814232568530338645)
              ·
                refine ⟨105237784067768956232453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17960581814232568530338645 105237784067768956232453)
                ·
                  rfl

theorem cell23_5533646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_5533646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533646 prefixEnd_5533646 := by exact prefixLift 5533646
  have htrace : WordTrace (prefixWord ++ tailWord_5533646) baseStart_5533646 baseEnd_5533646 := by
    simpa [prefixWord, tailWord_5533646, baseEnd_5533646] using wordTrace_append hprefix tailTrace_5533646
  have hstable : (prefixWord ++ tailWord_5533646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533646).length < 2 ^ (prefixWord ++ tailWord_5533646).sum := by decide
  have hdescent : baseEnd_5533646 < baseStart_5533646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533694 : List Nat := [4, 2, 2, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_5533694 : Nat := 118140960795 + 5533694 * 2 ^ 59
def prefixEnd_5533694 : Nat := 4983230072969 + 3 ^ 40 * 5533694 * 2
def baseEnd_5533694 : Nat := 2841444816901177630476011

theorem tailTrace_5533694 : CollatzResearch.WordTrace tailWord_5533694 prefixEnd_5533694 2841444816901177630476011 := by
  unfold tailWord_5533694
  simp only [CollatzResearch.WordTrace]
  refine ⟨25228800151797399067334017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134553600809586128359114757 25228800151797399067334017)
  ·
    refine ⟨18921600113848049300500513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25228800151797399067334017 18921600113848049300500513)
    ·
      refine ⟨14191200085386036975375385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18921600113848049300500513 14191200085386036975375385)
      ·
        refine ⟨10643400064039527731531539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14191200085386036975375385 10643400064039527731531539)
        ·
          refine ⟨15965100096059291597297309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10643400064039527731531539 15965100096059291597297309)
          ·
            refine ⟨5986912536022234348986491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15965100096059291597297309 5986912536022234348986491)
            ·
              refine ⟨8980368804033351523479737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5986912536022234348986491 8980368804033351523479737)
              ·
                refine ⟨6735276603025013642609803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8980368804033351523479737 6735276603025013642609803)
                ·
                  refine ⟨10102914904537520463914705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6735276603025013642609803 10102914904537520463914705)
                  ·
                    refine ⟨7577186178403140347936029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10102914904537520463914705 7577186178403140347936029)
                    ·
                      refine ⟨2841444816901177630476011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7577186178403140347936029 2841444816901177630476011)
                      ·
                        rfl

theorem cell23_5533694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_5533694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533694 prefixEnd_5533694 := by exact prefixLift 5533694
  have htrace : WordTrace (prefixWord ++ tailWord_5533694) baseStart_5533694 baseEnd_5533694 := by
    simpa [prefixWord, tailWord_5533694, baseEnd_5533694] using wordTrace_append hprefix tailTrace_5533694
  have hstable : (prefixWord ++ tailWord_5533694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533694).length < 2 ^ (prefixWord ++ tailWord_5533694).sum := by decide
  have hdescent : baseEnd_5533694 < baseStart_5533694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533696 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 4]
def baseStart_5533696 : Nat := 118140960795 + 5533696 * 2 ^ 59
def prefixEnd_5533696 : Nat := 4983230072969 + 3 ^ 40 * 5533696 * 2
def baseEnd_5533696 : Nat := 2841445843862486622651001

theorem tailTrace_5533696 : CollatzResearch.WordTrace tailWord_5533696 prefixEnd_5533696 2841445843862486622651001 := by
  unfold tailWord_5533696
  simp only [CollatzResearch.WordTrace]
  refine ⟨100915237080185973440122471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134553649440247964586829961 100915237080185973440122471)
  ·
    refine ⟨151372855620278960160183707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100915237080185973440122471 151372855620278960160183707)
    ·
      refine ⟨227059283430418440240275561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151372855620278960160183707 227059283430418440240275561)
      ·
        refine ⟨170294462572813830180206671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227059283430418440240275561 170294462572813830180206671)
        ·
          refine ⟨255441693859220745270310007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170294462572813830180206671 255441693859220745270310007)
          ·
            refine ⟨383162540788831117905465011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255441693859220745270310007 383162540788831117905465011)
            ·
              refine ⟨574743811183246676858197517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383162540788831117905465011 574743811183246676858197517)
              ·
                refine ⟨215528929193717503821824069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 574743811183246676858197517 215528929193717503821824069)
                ·
                  refine ⟨40411674223822031966592013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215528929193717503821824069 40411674223822031966592013)
                  ·
                    refine ⟨15154377833933261987472005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40411674223822031966592013 15154377833933261987472005)
                    ·
                      refine ⟨2841445843862486622651001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15154377833933261987472005 2841445843862486622651001)
                      ·
                        rfl

theorem cell23_5533696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_5533696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533696 prefixEnd_5533696 := by exact prefixLift 5533696
  have htrace : WordTrace (prefixWord ++ tailWord_5533696) baseStart_5533696 baseEnd_5533696 := by
    simpa [prefixWord, tailWord_5533696, baseEnd_5533696] using wordTrace_append hprefix tailTrace_5533696
  have hstable : (prefixWord ++ tailWord_5533696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533696).length < 2 ^ (prefixWord ++ tailWord_5533696).sum := by decide
  have hdescent : baseEnd_5533696 < baseStart_5533696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533730 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_5533730 : Nat := 118140960795 + 5533730 * 2 ^ 59
def prefixEnd_5533730 : Nat := 4983230072969 + 3 ^ 40 * 5533730 * 2
def baseEnd_5533730 : Nat := 2841463302204739489625845

theorem tailTrace_5533730 : CollatzResearch.WordTrace tailWord_5533730 prefixEnd_5533730 2841463302204739489625845 := by
  unfold tailWord_5533730
  simp only [CollatzResearch.WordTrace]
  refine ⟨50457928560562192671745661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134554476161499180457988429 50457928560562192671745661)
  ·
    refine ⟨18921723210210822251904623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50457928560562192671745661 18921723210210822251904623)
    ·
      refine ⟨28382584815316233377856935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18921723210210822251904623 28382584815316233377856935)
      ·
        refine ⟨42573877222974350066785403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28382584815316233377856935 42573877222974350066785403)
        ·
          refine ⟨63860815834461525100178105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42573877222974350066785403 63860815834461525100178105)
          ·
            refine ⟨47895611875846143825133579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63860815834461525100178105 47895611875846143825133579)
            ·
              refine ⟨71843417813769215737700369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47895611875846143825133579 71843417813769215737700369)
              ·
                refine ⟨53882563360326911803275277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71843417813769215737700369 53882563360326911803275277)
                ·
                  refine ⟨20205961260122591926228229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53882563360326911803275277 20205961260122591926228229)
                  ·
                    refine ⟨3788617736272985986167793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20205961260122591926228229 3788617736272985986167793)
                    ·
                      refine ⟨2841463302204739489625845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3788617736272985986167793 2841463302204739489625845)
                      ·
                        rfl

theorem cell23_5533730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_5533730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533730 prefixEnd_5533730 := by exact prefixLift 5533730
  have htrace : WordTrace (prefixWord ++ tailWord_5533730) baseStart_5533730 baseEnd_5533730 := by
    simpa [prefixWord, tailWord_5533730, baseEnd_5533730] using wordTrace_append hprefix tailTrace_5533730
  have hstable : (prefixWord ++ tailWord_5533730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533730).length < 2 ^ (prefixWord ++ tailWord_5533730).sum := by decide
  have hdescent : baseEnd_5533730 < baseStart_5533730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533733 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 2, 4, 3]
def baseStart_5533733 : Nat := 118140960795 + 5533733 * 2 ^ 59
def prefixEnd_5533733 : Nat := 4983230072969 + 3 ^ 40 * 5533733 * 2
def baseEnd_5533733 : Nat := 2841464842646702977888331

theorem tailTrace_5533733 : CollatzResearch.WordTrace tailWord_5533733 prefixEnd_5533733 2841464842646702977888331 := by
  unfold tailWord_5533733
  simp only [CollatzResearch.WordTrace]
  refine ⟨201831823661237902199341853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134554549107491934799561235 201831823661237902199341853)
  ·
    refine ⟨75686933872964213324753195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201831823661237902199341853 75686933872964213324753195)
    ·
      refine ⟨113530400809446319987129793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75686933872964213324753195 113530400809446319987129793)
      ·
        refine ⟨85147800607084739990347345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113530400809446319987129793 85147800607084739990347345)
        ·
          refine ⟨63860850455313554992760509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85147800607084739990347345 63860850455313554992760509)
          ·
            refine ⟨23947818920742583122285191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63860850455313554992760509 23947818920742583122285191)
            ·
              refine ⟨35921728381113874683427787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23947818920742583122285191 35921728381113874683427787)
              ·
                refine ⟨53882592571670812025141681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35921728381113874683427787 53882592571670812025141681)
                ·
                  refine ⟨40411944428753109018856261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53882592571670812025141681 40411944428753109018856261)
                  ·
                    refine ⟨7577239580391207941035549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40411944428753109018856261 7577239580391207941035549)
                    ·
                      refine ⟨2841464842646702977888331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7577239580391207941035549 2841464842646702977888331)
                      ·
                        rfl

theorem cell23_5533733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_5533733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533733 prefixEnd_5533733 := by exact prefixLift 5533733
  have htrace : WordTrace (prefixWord ++ tailWord_5533733) baseStart_5533733 baseEnd_5533733 := by
    simpa [prefixWord, tailWord_5533733, baseEnd_5533733] using wordTrace_append hprefix tailTrace_5533733
  have hstable : (prefixWord ++ tailWord_5533733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533733).length < 2 ^ (prefixWord ++ tailWord_5533733).sum := by decide
  have hdescent : baseEnd_5533733 < baseStart_5533733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533747 : List Nat := [1, 1, 1, 2, 4, 1, 4, 3, 2, 2, 2]
def baseStart_5533747 : Nat := 118140960795 + 5533747 * 2 ^ 59
def prefixEnd_5533747 : Nat := 4983230072969 + 3 ^ 40 * 5533747 * 2
def baseEnd_5533747 : Nat := 2841472031375865923113267

theorem tailTrace_5533747 : CollatzResearch.WordTrace tailWord_5533747 prefixEnd_5533747 2841472031375865923113267 := by
  unfold tailWord_5533747
  simp only [CollatzResearch.WordTrace]
  refine ⟨201832334283187182590351495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134554889522124788393567663 201832334283187182590351495)
  ·
    refine ⟨302748501424780773885527243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201832334283187182590351495 302748501424780773885527243)
    ·
      refine ⟨454122752137171160828290865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302748501424780773885527243 454122752137171160828290865)
      ·
        refine ⟨340592064102878370621218149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454122752137171160828290865 340592064102878370621218149)
        ·
          refine ⟨63861012019289694491478403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 340592064102878370621218149 63861012019289694491478403)
          ·
            refine ⟨95791518028934541737217605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63861012019289694491478403 95791518028934541737217605)
            ·
              refine ⟨17960909630425226575728301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95791518028934541737217605 17960909630425226575728301)
              ·
                refine ⟨6735341111409459965898113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17960909630425226575728301 6735341111409459965898113)
                ·
                  refine ⟨5051505833557094974423585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6735341111409459965898113 5051505833557094974423585)
                  ·
                    refine ⟨3788629375167821230817689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5051505833557094974423585 3788629375167821230817689)
                    ·
                      refine ⟨2841472031375865923113267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3788629375167821230817689 2841472031375865923113267)
                      ·
                        rfl

theorem cell23_5533747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 2, 2].length) (baseStart_5533747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533747 prefixEnd_5533747 := by exact prefixLift 5533747
  have htrace : WordTrace (prefixWord ++ tailWord_5533747) baseStart_5533747 baseEnd_5533747 := by
    simpa [prefixWord, tailWord_5533747, baseEnd_5533747] using wordTrace_append hprefix tailTrace_5533747
  have hstable : (prefixWord ++ tailWord_5533747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533747).length < 2 ^ (prefixWord ++ tailWord_5533747).sum := by decide
  have hdescent : baseEnd_5533747 < baseStart_5533747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533750 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_5533750 : Nat := 118140960795 + 5533750 * 2 ^ 59
def prefixEnd_5533750 : Nat := 4983230072969 + 3 ^ 40 * 5533750 * 2
def baseEnd_5533750 : Nat := 2841473571817829411375753

theorem tailTrace_5533750 : CollatzResearch.WordTrace tailWord_5533750 prefixEnd_5533750 2841473571817829411375753 := by
  unfold tailWord_5533750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12614527731386019631419419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134554962468117542735140469 12614527731386019631419419)
  ·
    refine ⟨18921791597079029447129129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12614527731386019631419419 18921791597079029447129129)
    ·
      refine ⟨14191343697809272085346847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18921791597079029447129129 14191343697809272085346847)
      ·
        refine ⟨21287015546713908128020271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14191343697809272085346847 21287015546713908128020271)
        ·
          refine ⟨31930523320070862192030407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21287015546713908128020271 31930523320070862192030407)
          ·
            refine ⟨47895784980106293288045611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31930523320070862192030407 47895784980106293288045611)
            ·
              refine ⟨71843677470159439932068417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47895784980106293288045611 71843677470159439932068417)
              ·
                refine ⟨53882758102619579949051313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71843677470159439932068417 53882758102619579949051313)
                ·
                  refine ⟨40412068576964684961788485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53882758102619579949051313 40412068576964684961788485)
                  ·
                    refine ⟨7577262858180878430335341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40412068576964684961788485 7577262858180878430335341)
                    ·
                      refine ⟨2841473571817829411375753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7577262858180878430335341 2841473571817829411375753)
                      ·
                        rfl

theorem cell23_5533750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_5533750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533750 prefixEnd_5533750 := by exact prefixLift 5533750
  have htrace : WordTrace (prefixWord ++ tailWord_5533750) baseStart_5533750 baseEnd_5533750 := by
    simpa [prefixWord, tailWord_5533750, baseEnd_5533750] using wordTrace_append hprefix tailTrace_5533750
  have hstable : (prefixWord ++ tailWord_5533750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533750).length < 2 ^ (prefixWord ++ tailWord_5533750).sum := by decide
  have hdescent : baseEnd_5533750 < baseStart_5533750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533783 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 2, 5]
def baseStart_5533783 : Nat := 118140960795 + 5533783 * 2 ^ 59
def prefixEnd_5533783 : Nat := 4983230072969 + 3 ^ 40 * 5533783 * 2
def baseEnd_5533783 : Nat := 947163505559809260754367

theorem tailTrace_5533783 : CollatzResearch.WordTrace tailWord_5533783 prefixEnd_5533783 947163505559809260754367 := by
  unfold tailWord_5533783
  simp only [CollatzResearch.WordTrace]
  refine ⟨201833647311056760738662003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134555764874037840492441335 201833647311056760738662003)
  ·
    refine ⟨302750470966585141107993005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201833647311056760738662003 302750470966585141107993005)
    ·
      refine ⟨113531426612469427915497377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302750470966585141107993005 113531426612469427915497377)
      ·
        refine ⟨85148569959352070936623033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113531426612469427915497377 85148569959352070936623033)
        ·
          refine ⟨63861427469514053202467275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85148569959352070936623033 63861427469514053202467275)
          ·
            refine ⟨95792141204271079803700913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63861427469514053202467275 95792141204271079803700913)
            ·
              refine ⟨71844105903203309852775685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95792141204271079803700913 71844105903203309852775685)
              ·
                refine ⟨13470769856850620597395441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71844105903203309852775685 13470769856850620597395441)
                ·
                  refine ⟨10103077392637965448046581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13470769856850620597395441 10103077392637965448046581)
                  ·
                    refine ⟨947163505559809260754367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10103077392637965448046581 947163505559809260754367)
                    ·
                      rfl

theorem cell23_5533783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_5533783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533783 prefixEnd_5533783 := by exact prefixLift 5533783
  have htrace : WordTrace (prefixWord ++ tailWord_5533783) baseStart_5533783 baseEnd_5533783 := by
    simpa [prefixWord, tailWord_5533783, baseEnd_5533783] using wordTrace_append hprefix tailTrace_5533783
  have hstable : (prefixWord ++ tailWord_5533783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533783).length < 2 ^ (prefixWord ++ tailWord_5533783).sum := by decide
  have hdescent : baseEnd_5533783 < baseStart_5533783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533840 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 3]
def baseStart_5533840 : Nat := 118140960795 + 5533840 * 2 ^ 59
def prefixEnd_5533840 : Nat := 4983230072969 + 3 ^ 40 * 5533840 * 2
def baseEnd_5533840 : Nat := 2841519785076734059250339

theorem tailTrace_5533840 : CollatzResearch.WordTrace tailWord_5533840 prefixEnd_5533840 2841519785076734059250339 := by
  unfold tailWord_5533840
  simp only [CollatzResearch.WordTrace]
  refine ⟨100917863135925129736743487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134557150847900172982324649 100917863135925129736743487)
  ·
    refine ⟨151376794703887694605115231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100917863135925129736743487 151376794703887694605115231)
    ·
      refine ⟨227065192055831541907672847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151376794703887694605115231 227065192055831541907672847)
      ·
        refine ⟨340597788083747312861509271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227065192055831541907672847 340597788083747312861509271)
        ·
          refine ⟨510896682125620969292263907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340597788083747312861509271 510896682125620969292263907)
          ·
            refine ⟨766345023188431453938395861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510896682125620969292263907 766345023188431453938395861)
            ·
              refine ⟨17961211480978862201681153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 766345023188431453938395861 17961211480978862201681153)
              ·
                refine ⟨13470908610734146651260865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17961211480978862201681153 13470908610734146651260865)
                ·
                  refine ⟨10103181458050609988445649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13470908610734146651260865 10103181458050609988445649)
                  ·
                    refine ⟨7577386093537957491334237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10103181458050609988445649 7577386093537957491334237)
                    ·
                      refine ⟨2841519785076734059250339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7577386093537957491334237 2841519785076734059250339)
                      ·
                        rfl

theorem cell23_5533840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 3].length) (baseStart_5533840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533840 prefixEnd_5533840 := by exact prefixLift 5533840
  have htrace : WordTrace (prefixWord ++ tailWord_5533840) baseStart_5533840 baseEnd_5533840 := by
    simpa [prefixWord, tailWord_5533840, baseEnd_5533840] using wordTrace_append hprefix tailTrace_5533840
  have hstable : (prefixWord ++ tailWord_5533840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533840).length < 2 ^ (prefixWord ++ tailWord_5533840).sum := by decide
  have hdescent : baseEnd_5533840 < baseStart_5533840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533843 : List Nat := [1, 1, 1, 2, 1, 2, 3, 6, 6]
def baseStart_5533843 : Nat := 118140960795 + 5533843 * 2 ^ 59
def prefixEnd_5533843 : Nat := 4983230072969 + 3 ^ 40 * 5533843 * 2
def baseEnd_5533843 : Nat := 315724591724299727501425

theorem tailTrace_5533843 : CollatzResearch.WordTrace tailWord_5533843 prefixEnd_5533843 315724591724299727501425 := by
  unfold tailWord_5533843
  simp only [CollatzResearch.WordTrace]
  refine ⟨201835835690839390985846183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134557223793892927323897455 201835835690839390985846183)
  ·
    refine ⟨302753753536259086478769275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201835835690839390985846183 302753753536259086478769275)
    ·
      refine ⟨454130630304388629718153913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302753753536259086478769275 454130630304388629718153913)
      ·
        refine ⟨340597972728291472288615435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454130630304388629718153913 340597972728291472288615435)
        ·
          refine ⟨510896959092437208432923153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340597972728291472288615435 510896959092437208432923153)
          ·
            refine ⟨383172719319327906324692365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510896959092437208432923153 383172719319327906324692365)
            ·
              refine ⟨143689769744747964871759637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383172719319327906324692365 143689769744747964871759637)
              ·
                refine ⟨6735457956785060853363733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 143689769744747964871759637 6735457956785060853363733)
                ·
                  refine ⟨315724591724299727501425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6735457956785060853363733 315724591724299727501425)
                  ·
                    rfl

theorem cell23_5533843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 6].length) (baseStart_5533843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533843 prefixEnd_5533843 := by exact prefixLift 5533843
  have htrace : WordTrace (prefixWord ++ tailWord_5533843) baseStart_5533843 baseEnd_5533843 := by
    simpa [prefixWord, tailWord_5533843, baseEnd_5533843] using wordTrace_append hprefix tailTrace_5533843
  have hstable : (prefixWord ++ tailWord_5533843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533843).length < 2 ^ (prefixWord ++ tailWord_5533843).sum := by decide
  have hdescent : baseEnd_5533843 < baseStart_5533843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533903 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 3, 6]
def baseStart_5533903 : Nat := 118140960795 + 5533903 * 2 ^ 59
def prefixEnd_5533903 : Nat := 4983230072969 + 3 ^ 40 * 5533903 * 2
def baseEnd_5533903 : Nat := 947184044785989104254183

theorem tailTrace_5533903 : CollatzResearch.WordTrace tailWord_5533903 prefixEnd_5533903 947184044785989104254183 := by
  unfold tailWord_5533903
  simp only [CollatzResearch.WordTrace]
  refine ⟨201838024070622021233030363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134558682713748014155353575 201838024070622021233030363)
  ·
    refine ⟨302757036105933031849545545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201838024070622021233030363 302757036105933031849545545)
    ·
      refine ⟨227067777079449773887159159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302757036105933031849545545 227067777079449773887159159)
      ·
        refine ⟨340601665619174660830738739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227067777079449773887159159 340601665619174660830738739)
        ·
          refine ⟨510902498428761991246108109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340601665619174660830738739 510902498428761991246108109)
          ·
            refine ⟨191588436910785746717290541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 510902498428761991246108109 191588436910785746717290541)
            ·
              refine ⟨71845663841544655018983953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191588436910785746717290541 71845663841544655018983953)
              ·
                refine ⟨53884247881158491264237965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71845663841544655018983953 53884247881158491264237965)
                ·
                  refine ⟨20206592955434434224089237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53884247881158491264237965 20206592955434434224089237)
                  ·
                    refine ⟨947184044785989104254183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20206592955434434224089237 947184044785989104254183)
                    ·
                      rfl

theorem cell23_5533903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_5533903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533903 prefixEnd_5533903 := by exact prefixLift 5533903
  have htrace : WordTrace (prefixWord ++ tailWord_5533903) baseStart_5533903 baseEnd_5533903 := by
    simpa [prefixWord, tailWord_5533903, baseEnd_5533903] using wordTrace_append hprefix tailTrace_5533903
  have hstable : (prefixWord ++ tailWord_5533903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533903).length < 2 ^ (prefixWord ++ tailWord_5533903).sum := by decide
  have hdescent : baseEnd_5533903 < baseStart_5533903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533920 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 1, 6]
def baseStart_5533920 : Nat := 118140960795 + 5533920 * 2 ^ 59
def prefixEnd_5533920 : Nat := 4983230072969 + 3 ^ 40 * 5533920 * 2
def baseEnd_5533920 : Nat := 947186954509697915416657

theorem tailTrace_5533920 : CollatzResearch.WordTrace tailWord_5533920 prefixEnd_5533920 947186954509697915416657 := by
  unfold tailWord_5533920
  simp only [CollatzResearch.WordTrace]
  refine ⟨100919322055780216568199607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134559096074373622090932809 100919322055780216568199607)
  ·
    refine ⟨151378983083670324852299411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100919322055780216568199607 151378983083670324852299411)
    ·
      refine ⟨227068474625505487278449117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151378983083670324852299411 227068474625505487278449117)
      ·
        refine ⟨85150677984564557729418419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227068474625505487278449117 85150677984564557729418419)
        ·
          refine ⟨127726016976846836594127629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85150677984564557729418419 127726016976846836594127629)
          ·
            refine ⟨47897256366317563722797861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127726016976846836594127629 47897256366317563722797861)
            ·
              refine ⟨8980735568684543198024599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47897256366317563722797861 8980735568684543198024599)
              ·
                refine ⟨13471103353026814797036899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8980735568684543198024599 13471103353026814797036899)
                ·
                  refine ⟨20206655029540222195555349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13471103353026814797036899 20206655029540222195555349)
                  ·
                    refine ⟨947186954509697915416657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20206655029540222195555349 947186954509697915416657)
                    ·
                      rfl

theorem cell23_5533920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 6].length) (baseStart_5533920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533920 prefixEnd_5533920 := by exact prefixLift 5533920
  have htrace : WordTrace (prefixWord ++ tailWord_5533920) baseStart_5533920 baseEnd_5533920 := by
    simpa [prefixWord, tailWord_5533920, baseEnd_5533920] using wordTrace_append hprefix tailTrace_5533920
  have hstable : (prefixWord ++ tailWord_5533920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533920).length < 2 ^ (prefixWord ++ tailWord_5533920).sum := by decide
  have hdescent : baseEnd_5533920 < baseStart_5533920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533927 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5533927 : Nat := 118140960795 + 5533927 * 2 ^ 59
def prefixEnd_5533927 : Nat := 4983230072969 + 3 ^ 40 * 5533927 * 2
def baseEnd_5533927 : Nat := 2841564457893675218862439

theorem tailTrace_5533927 : CollatzResearch.WordTrace tailWord_5533927 prefixEnd_5533927 2841564457893675218862439 := by
  unfold tailWord_5533927
  simp only [CollatzResearch.WordTrace]
  refine ⟨201838899422535073331904035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134559266281690048887936023 201838899422535073331904035)
  ·
    refine ⟨302758349133802609997856053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201838899422535073331904035 302758349133802609997856053)
    ·
      refine ⟨28383595231293994687299005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 302758349133802609997856053 28383595231293994687299005)
      ·
        refine ⟨10643848211735248007737127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28383595231293994687299005 10643848211735248007737127)
        ·
          refine ⟨15965772317602872011605691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10643848211735248007737127 15965772317602872011605691)
          ·
            refine ⟨23948658476404308017408537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15965772317602872011605691 23948658476404308017408537)
            ·
              refine ⟨17961493857303231013056403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23948658476404308017408537 17961493857303231013056403)
              ·
                refine ⟨26942240785954846519584605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17961493857303231013056403 26942240785954846519584605)
                ·
                  refine ⟨10103340294733067444844227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26942240785954846519584605 10103340294733067444844227)
                  ·
                    refine ⟨15155010442099601167266341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10103340294733067444844227 15155010442099601167266341)
                    ·
                      refine ⟨2841564457893675218862439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15155010442099601167266341 2841564457893675218862439)
                      ·
                        rfl

theorem cell23_5533927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5533927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533927 prefixEnd_5533927 := by exact prefixLift 5533927
  have htrace : WordTrace (prefixWord ++ tailWord_5533927) baseStart_5533927 baseEnd_5533927 := by
    simpa [prefixWord, tailWord_5533927, baseEnd_5533927] using wordTrace_append hprefix tailTrace_5533927
  have hstable : (prefixWord ++ tailWord_5533927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533927).length < 2 ^ (prefixWord ++ tailWord_5533927).sum := by decide
  have hdescent : baseEnd_5533927 < baseStart_5533927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533950 : List Nat := [4, 2, 2, 1, 1, 1, 12]
def baseStart_5533950 : Nat := 118140960795 + 5533950 * 2 ^ 59
def prefixEnd_5533950 : Nat := 4983230072969 + 3 ^ 40 * 5533950 * 2
def baseEnd_5533950 : Nat := 35081188493194180603393

theorem tailTrace_5533950 : CollatzResearch.WordTrace tailWord_5533950 prefixEnd_5533950 35081188493194180603393 := by
  unfold tailWord_5533950
  simp only [CollatzResearch.WordTrace]
  refine ⟨25229967287681468532498913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134559825534301165506660869 25229967287681468532498913)
  ·
    refine ⟨18922475465761101399374185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25229967287681468532498913 18922475465761101399374185)
    ·
      refine ⟨14191856599320826049530639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18922475465761101399374185 14191856599320826049530639)
      ·
        refine ⟨21287784898981239074295959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14191856599320826049530639 21287784898981239074295959)
        ·
          refine ⟨31931677348471858611443939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21287784898981239074295959 31931677348471858611443939)
          ·
            refine ⟨47897516022707787917165909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31931677348471858611443939 47897516022707787917165909)
            ·
              refine ⟨35081188493194180603393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 47897516022707787917165909 35081188493194180603393)
              ·
                rfl

theorem cell23_5533950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 12].length) (baseStart_5533950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533950 prefixEnd_5533950 := by exact prefixLift 5533950
  have htrace : WordTrace (prefixWord ++ tailWord_5533950) baseStart_5533950 baseEnd_5533950 := by
    simpa [prefixWord, tailWord_5533950, baseEnd_5533950] using wordTrace_append hprefix tailTrace_5533950
  have hstable : (prefixWord ++ tailWord_5533950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533950).length < 2 ^ (prefixWord ++ tailWord_5533950).sum := by decide
  have hdescent : baseEnd_5533950 < baseStart_5533950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533954 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_5533954 : Nat := 118140960795 + 5533954 * 2 ^ 59
def prefixEnd_5533954 : Nat := 4983230072969 + 3 ^ 40 * 5533954 * 2
def baseEnd_5533954 : Nat := 947192773957115537741605

theorem tailTrace_5533954 : CollatzResearch.WordTrace tailWord_5533954 prefixEnd_5533954 947192773957115537741605 := by
  unfold tailWord_5533954
  simp only [CollatzResearch.WordTrace]
  refine ⟨50459971048359314235784229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134559922795624837962091277 50459971048359314235784229)
  ·
    refine ⟨9461244571567371419209543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50459971048359314235784229 9461244571567371419209543)
    ·
      refine ⟨14191866857351057128814315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9461244571567371419209543 14191866857351057128814315)
      ·
        refine ⟨21287800286026585693221473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14191866857351057128814315 21287800286026585693221473)
        ·
          refine ⟨15965850214519939269916105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21287800286026585693221473 15965850214519939269916105)
          ·
            refine ⟨11974387660889954452437079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15965850214519939269916105 11974387660889954452437079)
            ·
              refine ⟨17961581491334931678655619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11974387660889954452437079 17961581491334931678655619)
              ·
                refine ⟨26942372237002397517983429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17961581491334931678655619 26942372237002397517983429)
                ·
                  refine ⟨5051694794437949534621893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26942372237002397517983429 5051694794437949534621893)
                  ·
                    refine ⟨947192773957115537741605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5051694794437949534621893 947192773957115537741605)
                    ·
                      rfl

theorem cell23_5533954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_5533954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533954 prefixEnd_5533954 := by exact prefixLift 5533954
  have htrace : WordTrace (prefixWord ++ tailWord_5533954) baseStart_5533954 baseEnd_5533954 := by
    simpa [prefixWord, tailWord_5533954, baseEnd_5533954] using wordTrace_append hprefix tailTrace_5533954
  have hstable : (prefixWord ++ tailWord_5533954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533954).length < 2 ^ (prefixWord ++ tailWord_5533954).sum := by decide
  have hdescent : baseEnd_5533954 < baseStart_5533954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533961 : List Nat := [1, 2, 1, 1, 3, 4, 2, 4, 1, 2, 2]
def baseStart_5533961 : Nat := 118140960795 + 5533961 * 2 ^ 59
def prefixEnd_5533961 : Nat := 4983230072969 + 3 ^ 40 * 5533961 * 2
def baseEnd_5533961 : Nat := 2841581916235928085837283

theorem tailTrace_5533961 : CollatzResearch.WordTrace tailWord_5533961 prefixEnd_5533961 2841581916235928085837283 := by
  unfold tailWord_5533961
  simp only [CollatzResearch.WordTrace]
  refine ⟨201840139504411897138641737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134560093002941264759094491 201840139504411897138641737)
  ·
    refine ⟨151380104628308922853981303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201840139504411897138641737 151380104628308922853981303)
    ·
      refine ⟨227070156942463384280971955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151380104628308922853981303 227070156942463384280971955)
      ·
        refine ⟨340605235413695076421457933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227070156942463384280971955 340605235413695076421457933)
        ·
          refine ⟨127726963280135653658046725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340605235413695076421457933 127726963280135653658046725)
          ·
            refine ⟨23948805615025435060883761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127726963280135653658046725 23948805615025435060883761)
            ·
              refine ⟨17961604211269076295662821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23948805615025435060883761 17961604211269076295662821)
              ·
                refine ⟨3367800789612951805436779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17961604211269076295662821 3367800789612951805436779)
                ·
                  refine ⟨5051701184419427708155169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3367800789612951805436779 5051701184419427708155169)
                  ·
                    refine ⟨3788775888314570781116377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5051701184419427708155169 3788775888314570781116377)
                    ·
                      refine ⟨2841581916235928085837283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3788775888314570781116377 2841581916235928085837283)
                      ·
                        rfl

theorem cell23_5533961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 1, 2, 2].length) (baseStart_5533961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533961 prefixEnd_5533961 := by exact prefixLift 5533961
  have htrace : WordTrace (prefixWord ++ tailWord_5533961) baseStart_5533961 baseEnd_5533961 := by
    simpa [prefixWord, tailWord_5533961, baseEnd_5533961] using wordTrace_append hprefix tailTrace_5533961
  have hstable : (prefixWord ++ tailWord_5533961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533961).length < 2 ^ (prefixWord ++ tailWord_5533961).sum := by decide
  have hdescent : baseEnd_5533961 < baseStart_5533961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5533981 : List Nat := [1, 4, 2, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_5533981 : Nat := 118140960795 + 5533981 * 2 ^ 59
def prefixEnd_5533981 : Nat := 4983230072969 + 3 ^ 40 * 5533981 * 2
def baseEnd_5533981 : Nat := 2841592185849018007587191

theorem tailTrace_5533981 : CollatzResearch.WordTrace tailWord_5533981 prefixEnd_5533981 2841592185849018007587191 := by
  unfold tailWord_5533981
  simp only [CollatzResearch.WordTrace]
  refine ⟨201840868964339440554369797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134560579309559627036246531 201840868964339440554369797)
  ·
    refine ⟨37845162930813645103944337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201840868964339440554369797 37845162930813645103944337)
    ·
      refine ⟨28383872198110233827958253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37845162930813645103944337 28383872198110233827958253)
      ·
        refine ⟨10643952074291337685484345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28383872198110233827958253 10643952074291337685484345)
        ·
          refine ⟨7982964055718503264113259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10643952074291337685484345 7982964055718503264113259)
          ·
            refine ⟨11974446083577754896169889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7982964055718503264113259 11974446083577754896169889)
            ·
              refine ⟨8980834562683316172127417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11974446083577754896169889 8980834562683316172127417)
              ·
                refine ⟨6735625922012487129095563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8980834562683316172127417 6735625922012487129095563)
                ·
                  refine ⟨10103438883018730693643345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6735625922012487129095563 10103438883018730693643345)
                  ·
                    refine ⟨7577579162264048020232509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10103438883018730693643345 7577579162264048020232509)
                    ·
                      refine ⟨2841592185849018007587191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7577579162264048020232509 2841592185849018007587191)
                      ·
                        rfl

theorem cell23_5533981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_5533981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5533981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5533981 prefixEnd_5533981 := by exact prefixLift 5533981
  have htrace : WordTrace (prefixWord ++ tailWord_5533981) baseStart_5533981 baseEnd_5533981 := by
    simpa [prefixWord, tailWord_5533981, baseEnd_5533981] using wordTrace_append hprefix tailTrace_5533981
  have hstable : (prefixWord ++ tailWord_5533981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5533981).length < 2 ^ (prefixWord ++ tailWord_5533981).sum := by decide
  have hdescent : baseEnd_5533981 < baseStart_5533981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5533981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534057 : List Nat := [1, 2, 1, 1, 1, 3, 4, 5, 5]
def baseStart_5534057 : Nat := 118140960795 + 5534057 * 2 ^ 59
def prefixEnd_5534057 : Nat := 4983230072969 + 3 ^ 40 * 5534057 * 2
def baseEnd_5534057 : Nat := 315736801153195523359649

theorem tailTrace_5534057 : CollatzResearch.WordTrace tailWord_5534057 prefixEnd_5534057 315736801153195523359649 := by
  unfold tailWord_5534057
  simp only [CollatzResearch.WordTrace]
  refine ⟨201843640912064105534136425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134562427274709403689424283 201843640912064105534136425)
  ·
    refine ⟨151382730684048079150602319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201843640912064105534136425 151382730684048079150602319)
    ·
      refine ⟨227074096026072118725903479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151382730684048079150602319 227074096026072118725903479)
      ·
        refine ⟨340611144039108178088855219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227074096026072118725903479 340611144039108178088855219)
        ·
          refine ⟨510916716058662267133282829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340611144039108178088855219 510916716058662267133282829)
          ·
            refine ⟨191593768521998350174981061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 510916716058662267133282829 191593768521998350174981061)
            ·
              refine ⟨35923831597874690657808949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191593768521998350174981061 35923831597874690657808949)
              ·
                refine ⟨3367859212300752249169589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35923831597874690657808949 3367859212300752249169589)
                ·
                  refine ⟨315736801153195523359649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3367859212300752249169589 315736801153195523359649)
                  ·
                    rfl

theorem cell23_5534057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 5].length) (baseStart_5534057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534057 prefixEnd_5534057 := by exact prefixLift 5534057
  have htrace : WordTrace (prefixWord ++ tailWord_5534057) baseStart_5534057 baseEnd_5534057 := by
    simpa [prefixWord, tailWord_5534057, baseEnd_5534057] using wordTrace_append hprefix tailTrace_5534057
  have hstable : (prefixWord ++ tailWord_5534057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534057).length < 2 ^ (prefixWord ++ tailWord_5534057).sum := by decide
  have hdescent : baseEnd_5534057 < baseStart_5534057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534104 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 2, 5]
def baseStart_5534104 : Nat := 118140960795 + 5534104 * 2 ^ 59
def prefixEnd_5534104 : Nat := 4983230072969 + 3 ^ 40 * 5534104 * 2
def baseEnd_5534104 : Nat := 947218447989840342116375

theorem tailTrace_5534104 : CollatzResearch.WordTrace tailWord_5534104 prefixEnd_5534104 947218447989840342116375 := by
  unfold tailWord_5534104
  simp only [CollatzResearch.WordTrace]
  refine ⟨100922677571446916280548683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134563570095262555040731577 100922677571446916280548683)
  ·
    refine ⟨151384016357170374420823025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100922677571446916280548683 151384016357170374420823025)
    ·
      refine ⟨113538012267877780815617269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151384016357170374420823025 113538012267877780815617269)
      ·
        refine ⟨10644188650113541951464119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113538012267877780815617269 10644188650113541951464119)
        ·
          refine ⟨15966282975170312927196179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10644188650113541951464119 15966282975170312927196179)
          ·
            refine ⟨23949424462755469390794269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15966282975170312927196179 23949424462755469390794269)
            ·
              refine ⟨8981034173533301021547851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23949424462755469390794269 8981034173533301021547851)
              ·
                refine ⟨13471551260299951532321777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8981034173533301021547851 13471551260299951532321777)
                ·
                  refine ⟨10103663445224963649241333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13471551260299951532321777 10103663445224963649241333)
                  ·
                    refine ⟨947218447989840342116375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10103663445224963649241333 947218447989840342116375)
                    ·
                      rfl

theorem cell23_5534104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_5534104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534104 prefixEnd_5534104 := by exact prefixLift 5534104
  have htrace : WordTrace (prefixWord ++ tailWord_5534104) baseStart_5534104 baseEnd_5534104 := by
    simpa [prefixWord, tailWord_5534104, baseEnd_5534104] using wordTrace_append hprefix tailTrace_5534104
  have hstable : (prefixWord ++ tailWord_5534104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534104).length < 2 ^ (prefixWord ++ tailWord_5534104).sum := by decide
  have hdescent : baseEnd_5534104 < baseStart_5534104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534117 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 5, 4]
def baseStart_5534117 : Nat := 118140960795 + 5534117 * 2 ^ 59
def prefixEnd_5534117 : Nat := 4983230072969 + 3 ^ 40 * 5534117 * 2
def baseEnd_5534117 : Nat := 947220673072676491828855

theorem tailTrace_5534117 : CollatzResearch.WordTrace tailWord_5534117 prefixEnd_5534117 947220673072676491828855 := by
  unfold tailWord_5534117
  simp only [CollatzResearch.WordTrace]
  refine ⟨201845829291846735781320605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134563886194564490520880403 201845829291846735781320605)
  ·
    refine ⟨75692185984442525917995227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201845829291846735781320605 75692185984442525917995227)
    ·
      refine ⟨113538278976663788876992841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75692185984442525917995227 113538278976663788876992841)
      ·
        refine ⟨85153709232497841657744631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113538278976663788876992841 85153709232497841657744631)
        ·
          refine ⟨127730563848746762486616947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85153709232497841657744631 127730563848746762486616947)
          ·
            refine ⟨191595845773120143729925421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127730563848746762486616947 191595845773120143729925421)
            ·
              refine ⟨71848442164920053898722033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191595845773120143729925421 71848442164920053898722033)
              ·
                refine ⟨53886331623690040424041525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71848442164920053898722033 53886331623690040424041525)
                ·
                  refine ⟨5051843589720941289753893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53886331623690040424041525 5051843589720941289753893)
                  ·
                    refine ⟨947220673072676491828855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5051843589720941289753893 947220673072676491828855)
                    ·
                      rfl

theorem cell23_5534117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_5534117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534117 prefixEnd_5534117 := by exact prefixLift 5534117
  have htrace : WordTrace (prefixWord ++ tailWord_5534117) baseStart_5534117 baseEnd_5534117 := by
    simpa [prefixWord, tailWord_5534117, baseEnd_5534117] using wordTrace_append hprefix tailTrace_5534117
  have hstable : (prefixWord ++ tailWord_5534117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534117).length < 2 ^ (prefixWord ++ tailWord_5534117).sum := by decide
  have hdescent : baseEnd_5534117 < baseStart_5534117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534207 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 1, 6]
def baseStart_5534207 : Nat := 118140960795 + 5534207 * 2 ^ 59
def prefixEnd_5534207 : Nat := 4983230072969 + 3 ^ 40 * 5534207 * 2
def baseEnd_5534207 : Nat := 947236077492311374453717

theorem tailTrace_5534207 : CollatzResearch.WordTrace tailWord_5534207 prefixEnd_5534207 947236077492311374453717 := by
  unfold tailWord_5534207
  simp only [CollatzResearch.WordTrace]
  refine ⟨201849111861520681152096875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134566074574347120768064583 201849111861520681152096875)
  ·
    refine ⟨302773667792281021728145313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201849111861520681152096875 302773667792281021728145313)
    ·
      refine ⟨227080250844210766296108985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302773667792281021728145313 227080250844210766296108985)
      ·
        refine ⟨170310188133158074722081739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227080250844210766296108985 170310188133158074722081739)
        ·
          refine ⟨255465282199737112083122609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170310188133158074722081739 255465282199737112083122609)
          ·
            refine ⟨191598961649802834062341957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255465282199737112083122609 191598961649802834062341957)
            ·
              refine ⟨35924805309338031386689117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191598961649802834062341957 35924805309338031386689117)
              ·
                refine ⟨13471801991001761770008419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35924805309338031386689117 13471801991001761770008419)
                ·
                  refine ⟨20207702986502642655012629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13471801991001761770008419 20207702986502642655012629)
                  ·
                    refine ⟨947236077492311374453717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20207702986502642655012629 947236077492311374453717)
                    ·
                      rfl

theorem cell23_5534207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 6].length) (baseStart_5534207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534207 prefixEnd_5534207 := by exact prefixLift 5534207
  have htrace : WordTrace (prefixWord ++ tailWord_5534207) baseStart_5534207 baseEnd_5534207 := by
    simpa [prefixWord, tailWord_5534207, baseEnd_5534207] using wordTrace_append hprefix tailTrace_5534207
  have hstable : (prefixWord ++ tailWord_5534207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534207).length < 2 ^ (prefixWord ++ tailWord_5534207).sum := by decide
  have hdescent : baseEnd_5534207 < baseStart_5534207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534234 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5]
def baseStart_5534234 : Nat := 118140960795 + 5534234 * 2 ^ 59
def prefixEnd_5534234 : Nat := 4983230072969 + 3 ^ 40 * 5534234 * 2
def baseEnd_5534234 : Nat := 2841722096454605517723527

theorem tailTrace_5534234 : CollatzResearch.WordTrace tailWord_5534234 prefixEnd_5534234 2841722096454605517723527 := by
  unfold tailWord_5534234
  simp only [CollatzResearch.WordTrace]
  refine ⟨50462524158105716190832439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134566731088281909842219837 50462524158105716190832439)
  ·
    refine ⟨75693786237158574286248659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50462524158105716190832439 75693786237158574286248659)
    ·
      refine ⟨113540679355737861429372989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75693786237158574286248659 113540679355737861429372989)
      ·
        refine ⟨42577754758401698036014871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113540679355737861429372989 42577754758401698036014871)
        ·
          refine ⟨63866632137602547054022307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42577754758401698036014871 63866632137602547054022307)
          ·
            refine ⟨95799948206403820581033461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63866632137602547054022307 95799948206403820581033461)
            ·
              refine ⟨8981245144350358179471887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95799948206403820581033461 8981245144350358179471887)
              ·
                refine ⟨13471867716525537269207831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8981245144350358179471887 13471867716525537269207831)
                ·
                  refine ⟨20207801574788305903811747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13471867716525537269207831 20207801574788305903811747)
                  ·
                    refine ⟨30311702362182458855717621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20207801574788305903811747 30311702362182458855717621)
                    ·
                      refine ⟨2841722096454605517723527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30311702362182458855717621 2841722096454605517723527)
                      ·
                        rfl

theorem cell23_5534234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_5534234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534234 prefixEnd_5534234 := by exact prefixLift 5534234
  have htrace : WordTrace (prefixWord ++ tailWord_5534234) baseStart_5534234 baseEnd_5534234 := by
    simpa [prefixWord, tailWord_5534234, baseEnd_5534234] using wordTrace_append hprefix tailTrace_5534234
  have hstable : (prefixWord ++ tailWord_5534234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534234).length < 2 ^ (prefixWord ++ tailWord_5534234).sum := by decide
  have hdescent : baseEnd_5534234 < baseStart_5534234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534237 : List Nat := [1, 4, 2, 2, 1, 13]
def baseStart_5534237 : Nat := 118140960795 + 5534237 * 2 ^ 59
def prefixEnd_5534237 : Nat := 4983230072969 + 3 ^ 40 * 5534237 * 2
def baseEnd_5534237 : Nat := 11694335954306868337391

theorem tailTrace_5534237 : CollatzResearch.WordTrace tailWord_5534237 prefixEnd_5534237 11694335954306868337391 := by
  unfold tailWord_5534237
  simp only [CollatzResearch.WordTrace]
  refine ⟨201850206051411996275688965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134566804034274664183792643 201850206051411996275688965)
  ·
    refine ⟨37846913634639749301691681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201850206051411996275688965 37846913634639749301691681)
    ·
      refine ⟨28385185225979811976268761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37846913634639749301691681 28385185225979811976268761)
      ·
        refine ⟨21288888919484858982201571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28385185225979811976268761 21288888919484858982201571)
        ·
          refine ⟨31933333379227288473302357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21288888919484858982201571 31933333379227288473302357)
          ·
            refine ⟨11694335954306868337391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 31933333379227288473302357 11694335954306868337391)
            ·
              rfl

theorem cell23_5534237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 13].length) (baseStart_5534237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534237 prefixEnd_5534237 := by exact prefixLift 5534237
  have htrace : WordTrace (prefixWord ++ tailWord_5534237) baseStart_5534237 baseEnd_5534237 := by
    simpa [prefixWord, tailWord_5534237, baseEnd_5534237] using wordTrace_append hprefix tailTrace_5534237
  have hstable : (prefixWord ++ tailWord_5534237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534237).length < 2 ^ (prefixWord ++ tailWord_5534237).sum := by decide
  have hdescent : baseEnd_5534237 < baseStart_5534237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534241 : List Nat := [1, 2, 3, 2, 2, 1, 4, 2, 2, 4]
def baseStart_5534241 : Nat := 118140960795 + 5534241 * 2 ^ 59
def prefixEnd_5534241 : Nat := 4983230072969 + 3 ^ 40 * 5534241 * 2
def baseEnd_5534241 : Nat := 947241896939728996778665

theorem tailTrace_5534241 : CollatzResearch.WordTrace tailWord_5534241 prefixEnd_5534241 947241896939728996778665 := by
  unfold tailWord_5534241
  simp only [CollatzResearch.WordTrace]
  refine ⟨201850351943397504958834577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134566901295598336639223051 201850351943397504958834577)
  ·
    refine ⟨151387763957548128719125933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201850351943397504958834577 151387763957548128719125933)
    ·
      refine ⟨56770411484080548269672225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151387763957548128719125933 56770411484080548269672225)
      ·
        refine ⟨42577808613060411202254169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56770411484080548269672225 42577808613060411202254169)
        ·
          refine ⟨31933356459795308401690627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42577808613060411202254169 31933356459795308401690627)
          ·
            refine ⟨47900034689692962602535941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31933356459795308401690627 47900034689692962602535941)
            ·
              refine ⟨8981256504317430487975489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47900034689692962602535941 8981256504317430487975489)
              ·
                refine ⟨6735942378238072865981617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8981256504317430487975489 6735942378238072865981617)
                ·
                  refine ⟨5051956783678554649486213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6735942378238072865981617 5051956783678554649486213)
                  ·
                    refine ⟨947241896939728996778665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5051956783678554649486213 947241896939728996778665)
                    ·
                      rfl

theorem cell23_5534241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_5534241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534241 prefixEnd_5534241 := by exact prefixLift 5534241
  have htrace : WordTrace (prefixWord ++ tailWord_5534241) baseStart_5534241 baseEnd_5534241 := by
    simpa [prefixWord, tailWord_5534241, baseEnd_5534241] using wordTrace_append hprefix tailTrace_5534241
  have hstable : (prefixWord ++ tailWord_5534241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534241).length < 2 ^ (prefixWord ++ tailWord_5534241).sum := by decide
  have hdescent : baseEnd_5534241 < baseStart_5534241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534257 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_5534257 : Nat := 118140960795 + 5534257 * 2 ^ 59
def prefixEnd_5534257 : Nat := 4983230072969 + 3 ^ 40 * 5534257 * 2
def baseEnd_5534257 : Nat := 2841733906509658927735921

theorem tailTrace_5534257 : CollatzResearch.WordTrace tailWord_5534257 prefixEnd_5534257 2841733906509658927735921 := by
  unfold tailWord_5534257
  simp only [CollatzResearch.WordTrace]
  refine ⟨201850935511339539691417025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134567290340893026460944683 201850935511339539691417025)
  ·
    refine ⟨151388201633504654768562769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201850935511339539691417025 151388201633504654768562769)
    ·
      refine ⟨113541151225128491076422077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151388201633504654768562769 113541151225128491076422077)
      ·
        refine ⟨42577931709423184153658279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113541151225128491076422077 42577931709423184153658279)
        ·
          refine ⟨63866897564134776230487419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42577931709423184153658279 63866897564134776230487419)
          ·
            refine ⟨95800346346202164345731129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63866897564134776230487419 95800346346202164345731129)
            ·
              refine ⟨71850259759651623259298347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95800346346202164345731129 71850259759651623259298347)
              ·
                refine ⟨107775389639477434888947521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71850259759651623259298347 107775389639477434888947521)
                ·
                  refine ⟨80831542229608076166710641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107775389639477434888947521 80831542229608076166710641)
                  ·
                    refine ⟨60623656672206057125032981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80831542229608076166710641 60623656672206057125032981)
                    ·
                      refine ⟨2841733906509658927735921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60623656672206057125032981 2841733906509658927735921)
                      ·
                        rfl

theorem cell23_5534257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_5534257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534257 prefixEnd_5534257 := by exact prefixLift 5534257
  have htrace : WordTrace (prefixWord ++ tailWord_5534257) baseStart_5534257 baseEnd_5534257 := by
    simpa [prefixWord, tailWord_5534257, baseEnd_5534257] using wordTrace_append hprefix tailTrace_5534257
  have hstable : (prefixWord ++ tailWord_5534257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534257).length < 2 ^ (prefixWord ++ tailWord_5534257).sum := by decide
  have hdescent : baseEnd_5534257 < baseStart_5534257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534278 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_5534278 : Nat := 118140960795 + 5534278 * 2 ^ 59
def prefixEnd_5534278 : Nat := 4983230072969 + 3 ^ 40 * 5534278 * 2
def baseEnd_5534278 : Nat := 2841744689603403345573325

theorem tailTrace_5534278 : CollatzResearch.WordTrace tailWord_5534278 prefixEnd_5534278 2841744689603403345573325 := by
  unfold tailWord_5534278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6307865670133233133685359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 134567800962842306851954325 6307865670133233133685359)
  ·
    refine ⟨9461798505199849700528039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6307865670133233133685359 9461798505199849700528039)
    ·
      refine ⟨14192697757799774550792059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9461798505199849700528039 14192697757799774550792059)
      ·
        refine ⟨21289046636699661826188089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14192697757799774550792059 21289046636699661826188089)
        ·
          refine ⟨15966784977524746369641067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21289046636699661826188089 15966784977524746369641067)
          ·
            refine ⟨23950177466287119554461601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15966784977524746369641067 23950177466287119554461601)
            ·
              refine ⟨17962633099715339665846201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23950177466287119554461601 17962633099715339665846201)
              ·
                refine ⟨13471974824786504749384651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17962633099715339665846201 13471974824786504749384651)
                ·
                  refine ⟨20207962237179757124076977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13471974824786504749384651 20207962237179757124076977)
                  ·
                    refine ⟨15155971677884817843057733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20207962237179757124076977 15155971677884817843057733)
                    ·
                      refine ⟨2841744689603403345573325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15155971677884817843057733 2841744689603403345573325)
                      ·
                        rfl

theorem cell23_5534278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_5534278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534278 prefixEnd_5534278 := by exact prefixLift 5534278
  have htrace : WordTrace (prefixWord ++ tailWord_5534278) baseStart_5534278 baseEnd_5534278 := by
    simpa [prefixWord, tailWord_5534278, baseEnd_5534278] using wordTrace_append hprefix tailTrace_5534278
  have hstable : (prefixWord ++ tailWord_5534278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534278).length < 2 ^ (prefixWord ++ tailWord_5534278).sum := by decide
  have hdescent : baseEnd_5534278 < baseStart_5534278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534285 : List Nat := [1, 6, 1, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_5534285 : Nat := 118140960795 + 5534285 * 2 ^ 59
def prefixEnd_5534285 : Nat := 4983230072969 + 3 ^ 40 * 5534285 * 2
def baseEnd_5534285 : Nat := 2841748283967984818185793

theorem tailTrace_5534285 : CollatzResearch.WordTrace tailWord_5534285 prefixEnd_5534285 2841748283967984818185793 := by
  unfold tailWord_5534285
  simp only [CollatzResearch.WordTrace]
  refine ⟨201851956755238100473436309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134567971170158733648957539 201851956755238100473436309)
  ·
    refine ⟨9461810472901785959692327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 201851956755238100473436309 9461810472901785959692327)
    ·
      refine ⟨14192715709352678939538491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9461810472901785959692327 14192715709352678939538491)
      ·
        refine ⟨21289073564029018409307737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14192715709352678939538491 21289073564029018409307737)
        ·
          refine ⟨15966805173021763806980803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21289073564029018409307737 15966805173021763806980803)
          ·
            refine ⟨23950207759532645710471205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15966805173021763806980803 23950207759532645710471205)
            ·
              refine ⟨4490663954912371070713351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23950207759532645710471205 4490663954912371070713351)
              ·
                refine ⟨6735995932368556606070027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490663954912371070713351 6735995932368556606070027)
                ·
                  refine ⟨10103993898552834909105041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6735995932368556606070027 10103993898552834909105041)
                  ·
                    refine ⟨7577995423914626181828781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10103993898552834909105041 7577995423914626181828781)
                    ·
                      refine ⟨2841748283967984818185793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7577995423914626181828781 2841748283967984818185793)
                      ·
                        rfl

theorem cell23_5534285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_5534285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534285 prefixEnd_5534285 := by exact prefixLift 5534285
  have htrace : WordTrace (prefixWord ++ tailWord_5534285) baseStart_5534285 baseEnd_5534285 := by
    simpa [prefixWord, tailWord_5534285, baseEnd_5534285] using wordTrace_append hprefix tailTrace_5534285
  have hstable : (prefixWord ++ tailWord_5534285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534285).length < 2 ^ (prefixWord ++ tailWord_5534285).sum := by decide
  have hdescent : baseEnd_5534285 < baseStart_5534285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534314 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 2, 6]
def baseStart_5534314 : Nat := 118140960795 + 5534314 * 2 ^ 59
def prefixEnd_5534314 : Nat := 4983230072969 + 3 ^ 40 * 5534314 * 2
def baseEnd_5534314 : Nat := 947254391635655068241053

theorem tailTrace_5534314 : CollatzResearch.WordTrace tailWord_5534314 prefixEnd_5534314 947254391635655068241053 := by
  unfold tailWord_5534314
  simp only [CollatzResearch.WordTrace]
  refine ⟨50463253618033259606560499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134568676314755358950827997 50463253618033259606560499)
  ·
    refine ⟨75694880427049889409840749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50463253618033259606560499 75694880427049889409840749)
    ·
      refine ⟨28385580160143708528690281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75694880427049889409840749 28385580160143708528690281)
      ·
        refine ⟨21289185120107781396517711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28385580160143708528690281 21289185120107781396517711)
        ·
          refine ⟨31933777680161672094776567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21289185120107781396517711 31933777680161672094776567)
          ·
            refine ⟨47900666520242508142164851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31933777680161672094776567 47900666520242508142164851)
            ·
              refine ⟨71850999780363762213247277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47900666520242508142164851 71850999780363762213247277)
              ·
                refine ⟨26944124917636410829967729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71850999780363762213247277 26944124917636410829967729)
                ·
                  refine ⟨20208093688227308122475797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26944124917636410829967729 20208093688227308122475797)
                  ·
                    refine ⟨947254391635655068241053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20208093688227308122475797 947254391635655068241053)
                    ·
                      rfl

theorem cell23_5534314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_5534314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534314 prefixEnd_5534314 := by exact prefixLift 5534314
  have htrace : WordTrace (prefixWord ++ tailWord_5534314) baseStart_5534314 baseEnd_5534314 := by
    simpa [prefixWord, tailWord_5534314, baseEnd_5534314] using wordTrace_append hprefix tailTrace_5534314
  have hstable : (prefixWord ++ tailWord_5534314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534314).length < 2 ^ (prefixWord ++ tailWord_5534314).sum := by decide
  have hdescent : baseEnd_5534314 < baseStart_5534314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534406 : List Nat := [6, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_5534406 : Nat := 118140960795 + 5534406 * 2 ^ 59
def prefixEnd_5534406 : Nat := 4983230072969 + 3 ^ 40 * 5534406 * 2
def baseEnd_5534406 : Nat := 2841810415127178844772737

theorem tailTrace_5534406 : CollatzResearch.WordTrace tailWord_5534406 prefixEnd_5534406 2841810415127178844772737 := by
  unfold tailWord_5534406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6308011562118741816830971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 134570913325199825425727381 6308011562118741816830971)
  ·
    refine ⟨9462017343178112725246457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6308011562118741816830971 9462017343178112725246457)
    ·
      refine ⟨7096513007383584543934843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9462017343178112725246457 7096513007383584543934843)
      ·
        refine ⟨10644769511075376815902265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7096513007383584543934843 10644769511075376815902265)
        ·
          refine ⟨7983577133306532611926699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10644769511075376815902265 7983577133306532611926699)
          ·
            refine ⟨11975365699959798917890049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7983577133306532611926699 11975365699959798917890049)
            ·
              refine ⟨8981524274969849188417537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11975365699959798917890049 8981524274969849188417537)
              ·
                refine ⟨6736143206227386891313153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8981524274969849188417537 6736143206227386891313153)
                ·
                  refine ⟨5052107404670540168484865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6736143206227386891313153 5052107404670540168484865)
                  ·
                    refine ⟨3789080553502905126363649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5052107404670540168484865 3789080553502905126363649)
                    ·
                      refine ⟨2841810415127178844772737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3789080553502905126363649 2841810415127178844772737)
                      ·
                        rfl

theorem cell23_5534406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_5534406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534406 prefixEnd_5534406 := by exact prefixLift 5534406
  have htrace : WordTrace (prefixWord ++ tailWord_5534406) baseStart_5534406 baseEnd_5534406 := by
    simpa [prefixWord, tailWord_5534406, baseEnd_5534406] using wordTrace_append hprefix tailTrace_5534406
  have hstable : (prefixWord ++ tailWord_5534406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534406).length < 2 ^ (prefixWord ++ tailWord_5534406).sum := by decide
  have hdescent : baseEnd_5534406 < baseStart_5534406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534471 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5534471 : Nat := 118140960795 + 5534471 * 2 ^ 59
def prefixEnd_5534471 : Nat := 4983230072969 + 3 ^ 40 * 5534471 * 2
def baseEnd_5534471 : Nat := 2841843791369721090459937

theorem tailTrace_5534471 : CollatzResearch.WordTrace tailWord_5534471 prefixEnd_5534471 2841843791369721090459937 := by
  unfold tailWord_5534471
  simp only [CollatzResearch.WordTrace]
  refine ⟨201858740732564254239707267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134572493821709502826471511 201858740732564254239707267)
  ·
    refine ⟨302788111098846381359560901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201858740732564254239707267 302788111098846381359560901)
    ·
      refine ⟨56772770831033696504917669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302788111098846381359560901 56772770831033696504917669)
      ·
        refine ⟨10644894530818818094672063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56772770831033696504917669 10644894530818818094672063)
        ·
          refine ⟨15967341796228227142008095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10644894530818818094672063 15967341796228227142008095)
          ·
            refine ⟨23951012694342340713012143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15967341796228227142008095 23951012694342340713012143)
            ·
              refine ⟨35926519041513511069518215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23951012694342340713012143 35926519041513511069518215)
              ·
                refine ⟨53889778562270266604277323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35926519041513511069518215 53889778562270266604277323)
                ·
                  refine ⟨80834667843405399906415985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53889778562270266604277323 80834667843405399906415985)
                  ·
                    refine ⟨60626000882554049929811989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80834667843405399906415985 60626000882554049929811989)
                    ·
                      refine ⟨2841843791369721090459937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60626000882554049929811989 2841843791369721090459937)
                      ·
                        rfl

theorem cell23_5534471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5534471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534471 prefixEnd_5534471 := by exact prefixLift 5534471
  have htrace : WordTrace (prefixWord ++ tailWord_5534471) baseStart_5534471 baseEnd_5534471 := by
    simpa [prefixWord, tailWord_5534471, baseEnd_5534471] using wordTrace_append hprefix tailTrace_5534471
  have hstable : (prefixWord ++ tailWord_5534471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534471).length < 2 ^ (prefixWord ++ tailWord_5534471).sum := by decide
  have hdescent : baseEnd_5534471 < baseStart_5534471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534498 : List Nat := [3, 3, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_5534498 : Nat := 118140960795 + 5534498 * 2 ^ 59
def prefixEnd_5534498 : Nat := 4983230072969 + 3 ^ 40 * 5534498 * 2
def baseEnd_5534498 : Nat := 947285885115797494940771

theorem tailTrace_5534498 : CollatzResearch.WordTrace tailWord_5534498 prefixEnd_5534498 947285885115797494940771 := by
  unfold tailWord_5534498
  simp only [CollatzResearch.WordTrace]
  refine ⟨50464931375866609462735037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134573150335644291900626765 50464931375866609462735037)
  ·
    refine ⟨18924349265949978548525639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50464931375866609462735037 18924349265949978548525639)
    ·
      refine ⟨28386523898924967822788459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18924349265949978548525639 28386523898924967822788459)
      ·
        refine ⟨42579785848387451734182689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28386523898924967822788459 42579785848387451734182689)
        ·
          refine ⟨31934839386290588800637017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42579785848387451734182689 31934839386290588800637017)
          ·
            refine ⟨23951129539717941600477763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31934839386290588800637017 23951129539717941600477763)
            ·
              refine ⟨35926694309576912400716645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23951129539717941600477763 35926694309576912400716645)
              ·
                refine ⟨6736255183045671075134371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35926694309576912400716645 6736255183045671075134371)
                ·
                  refine ⟨10104382774568506612701557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6736255183045671075134371 10104382774568506612701557)
                  ·
                    refine ⟨947285885115797494940771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10104382774568506612701557 947285885115797494940771)
                    ·
                      rfl

theorem cell23_5534498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_5534498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534498 prefixEnd_5534498 := by exact prefixLift 5534498
  have htrace : WordTrace (prefixWord ++ tailWord_5534498) baseStart_5534498 baseEnd_5534498 := by
    simpa [prefixWord, tailWord_5534498, baseEnd_5534498] using wordTrace_append hprefix tailTrace_5534498
  have hstable : (prefixWord ++ tailWord_5534498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534498).length < 2 ^ (prefixWord ++ tailWord_5534498).sum := by decide
  have hdescent : baseEnd_5534498 < baseStart_5534498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534506 : List Nat := [3, 1, 4, 3, 2, 1, 1, 3, 1, 4]
def baseStart_5534506 : Nat := 118140960795 + 5534506 * 2 ^ 59
def prefixEnd_5534506 : Nat := 4983230072969 + 3 ^ 40 * 5534506 * 2
def baseEnd_5534506 : Nat := 947287254397542817840759

theorem tailTrace_5534506 : CollatzResearch.WordTrace tailWord_5534506 prefixEnd_5534506 947287254397542817840759 := by
  unfold tailWord_5534506
  simp only [CollatzResearch.WordTrace]
  refine ⟨50465004321859363804307843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134573344858291636811487581 50465004321859363804307843)
  ·
    refine ⟨75697506482789045706461765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50465004321859363804307843 75697506482789045706461765)
    ·
      refine ⟨14193282465522946069961581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75697506482789045706461765 14193282465522946069961581)
      ·
        refine ⟨5322480924571104776235593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14193282465522946069961581 5322480924571104776235593)
        ·
          refine ⟨3991860693428328582176695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5322480924571104776235593 3991860693428328582176695)
          ·
            refine ⟨5987791040142492873265043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3991860693428328582176695 5987791040142492873265043)
            ·
              refine ⟨8981686560213739309897565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5987791040142492873265043 8981686560213739309897565)
              ·
                refine ⟨3368132460080152241211587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8981686560213739309897565 3368132460080152241211587)
                ·
                  refine ⟨5052198690120228361817381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3368132460080152241211587 5052198690120228361817381)
                  ·
                    refine ⟨947287254397542817840759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5052198690120228361817381 947287254397542817840759)
                    ·
                      rfl

theorem cell23_5534506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_5534506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534506 prefixEnd_5534506 := by exact prefixLift 5534506
  have htrace : WordTrace (prefixWord ++ tailWord_5534506) baseStart_5534506 baseEnd_5534506 := by
    simpa [prefixWord, tailWord_5534506, baseEnd_5534506] using wordTrace_append hprefix tailTrace_5534506
  have hstable : (prefixWord ++ tailWord_5534506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534506).length < 2 ^ (prefixWord ++ tailWord_5534506).sum := by decide
  have hdescent : baseEnd_5534506 < baseStart_5534506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534529 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5534529 : Nat := 118140960795 + 5534529 * 2 ^ 59
def prefixEnd_5534529 : Nat := 4983230072969 + 3 ^ 40 * 5534529 * 2
def baseEnd_5534529 : Nat := 2841873573247681863534671

theorem tailTrace_5534529 : CollatzResearch.WordTrace tailWord_5534529 prefixEnd_5534529 2841873573247681863534671 := by
  unfold tailWord_5534529
  simp only [CollatzResearch.WordTrace]
  refine ⟨201860856166354130145318641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134573904110902753430212427 201860856166354130145318641)
  ·
    refine ⟨151395642124765597608988981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201860856166354130145318641 151395642124765597608988981)
    ·
      refine ⟨14193341449196774775842717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151395642124765597608988981 14193341449196774775842717)
      ·
        refine ⟨5322503043448790540941019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14193341449196774775842717 5322503043448790540941019)
        ·
          refine ⟨7983754565173185811411529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5322503043448790540941019 7983754565173185811411529)
          ·
            refine ⟨5987815923879889358558647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7983754565173185811411529 5987815923879889358558647)
            ·
              refine ⟨8981723885819834037837971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5987815923879889358558647 8981723885819834037837971)
              ·
                refine ⟨13472585828729751056756957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8981723885819834037837971 13472585828729751056756957)
                ·
                  refine ⟨5052219685773656646283859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13472585828729751056756957 5052219685773656646283859)
                  ·
                    refine ⟨7578329528660484969425789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5052219685773656646283859 7578329528660484969425789)
                    ·
                      refine ⟨2841873573247681863534671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7578329528660484969425789 2841873573247681863534671)
                      ·
                        rfl

theorem cell23_5534529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5534529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534529 prefixEnd_5534529 := by exact prefixLift 5534529
  have htrace : WordTrace (prefixWord ++ tailWord_5534529) baseStart_5534529 baseEnd_5534529 := by
    simpa [prefixWord, tailWord_5534529, baseEnd_5534529] using wordTrace_append hprefix tailTrace_5534529
  have hstable : (prefixWord ++ tailWord_5534529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534529).length < 2 ^ (prefixWord ++ tailWord_5534529).sum := by decide
  have hdescent : baseEnd_5534529 < baseStart_5534529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534545 : List Nat := [1, 2, 2, 1, 6, 1, 1, 3, 2, 4]
def baseStart_5534545 : Nat := 118140960795 + 5534545 * 2 ^ 59
def prefixEnd_5534545 : Nat := 4983230072969 + 3 ^ 40 * 5534545 * 2
def baseEnd_5534545 : Nat := 947293929646051266978199

theorem tailTrace_5534545 : CollatzResearch.WordTrace tailWord_5534545 prefixEnd_5534545 947293929646051266978199 := by
  unfold tailWord_5534545
  simp only [CollatzResearch.WordTrace]
  refine ⟨201861439734296164877901089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134574293156197443251934059 201861439734296164877901089)
  ·
    refine ⟨151396079800722123658425817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201861439734296164877901089 151396079800722123658425817)
    ·
      refine ⟨113547059850541592743819363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151396079800722123658425817 113547059850541592743819363)
      ·
        refine ⟨170320589775812389115729045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113547059850541592743819363 170320589775812389115729045)
        ·
          refine ⟨7983777645741205739799799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 170320589775812389115729045 7983777645741205739799799)
          ·
            refine ⟨11975666468611808609699699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7983777645741205739799799 11975666468611808609699699)
            ·
              refine ⟨17963499702917712914549549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11975666468611808609699699 17963499702917712914549549)
              ·
                refine ⟨6736312388594142342956081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17963499702917712914549549 6736312388594142342956081)
                ·
                  refine ⟨5052234291445606757217061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6736312388594142342956081 5052234291445606757217061)
                  ·
                    refine ⟨947293929646051266978199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5052234291445606757217061 947293929646051266978199)
                    ·
                      rfl

theorem cell23_5534545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_5534545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534545 prefixEnd_5534545 := by exact prefixLift 5534545
  have htrace : WordTrace (prefixWord ++ tailWord_5534545) baseStart_5534545 baseEnd_5534545 := by
    simpa [prefixWord, tailWord_5534545, baseEnd_5534545] using wordTrace_append hprefix tailTrace_5534545
  have hstable : (prefixWord ++ tailWord_5534545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534545).length < 2 ^ (prefixWord ++ tailWord_5534545).sum := by decide
  have hdescent : baseEnd_5534545 < baseStart_5534545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534568 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_5534568 : Nat := 118140960795 + 5534568 * 2 ^ 59
def prefixEnd_5534568 : Nat := 4983230072969 + 3 ^ 40 * 5534568 * 2
def baseEnd_5534568 : Nat := 2841893598993207210946991

theorem tailTrace_5534568 : CollatzResearch.WordTrace tailWord_5534568 prefixEnd_5534568 2841893598993207210946991 := by
  unfold tailWord_5534568
  simp only [CollatzResearch.WordTrace]
  refine ⟨100931139306606419902994179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134574852408808559870658905 100931139306606419902994179)
  ·
    refine ⟨151396708959909629854491269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100931139306606419902994179 151396708959909629854491269)
    ·
      refine ⟨28386882929983055597717113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151396708959909629854491269 28386882929983055597717113)
      ·
        refine ⟨21290162197487291698287835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28386882929983055597717113 21290162197487291698287835)
        ·
          refine ⟨31935243296230937547431753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21290162197487291698287835 31935243296230937547431753)
          ·
            refine ⟨23951432472173203160573815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31935243296230937547431753 23951432472173203160573815)
            ·
              refine ⟨35927148708259804740860723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23951432472173203160573815 35927148708259804740860723)
              ·
                refine ⟨53890723062389707111291085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35927148708259804740860723 53890723062389707111291085)
                ·
                  refine ⟨20209021148396140166734157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53890723062389707111291085 20209021148396140166734157)
                  ·
                    refine ⟨7578382930648552562525309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20209021148396140166734157 7578382930648552562525309)
                    ·
                      refine ⟨2841893598993207210946991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7578382930648552562525309 2841893598993207210946991)
                      ·
                        rfl

theorem cell23_5534568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_5534568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534568 prefixEnd_5534568 := by exact prefixLift 5534568
  have htrace : WordTrace (prefixWord ++ tailWord_5534568) baseStart_5534568 baseEnd_5534568 := by
    simpa [prefixWord, tailWord_5534568, baseEnd_5534568] using wordTrace_append hprefix tailTrace_5534568
  have hstable : (prefixWord ++ tailWord_5534568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534568).length < 2 ^ (prefixWord ++ tailWord_5534568).sum := by decide
  have hdescent : baseEnd_5534568 < baseStart_5534568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534585 : List Nat := [1, 2, 1, 3, 2, 3, 1, 4, 2, 1, 3]
def baseStart_5534585 : Nat := 118140960795 + 5534585 * 2 ^ 59
def prefixEnd_5534585 : Nat := 4983230072969 + 3 ^ 40 * 5534585 * 2
def baseEnd_5534585 : Nat := 2841902328164333644434413

theorem tailTrace_5534585 : CollatzResearch.WordTrace tailWord_5534585 prefixEnd_5534585 2841902328164333644434413 := by
  unfold tailWord_5534585
  simp only [CollatzResearch.WordTrace]
  refine ⟨201862898654151251709357209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134575265769434167806238139 201862898654151251709357209)
  ·
    refine ⟨151397173990613438782017907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201862898654151251709357209 151397173990613438782017907)
    ·
      refine ⟨227095760985920158173026861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151397173990613438782017907 227095760985920158173026861)
      ·
        refine ⟨85160910369720059314885073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227095760985920158173026861 85160910369720059314885073)
        ·
          refine ⟨63870682777290044486163805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85160910369720059314885073 63870682777290044486163805)
          ·
            refine ⟨23951506041483766682311427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63870682777290044486163805 23951506041483766682311427)
            ·
              refine ⟨35927259062225650023467141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23951506041483766682311427 35927259062225650023467141)
              ·
                refine ⟨6736361074167309379400089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35927259062225650023467141 6736361074167309379400089)
                ·
                  refine ⟨5052270805625482034550067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6736361074167309379400089 5052270805625482034550067)
                  ·
                    refine ⟨7578406208438223051825101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5052270805625482034550067 7578406208438223051825101)
                    ·
                      refine ⟨2841902328164333644434413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7578406208438223051825101 2841902328164333644434413)
                      ·
                        rfl

theorem cell23_5534585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_5534585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534585 prefixEnd_5534585 := by exact prefixLift 5534585
  have htrace : WordTrace (prefixWord ++ tailWord_5534585) baseStart_5534585 baseEnd_5534585 := by
    simpa [prefixWord, tailWord_5534585, baseEnd_5534585] using wordTrace_append hprefix tailTrace_5534585
  have hstable : (prefixWord ++ tailWord_5534585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534585).length < 2 ^ (prefixWord ++ tailWord_5534585).sum := by decide
  have hdescent : baseEnd_5534585 < baseStart_5534585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534591 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 4]
def baseStart_5534591 : Nat := 118140960795 + 5534591 * 2 ^ 59
def prefixEnd_5534591 : Nat := 4983230072969 + 3 ^ 40 * 5534591 * 2
def baseEnd_5534591 : Nat := 2841905409048260620959385

theorem tailTrace_5534591 : CollatzResearch.WordTrace tailWord_5534591 prefixEnd_5534591 2841905409048260620959385 := by
  unfold tailWord_5534591
  simp only [CollatzResearch.WordTrace]
  refine ⟨201863117492129514734075627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134575411661419676489383751 201863117492129514734075627)
  ·
    refine ⟨302794676238194272101113441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201863117492129514734075627 302794676238194272101113441)
    ·
      refine ⟨227096007178645704075835081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302794676238194272101113441 227096007178645704075835081)
      ·
        refine ⟨170322005383984278056876311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227096007178645704075835081 170322005383984278056876311)
        ·
          refine ⟨255483008075976417085314467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170322005383984278056876311 255483008075976417085314467)
          ·
            refine ⟨383224512113964625627971701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255483008075976417085314467 383224512113964625627971701)
            ·
              refine ⟨35927298010684183652622347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 383224512113964625627971701 35927298010684183652622347)
              ·
                refine ⟨53890947016026275478933521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35927298010684183652622347 53890947016026275478933521)
                ·
                  refine ⟨40418210262019706609200141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53890947016026275478933521 40418210262019706609200141)
                  ·
                    refine ⟨15156828848257389978450053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40418210262019706609200141 15156828848257389978450053)
                    ·
                      refine ⟨2841905409048260620959385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15156828848257389978450053 2841905409048260620959385)
                      ·
                        rfl

theorem cell23_5534591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_5534591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534591 prefixEnd_5534591 := by exact prefixLift 5534591
  have htrace : WordTrace (prefixWord ++ tailWord_5534591) baseStart_5534591 baseEnd_5534591 := by
    simpa [prefixWord, tailWord_5534591, baseEnd_5534591] using wordTrace_append hprefix tailTrace_5534591
  have hstable : (prefixWord ++ tailWord_5534591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534591).length < 2 ^ (prefixWord ++ tailWord_5534591).sum := by decide
  have hdescent : baseEnd_5534591 < baseStart_5534591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534601 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 1, 8]
def baseStart_5534601 : Nat := 118140960795 + 5534601 * 2 ^ 59
def prefixEnd_5534601 : Nat := 4983230072969 + 3 ^ 40 * 5534601 * 2
def baseEnd_5534601 : Nat := 947303514618268527278113

theorem tailTrace_5534601 : CollatzResearch.WordTrace tailWord_5534601 prefixEnd_5534601 947303514618268527278113 := by
  unfold tailWord_5534601
  simp only [CollatzResearch.WordTrace]
  refine ⟨201863482222093286441939657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134575654814728857627959771 201863482222093286441939657)
  ·
    refine ⟨151397611666569964831454743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201863482222093286441939657 151397611666569964831454743)
    ·
      refine ⟨227096417499854947247182115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151397611666569964831454743 227096417499854947247182115)
      ·
        refine ⟨340644626249782420870773173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227096417499854947247182115 340644626249782420870773173)
        ·
          refine ⟨31935433710917101956634985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 340644626249782420870773173 31935433710917101956634985)
          ·
            refine ⟨23951575283187826467476239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31935433710917101956634985 23951575283187826467476239)
            ·
              refine ⟨35927362924781739701214359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23951575283187826467476239 35927362924781739701214359)
              ·
                refine ⟨53891044387172609551821539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35927362924781739701214359 53891044387172609551821539)
                ·
                  refine ⟨80836566580758914327732309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53891044387172609551821539 80836566580758914327732309)
                  ·
                    refine ⟨947303514618268527278113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80836566580758914327732309 947303514618268527278113)
                    ·
                      rfl

theorem cell23_5534601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_5534601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534601 prefixEnd_5534601 := by exact prefixLift 5534601
  have htrace : WordTrace (prefixWord ++ tailWord_5534601) baseStart_5534601 baseEnd_5534601 := by
    simpa [prefixWord, tailWord_5534601, baseEnd_5534601] using wordTrace_append hprefix tailTrace_5534601
  have hstable : (prefixWord ++ tailWord_5534601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534601).length < 2 ^ (prefixWord ++ tailWord_5534601).sum := by decide
  have hdescent : baseEnd_5534601 < baseStart_5534601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534602 : List Nat := [3, 1, 2, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_5534602 : Nat := 118140960795 + 5534602 * 2 ^ 59
def prefixEnd_5534602 : Nat := 4983230072969 + 3 ^ 40 * 5534602 * 2
def baseEnd_5534602 : Nat := 2841911057335460077921835

theorem tailTrace_5534602 : CollatzResearch.WordTrace tailWord_5534602 prefixEnd_5534602 2841911057335460077921835 := by
  unfold tailWord_5534602
  simp only [CollatzResearch.WordTrace]
  refine ⟨50465879673772415903181515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134575679130059775741817373 50465879673772415903181515)
  ·
    refine ⟨75698819510658623854772273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50465879673772415903181515 75698819510658623854772273)
    ·
      refine ⟨56774114632993967891079205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75698819510658623854772273 56774114632993967891079205)
      ·
        refine ⟨10645146493686368979577351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56774114632993967891079205 10645146493686368979577351)
        ·
          refine ⟨15967719740529553469366027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10645146493686368979577351 15967719740529553469366027)
          ·
            refine ⟨23951579610794330204049041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15967719740529553469366027 23951579610794330204049041)
            ·
              refine ⟨17963684708095747653036781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23951579610794330204049041 17963684708095747653036781)
              ·
                refine ⟨6736381765535905369888793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17963684708095747653036781 6736381765535905369888793)
                ·
                  refine ⟨5052286324151929027416595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6736381765535905369888793 5052286324151929027416595)
                  ·
                    refine ⟨7578429486227893541124893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5052286324151929027416595 7578429486227893541124893)
                    ·
                      refine ⟨2841911057335460077921835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7578429486227893541124893 2841911057335460077921835)
                      ·
                        rfl

theorem cell23_5534602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_5534602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534602 prefixEnd_5534602 := by exact prefixLift 5534602
  have htrace : WordTrace (prefixWord ++ tailWord_5534602) baseStart_5534602 baseEnd_5534602 := by
    simpa [prefixWord, tailWord_5534602, baseEnd_5534602] using wordTrace_append hprefix tailTrace_5534602
  have hstable : (prefixWord ++ tailWord_5534602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534602).length < 2 ^ (prefixWord ++ tailWord_5534602).sum := by decide
  have hdescent : baseEnd_5534602 < baseStart_5534602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534611 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 5]
def baseStart_5534611 : Nat := 118140960795 + 5534611 * 2 ^ 59
def prefixEnd_5534611 : Nat := 4983230072969 + 3 ^ 40 * 5534611 * 2
def baseEnd_5534611 : Nat := 2841915678661350542709293

theorem tailTrace_5534611 : CollatzResearch.WordTrace tailWord_5534611 prefixEnd_5534611 2841915678661350542709293 := by
  unfold tailWord_5534611
  simp only [CollatzResearch.WordTrace]
  refine ⟨201863846952057058149803687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134575897968038038766535791 201863846952057058149803687)
  ·
    refine ⟨302795770428085587224705531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201863846952057058149803687 302795770428085587224705531)
    ·
      refine ⟨454193655642128380837058297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302795770428085587224705531 454193655642128380837058297)
      ·
        refine ⟨340645241731596285627793723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454193655642128380837058297 340645241731596285627793723)
        ·
          refine ⟨510967862597394428441690585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340645241731596285627793723 510967862597394428441690585)
          ·
            refine ⟨383225896948045821331267939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510967862597394428441690585 383225896948045821331267939)
            ·
              refine ⟨574838845422068731996901909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383225896948045821331267939 574838845422068731996901909)
              ·
                refine ⟨26945570879159471812354777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 574838845422068731996901909 26945570879159471812354777)
                ·
                  refine ⟨20209178159369603859266083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26945570879159471812354777 20209178159369603859266083)
                  ·
                    refine ⟨30313767239054405788899125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20209178159369603859266083 30313767239054405788899125)
                    ·
                      refine ⟨2841915678661350542709293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30313767239054405788899125 2841915678661350542709293)
                      ·
                        rfl

theorem cell23_5534611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_5534611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534611 prefixEnd_5534611 := by exact prefixLift 5534611
  have htrace : WordTrace (prefixWord ++ tailWord_5534611) baseStart_5534611 baseEnd_5534611 := by
    simpa [prefixWord, tailWord_5534611, baseEnd_5534611] using wordTrace_append hprefix tailTrace_5534611
  have hstable : (prefixWord ++ tailWord_5534611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534611).length < 2 ^ (prefixWord ++ tailWord_5534611).sum := by decide
  have hdescent : baseEnd_5534611 < baseStart_5534611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534612 : List Nat := [2, 4, 2, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_5534612 : Nat := 118140960795 + 5534612 * 2 ^ 59
def prefixEnd_5534612 : Nat := 4983230072969 + 3 ^ 40 * 5534612 * 2
def baseEnd_5534612 : Nat := 2841916192142005038796789

theorem tailTrace_5534612 : CollatzResearch.WordTrace tailWord_5534612 prefixEnd_5534612 2841916192142005038796789 := by
  unfold tailWord_5534612
  simp only [CollatzResearch.WordTrace]
  refine ⟨100931941712526717660295045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134575922283368956880393393 100931941712526717660295045)
  ·
    refine ⟨18924739071098759561305321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100931941712526717660295045 18924739071098759561305321)
    ·
      refine ⟨14193554303324069670978991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18924739071098759561305321 14193554303324069670978991)
      ·
        refine ⟨21290331454986104506468487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14193554303324069670978991 21290331454986104506468487)
        ·
          refine ⟨31935497182479156759702731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21290331454986104506468487 31935497182479156759702731)
          ·
            refine ⟨47903245773718735139554097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31935497182479156759702731 47903245773718735139554097)
            ·
              refine ⟨35927434330289051354665573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47903245773718735139554097 35927434330289051354665573)
              ·
                refine ⟨6736393936929197128999795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35927434330289051354665573 6736393936929197128999795)
                ·
                  refine ⟨10104590905393795693499693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6736393936929197128999795 10104590905393795693499693)
                  ·
                    refine ⟨3789221589522673385062385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10104590905393795693499693 3789221589522673385062385)
                    ·
                      refine ⟨2841916192142005038796789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3789221589522673385062385 2841916192142005038796789)
                      ·
                        rfl

theorem cell23_5534612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_5534612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534612 prefixEnd_5534612 := by exact prefixLift 5534612
  have htrace : WordTrace (prefixWord ++ tailWord_5534612) baseStart_5534612 baseEnd_5534612 := by
    simpa [prefixWord, tailWord_5534612, baseEnd_5534612] using wordTrace_append hprefix tailTrace_5534612
  have hstable : (prefixWord ++ tailWord_5534612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534612).length < 2 ^ (prefixWord ++ tailWord_5534612).sum := by decide
  have hdescent : baseEnd_5534612 < baseStart_5534612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534648 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 7]
def baseStart_5534648 : Nat := 118140960795 + 5534648 * 2 ^ 59
def prefixEnd_5534648 : Nat := 4983230072969 + 3 ^ 40 * 5534648 * 2
def baseEnd_5534648 : Nat := 315770519716174099771847

theorem tailTrace_5534648 : CollatzResearch.WordTrace tailWord_5534648 prefixEnd_5534648 315770519716174099771847 := by
  unfold tailWord_5534648
  simp only [CollatzResearch.WordTrace]
  refine ⟨100932598226461506734450299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134576797635282008979267065 100932598226461506734450299)
  ·
    refine ⟨151398897339692260101675449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100932598226461506734450299 151398897339692260101675449)
    ·
      refine ⟨113549173004769195076256587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151398897339692260101675449 113549173004769195076256587)
      ·
        refine ⟨170323759507153792614384881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113549173004769195076256587 170323759507153792614384881)
        ·
          refine ⟨127742819630365344460788661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170323759507153792614384881 127742819630365344460788661)
          ·
            refine ⟨11975889340346751043198937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127742819630365344460788661 11975889340346751043198937)
            ·
              refine ⟨8981917005260063282399203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11975889340346751043198937 8981917005260063282399203)
              ·
                refine ⟨13472875507890094923598805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8981917005260063282399203 13472875507890094923598805)
                ·
                  refine ⟨315770519716174099771847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13472875507890094923598805 315770519716174099771847)
                  ·
                    rfl

theorem cell23_5534648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 7].length) (baseStart_5534648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534648 prefixEnd_5534648 := by exact prefixLift 5534648
  have htrace : WordTrace (prefixWord ++ tailWord_5534648) baseStart_5534648 baseEnd_5534648 := by
    simpa [prefixWord, tailWord_5534648, baseEnd_5534648] using wordTrace_append hprefix tailTrace_5534648
  have hstable : (prefixWord ++ tailWord_5534648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534648).length < 2 ^ (prefixWord ++ tailWord_5534648).sum := by decide
  have hdescent : baseEnd_5534648 < baseStart_5534648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534682 : List Nat := [3, 1, 1, 2, 4, 3, 1, 3, 5]
def baseStart_5534682 : Nat := 118140960795 + 5534682 * 2 ^ 59
def prefixEnd_5534682 : Nat := 4983230072969 + 3 ^ 40 * 5534682 * 2
def baseEnd_5534682 : Nat := 315772459531979973880163

theorem tailTrace_5534682 : CollatzResearch.WordTrace tailWord_5534682 prefixEnd_5534682 315772459531979973880163 := by
  unfold tailWord_5534682
  simp only [CollatzResearch.WordTrace]
  refine ⟨50466609133699959318909575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134577624356533224850425533 50466609133699959318909575)
  ·
    refine ⟨75699913700549938978364363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50466609133699959318909575 75699913700549938978364363)
    ·
      refine ⟨113549870550824908467546545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75699913700549938978364363 113549870550824908467546545)
      ·
        refine ⟨85162402913118681350659909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113549870550824908467546545 85162402913118681350659909)
        ·
          refine ⟨15967950546209752753248733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85162402913118681350659909 15967950546209752753248733)
          ·
            refine ⟨5987981454828657282468275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15967950546209752753248733 5987981454828657282468275)
            ·
              refine ⟨8981972182242985923702413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5987981454828657282468275 8981972182242985923702413)
              ·
                refine ⟨3368239568341119721388405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8981972182242985923702413 3368239568341119721388405)
                ·
                  refine ⟨315772459531979973880163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3368239568341119721388405 315772459531979973880163)
                  ·
                    rfl

theorem cell23_5534682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 5].length) (baseStart_5534682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534682 prefixEnd_5534682 := by exact prefixLift 5534682
  have htrace : WordTrace (prefixWord ++ tailWord_5534682) baseStart_5534682 baseEnd_5534682 := by
    simpa [prefixWord, tailWord_5534682, baseEnd_5534682] using wordTrace_append hprefix tailTrace_5534682
  have hstable : (prefixWord ++ tailWord_5534682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534682).length < 2 ^ (prefixWord ++ tailWord_5534682).sum := by decide
  have hdescent : baseEnd_5534682 < baseStart_5534682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534695 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 2, 5]
def baseStart_5534695 : Nat := 118140960795 + 5534695 * 2 ^ 59
def prefixEnd_5534695 : Nat := 4983230072969 + 3 ^ 40 * 5534695 * 2
def baseEnd_5534695 : Nat := 947319603678776071352969

theorem tailTrace_5534695 : CollatzResearch.WordTrace tailWord_5534695 prefixEnd_5534695 947319603678776071352969 := by
  unfold tailWord_5534695
  simp only [CollatzResearch.WordTrace]
  refine ⟨201866910683752740495861539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134577940455835160330574359 201866910683752740495861539)
  ·
    refine ⟨302800366025629110743792309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201866910683752740495861539 302800366025629110743792309)
    ·
      refine ⟨28387534314902729132230529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 302800366025629110743792309 28387534314902729132230529)
      ·
        refine ⟨21290650736177046849172897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28387534314902729132230529 21290650736177046849172897)
        ·
          refine ⟨15967988052132785136879673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21290650736177046849172897 15967988052132785136879673)
          ·
            refine ⟨11975991039099588852659755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15967988052132785136879673 11975991039099588852659755)
            ·
              refine ⟨17963986558649383278989633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11975991039099588852659755 17963986558649383278989633)
              ·
                refine ⟨13472989918987037459242225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17963986558649383278989633 13472989918987037459242225)
                ·
                  refine ⟨10104742439240278094431669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13472989918987037459242225 10104742439240278094431669)
                  ·
                    refine ⟨947319603678776071352969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10104742439240278094431669 947319603678776071352969)
                    ·
                      rfl

theorem cell23_5534695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_5534695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534695 prefixEnd_5534695 := by exact prefixLift 5534695
  have htrace : WordTrace (prefixWord ++ tailWord_5534695) baseStart_5534695 baseEnd_5534695 := by
    simpa [prefixWord, tailWord_5534695, baseEnd_5534695] using wordTrace_append hprefix tailTrace_5534695
  have hstable : (prefixWord ++ tailWord_5534695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534695).length < 2 ^ (prefixWord ++ tailWord_5534695).sum := by decide
  have hdescent : baseEnd_5534695 < baseStart_5534695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534755 : List Nat := [1, 1, 1, 4, 3, 3, 2, 2, 6]
def baseStart_5534755 : Nat := 118140960795 + 5534755 * 2 ^ 59
def prefixEnd_5534755 : Nat := 4983230072969 + 3 ^ 40 * 5534755 * 2
def baseEnd_5534755 : Nat := 315776624430621997700959

theorem tailTrace_5534755 : CollatzResearch.WordTrace tailWord_5534755 prefixEnd_5534755 315776624430621997700959 := by
  unfold tailWord_5534755
  simp only [CollatzResearch.WordTrace]
  refine ⟨201869099063535370743045719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134579399375690247162030479 201869099063535370743045719)
  ·
    refine ⟨302803648595303056114568579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201869099063535370743045719 302803648595303056114568579)
    ·
      refine ⟨454205472892954584171852869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302803648595303056114568579 454205472892954584171852869)
      ·
        refine ⟨85163526167428984532222413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 454205472892954584171852869 85163526167428984532222413)
        ·
          refine ⟨31936322312785869199583405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85163526167428984532222413 31936322312785869199583405)
          ·
            refine ⟨11976120867294700949843777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31936322312785869199583405 11976120867294700949843777)
            ·
              refine ⟨8982090650471025712382833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11976120867294700949843777 8982090650471025712382833)
              ·
                refine ⟨6736567987853269284287125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8982090650471025712382833 6736567987853269284287125)
                ·
                  refine ⟨315776624430621997700959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6736567987853269284287125 315776624430621997700959)
                  ·
                    rfl

theorem cell23_5534755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 6].length) (baseStart_5534755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534755 prefixEnd_5534755 := by exact prefixLift 5534755
  have htrace : WordTrace (prefixWord ++ tailWord_5534755) baseStart_5534755 baseEnd_5534755 := by
    simpa [prefixWord, tailWord_5534755, baseEnd_5534755] using wordTrace_append hprefix tailTrace_5534755
  have hstable : (prefixWord ++ tailWord_5534755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534755).length < 2 ^ (prefixWord ++ tailWord_5534755).sum := by decide
  have hdescent : baseEnd_5534755 < baseStart_5534755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534768 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 5, 5]
def baseStart_5534768 : Nat := 118140960795 + 5534768 * 2 ^ 59
def prefixEnd_5534768 : Nat := 4983230072969 + 3 ^ 40 * 5534768 * 2
def baseEnd_5534768 : Nat := 947332098374702142815357

theorem tailTrace_5534768 : CollatzResearch.WordTrace tailWord_5534768 prefixEnd_5534768 947332098374702142815357 := by
  unfold tailWord_5534768
  simp only [CollatzResearch.WordTrace]
  refine ⟨100934786606244136981634479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134579715474992182642179305 100934786606244136981634479)
  ·
    refine ⟨151402179909366205472451719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100934786606244136981634479 151402179909366205472451719)
    ·
      refine ⟨227103269864049308208677579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151402179909366205472451719 227103269864049308208677579)
      ·
        refine ⟨340654904796073962313016369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227103269864049308208677579 340654904796073962313016369)
        ·
          refine ⟨255491178597055471734762277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340654904796073962313016369 255491178597055471734762277)
          ·
            refine ⟨47904595986947900950267927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255491178597055471734762277 47904595986947900950267927)
            ·
              refine ⟨71856893980421851425401891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47904595986947900950267927 71856893980421851425401891)
              ·
                refine ⟨107785340970632777138102837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71856893980421851425401891 107785340970632777138102837)
                ·
                  refine ⟨10104875715996822856697141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107785340970632777138102837 10104875715996822856697141)
                  ·
                    refine ⟨947332098374702142815357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10104875715996822856697141 947332098374702142815357)
                    ·
                      rfl

theorem cell23_5534768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5, 5].length) (baseStart_5534768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534768 prefixEnd_5534768 := by exact prefixLift 5534768
  have htrace : WordTrace (prefixWord ++ tailWord_5534768) baseStart_5534768 baseEnd_5534768 := by
    simpa [prefixWord, tailWord_5534768, baseEnd_5534768] using wordTrace_append hprefix tailTrace_5534768
  have hstable : (prefixWord ++ tailWord_5534768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534768).length < 2 ^ (prefixWord ++ tailWord_5534768).sum := by decide
  have hdescent : baseEnd_5534768 < baseStart_5534768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534772 : List Nat := [2, 5, 1, 2, 1, 1, 2, 3, 6]
def baseStart_5534772 : Nat := 118140960795 + 5534772 * 2 ^ 59
def prefixEnd_5534772 : Nat := 4983230072969 + 3 ^ 40 * 5534772 * 2
def baseEnd_5534772 : Nat := 315777594338524934755117

theorem tailTrace_5534772 : CollatzResearch.WordTrace tailWord_5534772 prefixEnd_5534772 315777594338524934755117 := by
  unfold tailWord_5534772
  simp only [CollatzResearch.WordTrace]
  refine ⟨100934859552236891323207285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134579812736315855097609713 100934859552236891323207285)
  ·
    refine ⟨9462643083022208561550683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100934859552236891323207285 9462643083022208561550683)
    ·
      refine ⟨14193964624533312842326025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9462643083022208561550683 14193964624533312842326025)
      ·
        refine ⟨10645473468399984631744519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14193964624533312842326025 10645473468399984631744519)
        ·
          refine ⟨15968210202599976947616779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10645473468399984631744519 15968210202599976947616779)
          ·
            refine ⟨23952315303899965421425169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15968210202599976947616779 23952315303899965421425169)
            ·
              refine ⟨17964236477924974066068877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23952315303899965421425169 17964236477924974066068877)
              ·
                refine ⟨6736588679221865274775829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17964236477924974066068877 6736588679221865274775829)
                ·
                  refine ⟨315777594338524934755117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6736588679221865274775829 315777594338524934755117)
                  ·
                    rfl

theorem cell23_5534772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_5534772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534772 prefixEnd_5534772 := by exact prefixLift 5534772
  have htrace : WordTrace (prefixWord ++ tailWord_5534772) baseStart_5534772 baseEnd_5534772 := by
    simpa [prefixWord, tailWord_5534772, baseEnd_5534772] using wordTrace_append hprefix tailTrace_5534772
  have hstable : (prefixWord ++ tailWord_5534772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534772).length < 2 ^ (prefixWord ++ tailWord_5534772).sum := by decide
  have hdescent : baseEnd_5534772 < baseStart_5534772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534775 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 1, 5, 2]
def baseStart_5534775 : Nat := 118140960795 + 5534775 * 2 ^ 59
def prefixEnd_5534775 : Nat := 4983230072969 + 3 ^ 40 * 5534775 * 2
def baseEnd_5534775 : Nat := 2841999889488687901058539

theorem tailTrace_5534775 : CollatzResearch.WordTrace tailWord_5534775 prefixEnd_5534775 2841999889488687901058539 := by
  unfold tailWord_5534775
  simp only [CollatzResearch.WordTrace]
  refine ⟨201869828523462914158773779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134579885682308609439182519 201869828523462914158773779)
  ·
    refine ⟨302804742785194371238160669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201869828523462914158773779 302804742785194371238160669)
    ·
      refine ⟨113551778544447889214310251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302804742785194371238160669 113551778544447889214310251)
      ·
        refine ⟨170327667816671833821465377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113551778544447889214310251 170327667816671833821465377)
        ·
          refine ⟨127745750862503875366099033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170327667816671833821465377 127745750862503875366099033)
          ·
            refine ⟨95809313146877906524574275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127745750862503875366099033 95809313146877906524574275)
            ·
              refine ⟨143713969720316859786861413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95809313146877906524574275 143713969720316859786861413)
              ·
                refine ⟨26946369322559411210036515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143713969720316859786861413 26946369322559411210036515)
                ·
                  refine ⟨40419553983839116815054773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26946369322559411210036515 40419553983839116815054773)
                  ·
                    refine ⟨3789333185984917201411385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40419553983839116815054773 3789333185984917201411385)
                    ·
                      refine ⟨2841999889488687901058539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3789333185984917201411385 2841999889488687901058539)
                      ·
                        rfl

theorem cell23_5534775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 5, 2].length) (baseStart_5534775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534775 prefixEnd_5534775 := by exact prefixLift 5534775
  have htrace : WordTrace (prefixWord ++ tailWord_5534775) baseStart_5534775 baseEnd_5534775 := by
    simpa [prefixWord, tailWord_5534775, baseEnd_5534775] using wordTrace_append hprefix tailTrace_5534775
  have hstable : (prefixWord ++ tailWord_5534775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534775).length < 2 ^ (prefixWord ++ tailWord_5534775).sum := by decide
  have hdescent : baseEnd_5534775 < baseStart_5534775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534802 : List Nat := [3, 2, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_5534802 : Nat := 118140960795 + 5534802 * 2 ^ 59
def prefixEnd_5534802 : Nat := 4983230072969 + 3 ^ 40 * 5534802 * 2
def baseEnd_5534802 : Nat := 947337917822119765140305

theorem tailTrace_5534802 : CollatzResearch.WordTrace tailWord_5534802 prefixEnd_5534802 947337917822119765140305 := by
  unfold tailWord_5534802
  simp only [CollatzResearch.WordTrace]
  refine ⟨50467703323591274442501665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134580542196243398513337773 50467703323591274442501665)
  ·
    refine ⟨37850777492693455831876249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50467703323591274442501665 37850777492693455831876249)
    ·
      refine ⟨28388083119520091873907187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37850777492693455831876249 28388083119520091873907187)
      ·
        refine ⟨42582124679280137810860781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28388083119520091873907187 42582124679280137810860781)
        ·
          refine ⟨15968296754730051679072793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42582124679280137810860781 15968296754730051679072793)
          ·
            refine ⟨11976222566047538759304595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15968296754730051679072793 11976222566047538759304595)
            ·
              refine ⟨17964333849071308138956893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11976222566047538759304595 17964333849071308138956893)
              ·
                refine ⟨6736625193401740552108835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17964333849071308138956893 6736625193401740552108835)
                ·
                  refine ⟨10104937790102610828163253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6736625193401740552108835 10104937790102610828163253)
                  ·
                    refine ⟨947337917822119765140305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10104937790102610828163253 947337917822119765140305)
                    ·
                      rfl

theorem cell23_5534802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_5534802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534802 prefixEnd_5534802 := by exact prefixLift 5534802
  have htrace : WordTrace (prefixWord ++ tailWord_5534802) baseStart_5534802 baseEnd_5534802 := by
    simpa [prefixWord, tailWord_5534802, baseEnd_5534802] using wordTrace_append hprefix tailTrace_5534802
  have hstable : (prefixWord ++ tailWord_5534802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534802).length < 2 ^ (prefixWord ++ tailWord_5534802).sum := by decide
  have hdescent : baseEnd_5534802 < baseStart_5534802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534806 : List Nat := [5, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_5534806 : Nat := 118140960795 + 5534806 * 2 ^ 59
def prefixEnd_5534806 : Nat := 4983230072969 + 3 ^ 40 * 5534806 * 2
def baseEnd_5534806 : Nat := 315779534154330808863433

theorem tailTrace_5534806 : CollatzResearch.WordTrace tailWord_5534806 prefixEnd_5534806 315779534154330808863433 := by
  unfold tailWord_5534806
  simp only [CollatzResearch.WordTrace]
  refine ⟨12616934949146912903322017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134580639457567070968768181 12616934949146912903322017)
  ·
    refine ⟨9462701211860184677491513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12616934949146912903322017 9462701211860184677491513)
    ·
      refine ⟨7097025908895138508118635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9462701211860184677491513 7097025908895138508118635)
      ·
        refine ⟨10645538863342707762177953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7097025908895138508118635 10645538863342707762177953)
        ·
          refine ⟨7984154147507030821633465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10645538863342707762177953 7984154147507030821633465)
          ·
            refine ⟨5988115610630273116225099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7984154147507030821633465 5988115610630273116225099)
            ·
              refine ⟨8982173415945409674337649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5988115610630273116225099 8982173415945409674337649)
              ·
                refine ⟨6736630061959057255753237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8982173415945409674337649 6736630061959057255753237)
                ·
                  refine ⟨315779534154330808863433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6736630061959057255753237 315779534154330808863433)
                  ·
                    rfl

theorem cell23_5534806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_5534806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534806 prefixEnd_5534806 := by exact prefixLift 5534806
  have htrace : WordTrace (prefixWord ++ tailWord_5534806) baseStart_5534806 baseEnd_5534806 := by
    simpa [prefixWord, tailWord_5534806, baseEnd_5534806] using wordTrace_append hprefix tailTrace_5534806
  have hstable : (prefixWord ++ tailWord_5534806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534806).length < 2 ^ (prefixWord ++ tailWord_5534806).sum := by decide
  have hdescent : baseEnd_5534806 < baseStart_5534806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534815 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 4, 4]
def baseStart_5534815 : Nat := 118140960795 + 5534815 * 2 ^ 59
def prefixEnd_5534815 : Nat := 4983230072969 + 3 ^ 40 * 5534815 * 2
def baseEnd_5534815 : Nat := 947340142904955914852785

theorem tailTrace_5534815 : CollatzResearch.WordTrace tailWord_5534815 prefixEnd_5534815 947340142904955914852785 := by
  unfold tailWord_5534815
  simp only [CollatzResearch.WordTrace]
  refine ⟨201871287443318000990229899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134580858295545333993486599 201871287443318000990229899)
  ·
    refine ⟨302806931164977001485344849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201871287443318000990229899 302806931164977001485344849)
    ·
      refine ⟨227105198373732751114008637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302806931164977001485344849 227105198373732751114008637)
      ·
        refine ⟨85164449390149781667753239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227105198373732751114008637 85164449390149781667753239)
        ·
          refine ⟨127746674085224672501629859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85164449390149781667753239 127746674085224672501629859)
          ·
            refine ⟨191620011127837008752444789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127746674085224672501629859 191620011127837008752444789)
            ·
              refine ⟨17964376043234719570541699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191620011127837008752444789 17964376043234719570541699)
              ·
                refine ⟨26946564064852079355812549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17964376043234719570541699 26946564064852079355812549)
                ·
                  refine ⟨5052480762159764879214853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26946564064852079355812549 5052480762159764879214853)
                  ·
                    refine ⟨947340142904955914852785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5052480762159764879214853 947340142904955914852785)
                    ·
                      rfl

theorem cell23_5534815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 4].length) (baseStart_5534815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534815 prefixEnd_5534815 := by exact prefixLift 5534815
  have htrace : WordTrace (prefixWord ++ tailWord_5534815) baseStart_5534815 baseEnd_5534815 := by
    simpa [prefixWord, tailWord_5534815, baseEnd_5534815] using wordTrace_append hprefix tailTrace_5534815
  have hstable : (prefixWord ++ tailWord_5534815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534815).length < 2 ^ (prefixWord ++ tailWord_5534815).sum := by decide
  have hdescent : baseEnd_5534815 < baseStart_5534815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534825 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 5]
def baseStart_5534825 : Nat := 118140960795 + 5534825 * 2 ^ 59
def prefixEnd_5534825 : Nat := 4983230072969 + 3 ^ 40 * 5534825 * 2
def baseEnd_5534825 : Nat := 2842025563521412705433309

theorem tailTrace_5534825 : CollatzResearch.WordTrace tailWord_5534825 prefixEnd_5534825 2842025563521412705433309 := by
  unfold tailWord_5534825
  simp only [CollatzResearch.WordTrace]
  refine ⟨201871652173281772698093929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134581101448854515132062619 201871652173281772698093929)
  ·
    refine ⟨151403739129961329523570447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201871652173281772698093929 151403739129961329523570447)
    ·
      refine ⟨227105608694941994285355671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151403739129961329523570447 227105608694941994285355671)
      ·
        refine ⟨340658413042412991428033507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227105608694941994285355671 340658413042412991428033507)
        ·
          refine ⟨510987619563619487142050261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340658413042412991428033507 510987619563619487142050261)
          ·
            refine ⟨11976272333522331729891803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 510987619563619487142050261 11976272333522331729891803)
            ·
              refine ⟨17964408500283497594837705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11976272333522331729891803 17964408500283497594837705)
              ·
                refine ⟨13473306375212623196128279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17964408500283497594837705 13473306375212623196128279)
                ·
                  refine ⟨20209959562818934794192419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13473306375212623196128279 20209959562818934794192419)
                  ·
                    refine ⟨30314939344228402191288629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20209959562818934794192419 30314939344228402191288629)
                    ·
                      refine ⟨2842025563521412705433309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30314939344228402191288629 2842025563521412705433309)
                      ·
                        rfl

theorem cell23_5534825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_5534825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534825 prefixEnd_5534825 := by exact prefixLift 5534825
  have htrace : WordTrace (prefixWord ++ tailWord_5534825) baseStart_5534825 baseEnd_5534825 := by
    simpa [prefixWord, tailWord_5534825, baseEnd_5534825] using wordTrace_append hprefix tailTrace_5534825
  have hstable : (prefixWord ++ tailWord_5534825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534825).length < 2 ^ (prefixWord ++ tailWord_5534825).sum := by decide
  have hdescent : baseEnd_5534825 < baseStart_5534825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534828 : List Nat := [2, 2, 1, 1, 3, 2, 2, 10]
def baseStart_5534828 : Nat := 118140960795 + 5534828 * 2 ^ 59
def prefixEnd_5534828 : Nat := 4983230072969 + 3 ^ 40 * 5534828 * 2
def baseEnd_5534828 : Nat := 105260263109754673840585

theorem tailTrace_5534828 : CollatzResearch.WordTrace tailWord_5534828 prefixEnd_5534828 105260263109754673840585 := by
  unfold tailWord_5534828
  simp only [CollatzResearch.WordTrace]
  refine ⟨100935880796135452105226569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134581174394847269473635425 100935880796135452105226569)
  ·
    refine ⟨75701910597101589078919927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100935880796135452105226569 75701910597101589078919927)
    ·
      refine ⟨113552865895652383618379891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75701910597101589078919927 113552865895652383618379891)
      ·
        refine ⟨170329298843478575427569837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113552865895652383618379891 170329298843478575427569837)
        ·
          refine ⟨63873487066304465785338689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170329298843478575427569837 63873487066304465785338689)
          ·
            refine ⟨47905115299728349339004017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63873487066304465785338689 47905115299728349339004017)
            ·
              refine ⟨35928836474796262004253013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47905115299728349339004017 35928836474796262004253013)
              ·
                refine ⟨105260263109754673840585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35928836474796262004253013 105260263109754673840585)
                ·
                  rfl

theorem cell23_5534828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 10].length) (baseStart_5534828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534828 prefixEnd_5534828 := by exact prefixLift 5534828
  have htrace : WordTrace (prefixWord ++ tailWord_5534828) baseStart_5534828 baseEnd_5534828 := by
    simpa [prefixWord, tailWord_5534828, baseEnd_5534828] using wordTrace_append hprefix tailTrace_5534828
  have hstable : (prefixWord ++ tailWord_5534828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534828).length < 2 ^ (prefixWord ++ tailWord_5534828).sum := by decide
  have hdescent : baseEnd_5534828 < baseStart_5534828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534855 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_5534855 : Nat := 118140960795 + 5534855 * 2 ^ 59
def prefixEnd_5534855 : Nat := 4983230072969 + 3 ^ 40 * 5534855 * 2
def baseEnd_5534855 : Nat := 2842040967941047588058171

theorem tailTrace_5534855 : CollatzResearch.WordTrace tailWord_5534855 prefixEnd_5534855 2842040967941047588058171 := by
  unfold tailWord_5534855
  simp only [CollatzResearch.WordTrace]
  refine ⟨201872746363173087821686019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134581830908782058547790679 201872746363173087821686019)
  ·
    refine ⟨302809119544759631732529029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201872746363173087821686019 302809119544759631732529029)
    ·
      refine ⟨56776709914642430949849193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302809119544759631732529029 56776709914642430949849193)
      ·
        refine ⟨42582532435981823212386895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56776709914642430949849193 42582532435981823212386895)
        ·
          refine ⟨63873798653972734818580343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42582532435981823212386895 63873798653972734818580343)
          ·
            refine ⟨95810697980959102227870515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63873798653972734818580343 95810697980959102227870515)
            ·
              refine ⟨143716046971438653341805773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95810697980959102227870515 143716046971438653341805773)
              ·
                refine ⟨53893517614289495003177165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143716046971438653341805773 53893517614289495003177165)
                ·
                  refine ⟨20210069105358560626191437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53893517614289495003177165 20210069105358560626191437)
                  ·
                    refine ⟨7578775914509460234821789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20210069105358560626191437 7578775914509460234821789)
                    ·
                      refine ⟨2842040967941047588058171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7578775914509460234821789 2842040967941047588058171)
                      ·
                        rfl

theorem cell23_5534855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_5534855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534855 prefixEnd_5534855 := by exact prefixLift 5534855
  have htrace : WordTrace (prefixWord ++ tailWord_5534855) baseStart_5534855 baseEnd_5534855 := by
    simpa [prefixWord, tailWord_5534855, baseEnd_5534855] using wordTrace_append hprefix tailTrace_5534855
  have hstable : (prefixWord ++ tailWord_5534855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534855).length < 2 ^ (prefixWord ++ tailWord_5534855).sum := by decide
  have hdescent : baseEnd_5534855 < baseStart_5534855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534893 : List Nat := [1, 5, 2, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_5534893 : Nat := 118140960795 + 5534893 * 2 ^ 59
def prefixEnd_5534893 : Nat := 4983230072969 + 3 ^ 40 * 5534893 * 2
def baseEnd_5534893 : Nat := 2842060480205918439382997

theorem tailTrace_5534893 : CollatzResearch.WordTrace tailWord_5534893 prefixEnd_5534893 2842060480205918439382997 := by
  unfold tailWord_5534893
  simp only [CollatzResearch.WordTrace]
  refine ⟨201874132337035420311569333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134582754891356946874379555 201874132337035420311569333)
  ·
    refine ⟨18925699906597070654209625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201874132337035420311569333 18925699906597070654209625)
    ·
      refine ⟨14194274929947802990657219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18925699906597070654209625 14194274929947802990657219)
      ·
        refine ⟨21291412394921704485985829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14194274929947802990657219 21291412394921704485985829)
        ·
          refine ⟨3992139824047819591122343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21291412394921704485985829 3992139824047819591122343)
          ·
            refine ⟨5988209736071729386683515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3992139824047819591122343 5988209736071729386683515)
            ·
              refine ⟨8982314604107594080025273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5988209736071729386683515 8982314604107594080025273)
              ·
                refine ⟨6736735953080695560018955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8982314604107594080025273 6736735953080695560018955)
                ·
                  refine ⟨10105103929621043340028433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6736735953080695560018955 10105103929621043340028433)
                  ·
                    refine ⟨7578827947215782505021325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10105103929621043340028433 7578827947215782505021325)
                    ·
                      refine ⟨2842060480205918439382997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7578827947215782505021325 2842060480205918439382997)
                      ·
                        rfl

theorem cell23_5534893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_5534893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534893 prefixEnd_5534893 := by exact prefixLift 5534893
  have htrace : WordTrace (prefixWord ++ tailWord_5534893) baseStart_5534893 baseEnd_5534893 := by
    simpa [prefixWord, tailWord_5534893, baseEnd_5534893] using wordTrace_append hprefix tailTrace_5534893
  have hstable : (prefixWord ++ tailWord_5534893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534893).length < 2 ^ (prefixWord ++ tailWord_5534893).sum := by decide
  have hdescent : baseEnd_5534893 < baseStart_5534893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5534899 : List Nat := [1, 1, 1, 2, 3, 2, 5, 2, 1, 3, 2]
def baseStart_5534899 : Nat := 118140960795 + 5534899 * 2 ^ 59
def prefixEnd_5534899 : Nat := 4983230072969 + 3 ^ 40 * 5534899 * 2
def baseEnd_5534899 : Nat := 2842063561089845415907969

theorem tailTrace_5534899 : CollatzResearch.WordTrace tailWord_5534899 prefixEnd_5534899 2842063561089845415907969 := by
  unfold tailWord_5534899
  simp only [CollatzResearch.WordTrace]
  refine ⟨201874351175013683336287751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134582900783342455557525167 201874351175013683336287751)
  ·
    refine ⟨302811526762520525004431627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201874351175013683336287751 302811526762520525004431627)
    ·
      refine ⟨454217290143780787506647441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302811526762520525004431627 454217290143780787506647441)
      ·
        refine ⟨340662967607835590629985581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454217290143780787506647441 340662967607835590629985581)
        ·
          refine ⟨127748612852938346486244593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340662967607835590629985581 127748612852938346486244593)
          ·
            refine ⟨95811459639703759864683445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127748612852938346486244593 95811459639703759864683445)
            ·
              refine ⟨8982324341222227487314073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95811459639703759864683445 8982324341222227487314073)
              ·
                refine ⟨6736743255916670615485555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8982324341222227487314073 6736743255916670615485555)
                ·
                  refine ⟨10105114883875005923228333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6736743255916670615485555 10105114883875005923228333)
                  ·
                    refine ⟨3789418081453127221210625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10105114883875005923228333 3789418081453127221210625)
                    ·
                      refine ⟨2842063561089845415907969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3789418081453127221210625 2842063561089845415907969)
                      ·
                        rfl

theorem cell23_5534899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 3, 2].length) (baseStart_5534899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5534899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5534899 prefixEnd_5534899 := by exact prefixLift 5534899
  have htrace : WordTrace (prefixWord ++ tailWord_5534899) baseStart_5534899 baseEnd_5534899 := by
    simpa [prefixWord, tailWord_5534899, baseEnd_5534899] using wordTrace_append hprefix tailTrace_5534899
  have hstable : (prefixWord ++ tailWord_5534899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5534899).length < 2 ^ (prefixWord ++ tailWord_5534899).sum := by decide
  have hdescent : baseEnd_5534899 < baseStart_5534899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5534899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535002 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_5535002 : Nat := 118140960795 + 5535002 * 2 ^ 59
def prefixEnd_5535002 : Nat := 4983230072969 + 3 ^ 40 * 5535002 * 2
def baseEnd_5535002 : Nat := 2842116449597258512919995

theorem tailTrace_5535002 : CollatzResearch.WordTrace tailWord_5535002 prefixEnd_5535002 2842116449597258512919995 := by
  unfold tailWord_5535002
  simp only [CollatzResearch.WordTrace]
  refine ⟨50469526973410132981821815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134585405262427021284858173 50469526973410132981821815)
  ·
    refine ⟨75704290460115199472732723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50469526973410132981821815 75704290460115199472732723)
    ·
      refine ⟨113556435690172799209099085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75704290460115199472732723 113556435690172799209099085)
      ·
        refine ⟨42583663383814799703412157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113556435690172799209099085 42583663383814799703412157)
        ·
          refine ⟨15968873768930549888779559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42583663383814799703412157 15968873768930549888779559)
          ·
            refine ⟨23953310653395824833169339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15968873768930549888779559 23953310653395824833169339)
            ·
              refine ⟨35929965980093737249754009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23953310653395824833169339 35929965980093737249754009)
              ·
                refine ⟨26947474485070302937315507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35929965980093737249754009 26947474485070302937315507)
                ·
                  refine ⟨40421211727605454405973261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26947474485070302937315507 40421211727605454405973261)
                  ·
                    refine ⟨15157954397852045402239973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40421211727605454405973261 15157954397852045402239973)
                    ·
                      refine ⟨2842116449597258512919995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15157954397852045402239973 2842116449597258512919995)
                      ·
                        rfl

theorem cell23_5535002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_5535002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535002 prefixEnd_5535002 := by exact prefixLift 5535002
  have htrace : WordTrace (prefixWord ++ tailWord_5535002) baseStart_5535002 baseEnd_5535002 := by
    simpa [prefixWord, tailWord_5535002, baseEnd_5535002] using wordTrace_append hprefix tailTrace_5535002
  have hstable : (prefixWord ++ tailWord_5535002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535002).length < 2 ^ (prefixWord ++ tailWord_5535002).sum := by decide
  have hdescent : baseEnd_5535002 < baseStart_5535002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535039 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 3]
def baseStart_5535039 : Nat := 118140960795 + 5535039 * 2 ^ 59
def prefixEnd_5535039 : Nat := 4983230072969 + 3 ^ 40 * 5535039 * 2
def baseEnd_5535039 : Nat := 2842135448381474868157325

theorem tailTrace_5535039 : CollatzResearch.WordTrace tailWord_5535039 prefixEnd_5535039 2842135448381474868157325 := by
  unfold tailWord_5535039
  simp only [CollatzResearch.WordTrace]
  refine ⟨201879457394506487246384171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134586304929670991497589447 201879457394506487246384171)
  ·
    refine ⟨302819186091759730869576257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201879457394506487246384171 302819186091759730869576257)
    ·
      refine ⟨227114389568819798152182193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302819186091759730869576257 227114389568819798152182193)
      ·
        refine ⟨170335792176614848614136645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227114389568819798152182193 170335792176614848614136645)
        ·
          refine ⟨31937961033115284115150621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170335792176614848614136645 31937961033115284115150621)
          ·
            refine ⟨11976735387418231543181483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31937961033115284115150621 11976735387418231543181483)
            ·
              refine ⟨17965103081127347314772225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11976735387418231543181483 17965103081127347314772225)
              ·
                refine ⟨13473827310845510486079169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17965103081127347314772225 13473827310845510486079169)
                ·
                  refine ⟨10105370483134132864559377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13473827310845510486079169 10105370483134132864559377)
                  ·
                    refine ⟨7579027862350599648419533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10105370483134132864559377 7579027862350599648419533)
                    ·
                      refine ⟨2842135448381474868157325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7579027862350599648419533 2842135448381474868157325)
                      ·
                        rfl

theorem cell23_5535039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_5535039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535039 prefixEnd_5535039 := by exact prefixLift 5535039
  have htrace : WordTrace (prefixWord ++ tailWord_5535039) baseStart_5535039 baseEnd_5535039 := by
    simpa [prefixWord, tailWord_5535039, baseEnd_5535039] using wordTrace_append hprefix tailTrace_5535039
  have hstable : (prefixWord ++ tailWord_5535039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535039).length < 2 ^ (prefixWord ++ tailWord_5535039).sum := by decide
  have hdescent : baseEnd_5535039 < baseStart_5535039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535045 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_5535045 : Nat := 118140960795 + 5535045 * 2 ^ 59
def prefixEnd_5535045 : Nat := 4983230072969 + 3 ^ 40 * 5535045 * 2
def baseEnd_5535045 : Nat := 2842138529265401844682297

theorem tailTrace_5535045 : CollatzResearch.WordTrace tailWord_5535045 prefixEnd_5535045 2842138529265401844682297 := by
  unfold tailWord_5535045
  simp only [CollatzResearch.WordTrace]
  refine ⟨201879676232484750271102589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134586450821656500180735059 201879676232484750271102589)
  ·
    refine ⟨75704878587181781351663471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201879676232484750271102589 75704878587181781351663471)
    ·
      refine ⟨113557317880772672027495207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75704878587181781351663471 113557317880772672027495207)
      ·
        refine ⟨170335976821159008041242811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113557317880772672027495207 170335976821159008041242811)
        ·
          refine ⟨255503965231738512061864217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170335976821159008041242811 255503965231738512061864217)
          ·
            refine ⟨191627973923803884046398163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255503965231738512061864217 191627973923803884046398163)
            ·
              refine ⟨287441960885705826069597245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191627973923803884046398163 287441960885705826069597245)
              ·
                refine ⟨107790735332139684776098967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287441960885705826069597245 107790735332139684776098967)
                ·
                  refine ⟨161686102998209527164148451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107790735332139684776098967 161686102998209527164148451)
                  ·
                    refine ⟨242529154497314290746222677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161686102998209527164148451 242529154497314290746222677)
                    ·
                      refine ⟨2842138529265401844682297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 242529154497314290746222677 2842138529265401844682297)
                      ·
                        rfl

theorem cell23_5535045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_5535045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535045 prefixEnd_5535045 := by exact prefixLift 5535045
  have htrace : WordTrace (prefixWord ++ tailWord_5535045) baseStart_5535045 baseEnd_5535045 := by
    simpa [prefixWord, tailWord_5535045, baseEnd_5535045] using wordTrace_append hprefix tailTrace_5535045
  have hstable : (prefixWord ++ tailWord_5535045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535045).length < 2 ^ (prefixWord ++ tailWord_5535045).sum := by decide
  have hdescent : baseEnd_5535045 < baseStart_5535045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535106 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_5535106 : Nat := 118140960795 + 5535106 * 2 ^ 59
def prefixEnd_5535106 : Nat := 4983230072969 + 3 ^ 40 * 5535106 * 2
def baseEnd_5535106 : Nat := 947389950528442035339839

theorem tailTrace_5535106 : CollatzResearch.WordTrace tailWord_5535106 prefixEnd_5535106 947389950528442035339839 := by
  unfold tailWord_5535106
  simp only [CollatzResearch.WordTrace]
  refine ⟨50470475271315939422268293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134587934056842505126048781 50470475271315939422268293)
  ·
    refine ⟨9463214113371738641675305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50470475271315939422268293 9463214113371738641675305)
    ·
      refine ⟨7097410585028803981256479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9463214113371738641675305 7097410585028803981256479)
      ·
        refine ⟨10646115877543205971884719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7097410585028803981256479 10646115877543205971884719)
        ·
          refine ⟨15969173816314808957827079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10646115877543205971884719 15969173816314808957827079)
          ·
            refine ⟨23953760724472213436740619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15969173816314808957827079 23953760724472213436740619)
            ·
              refine ⟨35930641086708320155110929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23953760724472213436740619 35930641086708320155110929)
              ·
                refine ⟨26947980815031240116333197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35930641086708320155110929 26947980815031240116333197)
                ·
                  refine ⟨10105492805636715043624949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26947980815031240116333197 10105492805636715043624949)
                  ·
                    refine ⟨947389950528442035339839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10105492805636715043624949 947389950528442035339839)
                    ·
                      rfl

theorem cell23_5535106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_5535106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535106 prefixEnd_5535106 := by exact prefixLift 5535106
  have htrace : WordTrace (prefixWord ++ tailWord_5535106) baseStart_5535106 baseEnd_5535106 := by
    simpa [prefixWord, tailWord_5535106, baseEnd_5535106] using wordTrace_append hprefix tailTrace_5535106
  have hstable : (prefixWord ++ tailWord_5535106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535106).length < 2 ^ (prefixWord ++ tailWord_5535106).sum := by decide
  have hdescent : baseEnd_5535106 < baseStart_5535106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535129 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 3, 2, 3]
def baseStart_5535129 : Nat := 118140960795 + 5535129 * 2 ^ 59
def prefixEnd_5535129 : Nat := 4983230072969 + 3 ^ 40 * 5535129 * 2
def baseEnd_5535129 : Nat := 2842181661640379516031911

theorem tailTrace_5535129 : CollatzResearch.WordTrace tailWord_5535129 prefixEnd_5535129 2842181661640379516031911 := by
  unfold tailWord_5535129
  simp only [CollatzResearch.WordTrace]
  refine ⟨201882739964180432617160441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134588493309453621744773627 201882739964180432617160441)
  ·
    refine ⟨151412054973135324462870331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201882739964180432617160441 151412054973135324462870331)
    ·
      refine ⟨227118082459702986694305497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151412054973135324462870331 227118082459702986694305497)
      ·
        refine ⟨170338561844777240020729123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227118082459702986694305497 170338561844777240020729123)
        ·
          refine ⟨255507842767165860031093685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170338561844777240020729123 255507842767165860031093685)
          ·
            refine ⟨23953860259421799377915033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 255507842767165860031093685 23953860259421799377915033)
            ·
              refine ⟨17965395194566349533436275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23953860259421799377915033 17965395194566349533436275)
              ·
                refine ⟨26948092791849524300154413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17965395194566349533436275 26948092791849524300154413)
                ·
                  refine ⟨10105534796943571612557905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26948092791849524300154413 10105534796943571612557905)
                  ·
                    refine ⟨7579151097707678709418429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10105534796943571612557905 7579151097707678709418429)
                    ·
                      refine ⟨2842181661640379516031911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7579151097707678709418429 2842181661640379516031911)
                      ·
                        rfl

theorem cell23_5535129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_5535129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535129 prefixEnd_5535129 := by exact prefixLift 5535129
  have htrace : WordTrace (prefixWord ++ tailWord_5535129) baseStart_5535129 baseEnd_5535129 := by
    simpa [prefixWord, tailWord_5535129, baseEnd_5535129] using wordTrace_append hprefix tailTrace_5535129
  have hstable : (prefixWord ++ tailWord_5535129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535129).length < 2 ^ (prefixWord ++ tailWord_5535129).sum := by decide
  have hdescent : baseEnd_5535129 < baseStart_5535129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535149 : List Nat := [1, 5, 2, 2, 1, 2, 10]
def baseStart_5535149 : Nat := 118140960795 + 5535149 * 2 ^ 59
def prefixEnd_5535149 : Nat := 4983230072969 + 3 ^ 40 * 5535149 * 2
def baseEnd_5535149 : Nat := 35088789274734190589899

theorem tailTrace_5535149 : CollatzResearch.WordTrace tailWord_5535149 prefixEnd_5535149 35088789274734190589899 := by
  unfold tailWord_5535149
  simp only [CollatzResearch.WordTrace]
  refine ⟨201883469424107976032888501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134588979616071984021925667 201883469424107976032888501)
  ·
    refine ⟨18926575258510122753083297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201883469424107976032888501 18926575258510122753083297)
    ·
      refine ⟨14194931443882592064812473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18926575258510122753083297 14194931443882592064812473)
      ·
        refine ⟨10646198582911944048609355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14194931443882592064812473 10646198582911944048609355)
        ·
          refine ⟨15969297874367916072914033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10646198582911944048609355 15969297874367916072914033)
          ·
            refine ⟨11976973405775937054685525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15969297874367916072914033 11976973405775937054685525)
            ·
              refine ⟨35088789274734190589899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11976973405775937054685525 35088789274734190589899)
              ·
                rfl

theorem cell23_5535149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 10].length) (baseStart_5535149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535149 prefixEnd_5535149 := by exact prefixLift 5535149
  have htrace : WordTrace (prefixWord ++ tailWord_5535149) baseStart_5535149 baseEnd_5535149 := by
    simpa [prefixWord, tailWord_5535149, baseEnd_5535149] using wordTrace_append hprefix tailTrace_5535149
  have hstable : (prefixWord ++ tailWord_5535149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535149).length < 2 ^ (prefixWord ++ tailWord_5535149).sum := by decide
  have hdescent : baseEnd_5535149 < baseStart_5535149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535192 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 1, 8]
def baseStart_5535192 : Nat := 118140960795 + 5535192 * 2 ^ 59
def prefixEnd_5535192 : Nat := 4983230072969 + 3 ^ 40 * 5535192 * 2
def baseEnd_5535192 : Nat := 947404670307204256514707

theorem tailTrace_5535192 : CollatzResearch.WordTrace tailWord_5535192 prefixEnd_5535192 947404670307204256514707 := by
  unfold tailWord_5535192
  simp only [CollatzResearch.WordTrace]
  refine ⟨100942518881476097188351915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134590025175301462917802553 100942518881476097188351915)
  ·
    refine ⟨151413778322214145782527873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100942518881476097188351915 151413778322214145782527873)
    ·
      refine ⟨113560333741660609336895905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151413778322214145782527873 113560333741660609336895905)
      ·
        refine ⟨85170250306245457002671929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113560333741660609336895905 85170250306245457002671929)
        ·
          refine ⟨63877687729684092752003947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85170250306245457002671929 63877687729684092752003947)
          ·
            refine ⟨95816531594526139128005921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63877687729684092752003947 95816531594526139128005921)
            ·
              refine ⟨71862398695894604346004441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95816531594526139128005921 71862398695894604346004441)
              ·
                refine ⟨53896799021920953259503331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71862398695894604346004441 53896799021920953259503331)
                ·
                  refine ⟨80845198532881429889254997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53896799021920953259503331 80845198532881429889254997)
                  ·
                    refine ⟨947404670307204256514707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80845198532881429889254997 947404670307204256514707)
                    ·
                      rfl

theorem cell23_5535192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_5535192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535192 prefixEnd_5535192 := by exact prefixLift 5535192
  have htrace : WordTrace (prefixWord ++ tailWord_5535192) baseStart_5535192 baseEnd_5535192 := by
    simpa [prefixWord, tailWord_5535192, baseEnd_5535192] using wordTrace_append hprefix tailTrace_5535192
  have hstable : (prefixWord ++ tailWord_5535192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535192).length < 2 ^ (prefixWord ++ tailWord_5535192).sum := by decide
  have hdescent : baseEnd_5535192 < baseStart_5535192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535203 : List Nat := [1, 1, 1, 6, 2, 1, 2, 3, 1, 3, 2]
def baseStart_5535203 : Nat := 118140960795 + 5535203 * 2 ^ 59
def prefixEnd_5535203 : Nat := 4983230072969 + 3 ^ 40 * 5535203 * 2
def baseEnd_5535203 : Nat := 2842219659208812226506571

theorem tailTrace_5535203 : CollatzResearch.WordTrace tailWord_5535203 prefixEnd_5535203 2842219659208812226506571 := by
  unfold tailWord_5535203
  simp only [CollatzResearch.WordTrace]
  refine ⟨201885438965912343255354263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134590292643941562170236175 201885438965912343255354263)
  ·
    refine ⟨302828158448868514883031395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201885438965912343255354263 302828158448868514883031395)
    ·
      refine ⟨454242237673302772324547093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302828158448868514883031395 454242237673302772324547093)
      ·
        refine ⟨21292604890936067452713145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 454242237673302772324547093 21292604890936067452713145)
        ·
          refine ⟨15969453668202050589534859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21292604890936067452713145 15969453668202050589534859)
          ·
            refine ⟨23954180502303075884302289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15969453668202050589534859 23954180502303075884302289)
            ·
              refine ⟨17965635376727306913226717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23954180502303075884302289 17965635376727306913226717)
              ·
                refine ⟨6737113266272740092460019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17965635376727306913226717 6737113266272740092460019)
                ·
                  refine ⟨10105669899409110138690029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6737113266272740092460019 10105669899409110138690029)
                  ·
                    refine ⟨3789626212278416302008761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10105669899409110138690029 3789626212278416302008761)
                    ·
                      refine ⟨2842219659208812226506571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3789626212278416302008761 2842219659208812226506571)
                      ·
                        rfl

theorem cell23_5535203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_5535203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535203 prefixEnd_5535203 := by exact prefixLift 5535203
  have htrace : WordTrace (prefixWord ++ tailWord_5535203) baseStart_5535203 baseEnd_5535203 := by
    simpa [prefixWord, tailWord_5535203, baseEnd_5535203] using wordTrace_append hprefix tailTrace_5535203
  have hstable : (prefixWord ++ tailWord_5535203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535203).length < 2 ^ (prefixWord ++ tailWord_5535203).sum := by decide
  have hdescent : baseEnd_5535203 < baseStart_5535203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535212 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_5535212 : Nat := 118140960795 + 5535212 * 2 ^ 59
def prefixEnd_5535212 : Nat := 4983230072969 + 3 ^ 40 * 5535212 * 2
def baseEnd_5535212 : Nat := 2842224280534702691294029

theorem tailTrace_5535212 : CollatzResearch.WordTrace tailWord_5535212 prefixEnd_5535212 2842224280534702691294029 := by
  unfold tailWord_5535212
  simp only [CollatzResearch.WordTrace]
  refine ⟨100942883611439868896215945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134590511481919825194954593 100942883611439868896215945)
  ·
    refine ⟨75707162708579901672161959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100942883611439868896215945 75707162708579901672161959)
    ·
      refine ⟨113560744062869852508242939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75707162708579901672161959 113560744062869852508242939)
      ·
        refine ⟨170341116094304778762364409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113560744062869852508242939 170341116094304778762364409)
        ·
          refine ⟨127755837070728584071773307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170341116094304778762364409 127755837070728584071773307)
          ·
            refine ⟨191633755606092876107659961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127755837070728584071773307 191633755606092876107659961)
            ·
              refine ⟨143725316704569657080744971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191633755606092876107659961 143725316704569657080744971)
              ·
                refine ⟨215587975056854485621117457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143725316704569657080744971 215587975056854485621117457)
                ·
                  refine ⟨161690981292640864215838093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215587975056854485621117457 161690981292640864215838093)
                  ·
                    refine ⟨60634117984740324080939285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161690981292640864215838093 60634117984740324080939285)
                    ·
                      refine ⟨2842224280534702691294029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60634117984740324080939285 2842224280534702691294029)
                      ·
                        rfl

theorem cell23_5535212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_5535212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535212 prefixEnd_5535212 := by exact prefixLift 5535212
  have htrace : WordTrace (prefixWord ++ tailWord_5535212) baseStart_5535212 baseEnd_5535212 := by
    simpa [prefixWord, tailWord_5535212, baseEnd_5535212] using wordTrace_append hprefix tailTrace_5535212
  have hstable : (prefixWord ++ tailWord_5535212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535212).length < 2 ^ (prefixWord ++ tailWord_5535212).sum := by decide
  have hdescent : baseEnd_5535212 < baseStart_5535212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535303 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 2, 5]
def baseStart_5535303 : Nat := 118140960795 + 5535303 * 2 ^ 59
def prefixEnd_5535303 : Nat := 4983230072969 + 3 ^ 40 * 5535303 * 2
def baseEnd_5535303 : Nat := 947423669091420611752037

theorem tailTrace_5535303 : CollatzResearch.WordTrace tailWord_5535303 prefixEnd_5535303 947423669091420611752037 := by
  unfold tailWord_5535303
  simp only [CollatzResearch.WordTrace]
  refine ⟨201889086265550060333994563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134592724177033373555996375 201889086265550060333994563)
  ·
    refine ⟨302833629398325090500991845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201889086265550060333994563 302833629398325090500991845)
    ·
      refine ⟨56781305512185954468935971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302833629398325090500991845 56781305512185954468935971)
      ·
        refine ⟨85171958268278931703403957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56781305512185954468935971 85171958268278931703403957)
        ·
          refine ⟨7984871087651149847194121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85171958268278931703403957 7984871087651149847194121)
          ·
            refine ⟨5988653315738362385395591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7984871087651149847194121 5988653315738362385395591)
            ·
              refine ⟨8982979973607543578093387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5988653315738362385395591 8982979973607543578093387)
              ·
                refine ⟨13474469960411315367140081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8982979973607543578093387 13474469960411315367140081)
                ·
                  refine ⟨10105852470308486525355061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13474469960411315367140081 10105852470308486525355061)
                  ·
                    refine ⟨947423669091420611752037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10105852470308486525355061 947423669091420611752037)
                    ·
                      rfl

theorem cell23_5535303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_5535303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535303 prefixEnd_5535303 := by exact prefixLift 5535303
  have htrace : WordTrace (prefixWord ++ tailWord_5535303) baseStart_5535303 baseEnd_5535303 := by
    simpa [prefixWord, tailWord_5535303, baseEnd_5535303] using wordTrace_append hprefix tailTrace_5535303
  have hstable : (prefixWord ++ tailWord_5535303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535303).length < 2 ^ (prefixWord ++ tailWord_5535303).sum := by decide
  have hdescent : baseEnd_5535303 < baseStart_5535303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535306 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 1, 6, 2]
def baseStart_5535306 : Nat := 118140960795 + 5535306 * 2 ^ 59
def prefixEnd_5535306 : Nat := 4983230072969 + 3 ^ 40 * 5535306 * 2
def baseEnd_5535306 : Nat := 2842272547716225323518597

theorem tailTrace_5535306 : CollatzResearch.WordTrace tailWord_5535306 prefixEnd_5535306 2842272547716225323518597 := by
  unfold tailWord_5535306
  simp only [CollatzResearch.WordTrace]
  refine ⟨50472298921134797961588443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134592797123026127897569181 50472298921134797961588443)
  ·
    refine ⟨75708448381702196942382665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50472298921134797961588443 75708448381702196942382665)
    ·
      refine ⟨56781336286276647706786999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75708448381702196942382665 56781336286276647706786999)
      ·
        refine ⟨85172004429414971560180499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56781336286276647706786999 85172004429414971560180499)
        ·
          refine ⟨127758006644122457340270749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85172004429414971560180499 127758006644122457340270749)
          ·
            refine ⟨47909252491545921502601531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127758006644122457340270749 47909252491545921502601531)
            ·
              refine ⟨71863878737318882253902297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47909252491545921502601531 71863878737318882253902297)
              ·
                refine ⟨53897909052989161690426723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71863878737318882253902297 53897909052989161690426723)
                ·
                  refine ⟨80846863579483742535640085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53897909052989161690426723 80846863579483742535640085)
                  ·
                    refine ⟨3789696730288300431358129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80846863579483742535640085 3789696730288300431358129)
                    ·
                      refine ⟨2842272547716225323518597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3789696730288300431358129 2842272547716225323518597)
                      ·
                        rfl

theorem cell23_5535306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_5535306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535306 prefixEnd_5535306 := by exact prefixLift 5535306
  have htrace : WordTrace (prefixWord ++ tailWord_5535306) baseStart_5535306 baseEnd_5535306 := by
    simpa [prefixWord, tailWord_5535306, baseEnd_5535306] using wordTrace_append hprefix tailTrace_5535306
  have hstable : (prefixWord ++ tailWord_5535306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535306).length < 2 ^ (prefixWord ++ tailWord_5535306).sum := by decide
  have hdescent : baseEnd_5535306 < baseStart_5535306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535316 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_5535316 : Nat := 118140960795 + 5535316 * 2 ^ 59
def prefixEnd_5535316 : Nat := 4983230072969 + 3 ^ 40 * 5535316 * 2
def baseEnd_5535316 : Nat := 947425894174256761464517

theorem tailTrace_5535316 : CollatzResearch.WordTrace tailWord_5535316 prefixEnd_5535316 947425894174256761464517 := by
  unfold tailWord_5535316
  simp only [CollatzResearch.WordTrace]
  refine ⟨100944780207251481777108901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134593040276335309036145201 100944780207251481777108901)
  ·
    refine ⟨18927146288859652833207919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100944780207251481777108901 18927146288859652833207919)
    ·
      refine ⟨28390719433289479249811879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18927146288859652833207919 28390719433289479249811879)
      ·
        refine ⟨42586079149934218874717819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28390719433289479249811879 42586079149934218874717819)
        ·
          refine ⟨63879118724901328312076729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42586079149934218874717819 63879118724901328312076729)
          ·
            refine ⟨47909339043675996234057547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63879118724901328312076729 47909339043675996234057547)
            ·
              refine ⟨71864008565513994351086321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47909339043675996234057547 71864008565513994351086321)
              ·
                refine ⟨53898006424135495763314741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71864008565513994351086321 53898006424135495763314741)
                ·
                  refine ⟨5052938102262702727810757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53898006424135495763314741 5052938102262702727810757)
                  ·
                    refine ⟨947425894174256761464517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5052938102262702727810757 947425894174256761464517)
                    ·
                      rfl

theorem cell23_5535316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_5535316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535316 prefixEnd_5535316 := by exact prefixLift 5535316
  have htrace : WordTrace (prefixWord ++ tailWord_5535316) baseStart_5535316 baseEnd_5535316 := by
    simpa [prefixWord, tailWord_5535316, baseEnd_5535316] using wordTrace_append hprefix tailTrace_5535316
  have hstable : (prefixWord ++ tailWord_5535316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535316).length < 2 ^ (prefixWord ++ tailWord_5535316).sum := by decide
  have hdescent : baseEnd_5535316 < baseStart_5535316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535318 : List Nat := [5, 2, 2, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_5535318 : Nat := 118140960795 + 5535318 * 2 ^ 59
def prefixEnd_5535318 : Nat := 4983230072969 + 3 ^ 40 * 5535318 * 2
def baseEnd_5535318 : Nat := 2842278709484079276568543

theorem tailTrace_5535318 : CollatzResearch.WordTrace tailWord_5535318 prefixEnd_5535318 2842278709484079276568543 := by
  unfold tailWord_5535318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12618102085030982368486913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134593088906997145263860405 12618102085030982368486913)
  ·
    refine ⟨9463576563773236776365185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12618102085030982368486913 9463576563773236776365185)
    ·
      refine ⟨7097682422829927582273889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9463576563773236776365185 7097682422829927582273889)
      ·
        refine ⟨5323261817122445686705417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7097682422829927582273889 5323261817122445686705417)
        ·
          refine ⟨3992446362841834265029063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5323261817122445686705417 3992446362841834265029063)
          ·
            refine ⟨5988669544262751397543595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3992446362841834265029063 5988669544262751397543595)
            ·
              refine ⟨8983004316394127096315393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5988669544262751397543595 8983004316394127096315393)
              ·
                refine ⟨6737253237295595322236545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8983004316394127096315393 6737253237295595322236545)
                ·
                  refine ⟨5052939927971696491677409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6737253237295595322236545 5052939927971696491677409)
                  ·
                    refine ⟨3789704945978772368758057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5052939927971696491677409 3789704945978772368758057)
                    ·
                      refine ⟨2842278709484079276568543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3789704945978772368758057 2842278709484079276568543)
                      ·
                        rfl

theorem cell23_5535318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_5535318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535318 prefixEnd_5535318 := by exact prefixLift 5535318
  have htrace : WordTrace (prefixWord ++ tailWord_5535318) baseStart_5535318 baseEnd_5535318 := by
    simpa [prefixWord, tailWord_5535318, baseEnd_5535318] using wordTrace_append hprefix tailTrace_5535318
  have hstable : (prefixWord ++ tailWord_5535318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535318).length < 2 ^ (prefixWord ++ tailWord_5535318).sum := by decide
  have hdescent : baseEnd_5535318 < baseStart_5535318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535319 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_5535319 : Nat := 118140960795 + 5535319 * 2 ^ 59
def prefixEnd_5535319 : Nat := 4983230072969 + 3 ^ 40 * 5535319 * 2
def baseEnd_5535319 : Nat := 2842279222964733772656037

theorem tailTrace_5535319 : CollatzResearch.WordTrace tailWord_5535319 prefixEnd_5535319 2842279222964733772656037 := by
  unfold tailWord_5535319
  simp only [CollatzResearch.WordTrace]
  refine ⟨201889669833492095066577011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134593113222328063377718007 201889669833492095066577011)
  ·
    refine ⟨302834504750238142599865517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201889669833492095066577011 302834504750238142599865517)
    ·
      refine ⟨113562939281339303474949569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302834504750238142599865517 113562939281339303474949569)
      ·
        refine ⟨85172204461004477606212177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113562939281339303474949569 85172204461004477606212177)
        ·
          refine ⟨63879153345753358204659133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85172204461004477606212177 63879153345753358204659133)
          ·
            refine ⟨23954682504657509326747175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63879153345753358204659133 23954682504657509326747175)
            ·
              refine ⟨35932023756986263990120763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23954682504657509326747175 35932023756986263990120763)
              ·
                refine ⟨53898035635479395985181145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35932023756986263990120763 53898035635479395985181145)
                ·
                  refine ⟨40423526726609546988885859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53898035635479395985181145 40423526726609546988885859)
                  ·
                    refine ⟨60635290089914320483328789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40423526726609546988885859 60635290089914320483328789)
                    ·
                      refine ⟨2842279222964733772656037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60635290089914320483328789 2842279222964733772656037)
                      ·
                        rfl

theorem cell23_5535319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_5535319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535319 prefixEnd_5535319 := by exact prefixLift 5535319
  have htrace : WordTrace (prefixWord ++ tailWord_5535319) baseStart_5535319 baseEnd_5535319 := by
    simpa [prefixWord, tailWord_5535319, baseEnd_5535319] using wordTrace_append hprefix tailTrace_5535319
  have hstable : (prefixWord ++ tailWord_5535319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535319).length < 2 ^ (prefixWord ++ tailWord_5535319).sum := by decide
  have hdescent : baseEnd_5535319 < baseStart_5535319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535329 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 8]
def baseStart_5535329 : Nat := 118140960795 + 5535329 * 2 ^ 59
def prefixEnd_5535329 : Nat := 4983230072969 + 3 ^ 40 * 5535329 * 2
def baseEnd_5535329 : Nat := 315809373085697637058999

theorem tailTrace_5535329 : CollatzResearch.WordTrace tailWord_5535329 prefixEnd_5535329 315809373085697637058999 := by
  unfold tailWord_5535329
  simp only [CollatzResearch.WordTrace]
  refine ⟨201890034563455866774441041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134593356375637244516294027 201890034563455866774441041)
  ·
    refine ⟨151417525922591900080830781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201890034563455866774441041 151417525922591900080830781)
    ·
      refine ⟨56781572220971962530311543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151417525922591900080830781 56781572220971962530311543)
      ·
        refine ⟨85172358331457943795467315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56781572220971962530311543 85172358331457943795467315)
        ·
          refine ⟨127758537497186915693200973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85172358331457943795467315 127758537497186915693200973)
          ·
            refine ⟨47909451561445093384950365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127758537497186915693200973 47909451561445093384950365)
            ·
              refine ⟨17966044335541910019356387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47909451561445093384950365 17966044335541910019356387)
              ·
                refine ⟨26949066503312865029034581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17966044335541910019356387 26949066503312865029034581)
                ·
                  refine ⟨315809373085697637058999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26949066503312865029034581 315809373085697637058999)
                  ·
                    rfl

theorem cell23_5535329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 8].length) (baseStart_5535329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535329 prefixEnd_5535329 := by exact prefixLift 5535329
  have htrace : WordTrace (prefixWord ++ tailWord_5535329) baseStart_5535329 baseEnd_5535329 := by
    simpa [prefixWord, tailWord_5535329, baseEnd_5535329] using wordTrace_append hprefix tailTrace_5535329
  have hstable : (prefixWord ++ tailWord_5535329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535329).length < 2 ^ (prefixWord ++ tailWord_5535329).sum := by decide
  have hdescent : baseEnd_5535329 < baseStart_5535329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535333 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 3, 4]
def baseStart_5535333 : Nat := 118140960795 + 5535333 * 2 ^ 59
def prefixEnd_5535333 : Nat := 4983230072969 + 3 ^ 40 * 5535333 * 2
def baseEnd_5535333 : Nat := 947428803897965572626991

theorem tailTrace_5535333 : CollatzResearch.WordTrace tailWord_5535333 prefixEnd_5535333 947428803897965572626991 := by
  unfold tailWord_5535333
  simp only [CollatzResearch.WordTrace]
  refine ⟨201890180455441375457586653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134593453636960916971724435 201890180455441375457586653)
  ·
    refine ⟨75708817670790515796594995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201890180455441375457586653 75708817670790515796594995)
    ·
      refine ⟨113563226506185773694892493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75708817670790515796594995 113563226506185773694892493)
      ·
        refine ⟨42586209939819665135584685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113563226506185773694892493 42586209939819665135584685)
        ·
          refine ⟨15969828727432374425844257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42586209939819665135584685 15969828727432374425844257)
          ·
            refine ⟨11977371545574280819383193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15969828727432374425844257 11977371545574280819383193)
            ·
              refine ⟨8983028659180710614537395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11977371545574280819383193 8983028659180710614537395)
              ·
                refine ⟨13474542988771065921806093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8983028659180710614537395 13474542988771065921806093)
                ·
                  refine ⟨5052953620789149720677285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13474542988771065921806093 5052953620789149720677285)
                  ·
                    refine ⟨947428803897965572626991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5052953620789149720677285 947428803897965572626991)
                    ·
                      rfl

theorem cell23_5535333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_5535333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535333 prefixEnd_5535333 := by exact prefixLift 5535333
  have htrace : WordTrace (prefixWord ++ tailWord_5535333) baseStart_5535333 baseEnd_5535333 := by
    simpa [prefixWord, tailWord_5535333, baseEnd_5535333] using wordTrace_append hprefix tailTrace_5535333
  have hstable : (prefixWord ++ tailWord_5535333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535333).length < 2 ^ (prefixWord ++ tailWord_5535333).sum := by decide
  have hdescent : baseEnd_5535333 < baseStart_5535333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535359 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 7, 5]
def baseStart_5535359 : Nat := 118140960795 + 5535359 * 2 ^ 59
def prefixEnd_5535359 : Nat := 4983230072969 + 3 ^ 40 * 5535359 * 2
def baseEnd_5535359 : Nat := 947433254063637872051951

theorem tailTrace_5535359 : CollatzResearch.WordTrace tailWord_5535359 prefixEnd_5535359 947433254063637872051951 := by
  unfold tailWord_5535359
  simp only [CollatzResearch.WordTrace]
  refine ⟨201891128753347181898033131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134594085835564787932022087 201891128753347181898033131)
  ·
    refine ⟨302836693130020772847049697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201891128753347181898033131 302836693130020772847049697)
    ·
      refine ⟨227127519847515579635287273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302836693130020772847049697 227127519847515579635287273)
      ·
        refine ⟨170345639885636684726465455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227127519847515579635287273 170345639885636684726465455)
        ·
          refine ⟨255518459828455027089698183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170345639885636684726465455 255518459828455027089698183)
          ·
            refine ⟨383277689742682540634547275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255518459828455027089698183 383277689742682540634547275)
            ·
              refine ⟨574916534614023810951820913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383277689742682540634547275 574916534614023810951820913)
              ·
                refine ⟨431187400960517858213865685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574916534614023810951820913 431187400960517858213865685)
                ·
                  refine ⟨10105954710012137301887477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 431187400960517858213865685 10105954710012137301887477)
                  ·
                    refine ⟨947433254063637872051951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10105954710012137301887477 947433254063637872051951)
                    ·
                      rfl

theorem cell23_5535359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 5].length) (baseStart_5535359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535359 prefixEnd_5535359 := by exact prefixLift 5535359
  have htrace : WordTrace (prefixWord ++ tailWord_5535359) baseStart_5535359 baseEnd_5535359 := by
    simpa [prefixWord, tailWord_5535359, baseEnd_5535359] using wordTrace_append hprefix tailTrace_5535359
  have hstable : (prefixWord ++ tailWord_5535359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535359).length < 2 ^ (prefixWord ++ tailWord_5535359).sum := by decide
  have hdescent : baseEnd_5535359 < baseStart_5535359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535383 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 4, 3, 2]
def baseStart_5535383 : Nat := 118140960795 + 5535383 * 2 ^ 59
def prefixEnd_5535383 : Nat := 4983230072969 + 3 ^ 40 * 5535383 * 2
def baseEnd_5535383 : Nat := 2842312085726621522255743

theorem tailTrace_5535383 : CollatzResearch.WordTrace tailWord_5535383 prefixEnd_5535383 2842312085726621522255743 := by
  unfold tailWord_5535383
  simp only [CollatzResearch.WordTrace]
  refine ⟨201892004105260233996906803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134594669403506822664604535 201892004105260233996906803)
  ·
    refine ⟨302838006157890350995360205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201892004105260233996906803 302838006157890350995360205)
    ·
      refine ⟨113564252309208881623260077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302838006157890350995360205 113564252309208881623260077)
      ·
        refine ⟨42586594615953330608722529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113564252309208881623260077 42586594615953330608722529)
        ·
          refine ⟨31939945961964997956541897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42586594615953330608722529 31939945961964997956541897)
          ·
            refine ⟨23954959471473748467406423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31939945961964997956541897 23954959471473748467406423)
            ·
              refine ⟨35932439207210622701109635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23954959471473748467406423 35932439207210622701109635)
              ·
                refine ⟨53898658810815934051664453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35932439207210622701109635 53898658810815934051664453)
                ·
                  refine ⟨10105998527027987634687085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53898658810815934051664453 10105998527027987634687085)
                  ·
                    refine ⟨3789749447635495363007657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10105998527027987634687085 3789749447635495363007657)
                    ·
                      refine ⟨2842312085726621522255743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3789749447635495363007657 2842312085726621522255743)
                      ·
                        rfl

theorem cell23_5535383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_5535383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535383 prefixEnd_5535383 := by exact prefixLift 5535383
  have htrace : WordTrace (prefixWord ++ tailWord_5535383) baseStart_5535383 baseEnd_5535383 := by
    simpa [prefixWord, tailWord_5535383, baseEnd_5535383] using wordTrace_append hprefix tailTrace_5535383
  have hstable : (prefixWord ++ tailWord_5535383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535383).length < 2 ^ (prefixWord ++ tailWord_5535383).sum := by decide
  have hdescent : baseEnd_5535383 < baseStart_5535383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535436 : List Nat := [2, 2, 1, 5, 2, 11]
def baseStart_5535436 : Nat := 118140960795 + 5535436 * 2 ^ 59
def prefixEnd_5535436 : Nat := 4983230072969 + 3 ^ 40 * 5535436 * 2
def baseEnd_5535436 : Nat := 11696869548153538332893

theorem tailTrace_5535436 : CollatzResearch.WordTrace tailWord_5535436 prefixEnd_5535436 11696869548153538332893 := by
  unfold tailWord_5535436
  simp only [CollatzResearch.WordTrace]
  refine ⟨100946968587034112024293081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134595958116045482699057441 100946968587034112024293081)
  ·
    refine ⟨75710226440275584018219811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100946968587034112024293081 75710226440275584018219811)
    ·
      refine ⟨113565339660413376027329717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75710226440275584018219811 113565339660413376027329717)
      ·
        refine ⟨10646750593163754002562161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113565339660413376027329717 10646750593163754002562161)
        ·
          refine ⟨7985062944872815501921621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10646750593163754002562161 7985062944872815501921621)
          ·
            refine ⟨11696869548153538332893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7985062944872815501921621 11696869548153538332893)
            ·
              rfl

theorem cell23_5535436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 11].length) (baseStart_5535436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535436 prefixEnd_5535436 := by exact prefixLift 5535436
  have htrace : WordTrace (prefixWord ++ tailWord_5535436) baseStart_5535436 baseEnd_5535436 := by
    simpa [prefixWord, tailWord_5535436, baseEnd_5535436] using wordTrace_append hprefix tailTrace_5535436
  have hstable : (prefixWord ++ tailWord_5535436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535436).length < 2 ^ (prefixWord ++ tailWord_5535436).sum := by decide
  have hdescent : baseEnd_5535436 < baseStart_5535436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535447 : List Nat := [1, 1, 3, 2, 1, 3, 3, 4, 1, 2, 2]
def baseStart_5535447 : Nat := 118140960795 + 5535447 * 2 ^ 59
def prefixEnd_5535447 : Nat := 4983230072969 + 3 ^ 40 * 5535447 * 2
def baseEnd_5535447 : Nat := 2842344948488509271855449

theorem tailTrace_5535447 : CollatzResearch.WordTrace tailWord_5535447 prefixEnd_5535447 2842344948488509271855449 := by
  unfold tailWord_5535447
  simp only [CollatzResearch.WordTrace]
  refine ⟨201894338377028372927236595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134596225584685581951491063 201894338377028372927236595)
  ·
    refine ⟨302841507565542559390854893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201894338377028372927236595 302841507565542559390854893)
    ·
      refine ⟨113565565337078459771570585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302841507565542559390854893 113565565337078459771570585)
      ·
        refine ⟨85174174002808844828677939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113565565337078459771570585 85174174002808844828677939)
        ·
          refine ⟨127761261004213267243016909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85174174002808844828677939 127761261004213267243016909)
          ·
            refine ⟨47910472876579975216131341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127761261004213267243016909 47910472876579975216131341)
            ·
              refine ⟨17966427328717490706049253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47910472876579975216131341 17966427328717490706049253)
              ·
                refine ⟨3368705124134529507384235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17966427328717490706049253 3368705124134529507384235)
                ·
                  refine ⟨5053057686201794261076353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3368705124134529507384235 5053057686201794261076353)
                  ·
                    refine ⟨3789793264651345695807265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5053057686201794261076353 3789793264651345695807265)
                    ·
                      refine ⟨2842344948488509271855449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3789793264651345695807265 2842344948488509271855449)
                      ·
                        rfl

theorem cell23_5535447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_5535447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535447 prefixEnd_5535447 := by exact prefixLift 5535447
  have htrace : WordTrace (prefixWord ++ tailWord_5535447) baseStart_5535447 baseEnd_5535447 := by
    simpa [prefixWord, tailWord_5535447, baseEnd_5535447] using wordTrace_append hprefix tailTrace_5535447
  have hstable : (prefixWord ++ tailWord_5535447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535447).length < 2 ^ (prefixWord ++ tailWord_5535447).sum := by decide
  have hdescent : baseEnd_5535447 < baseStart_5535447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535496 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 4, 6]
def baseStart_5535496 : Nat := 118140960795 + 5535496 * 2 ^ 59
def prefixEnd_5535496 : Nat := 4983230072969 + 3 ^ 40 * 5535496 * 2
def baseEnd_5535496 : Nat := 947456703013526526714241

theorem tailTrace_5535496 : CollatzResearch.WordTrace tailWord_5535496 prefixEnd_5535496 947456703013526526714241 := by
  unfold tailWord_5535496
  simp only [CollatzResearch.WordTrace]
  refine ⟨100948062776925427147885171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134597417035900569530513561 100948062776925427147885171)
  ·
    refine ⟨151422094165388140721827757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100948062776925427147885171 151422094165388140721827757)
    ·
      refine ⟨56783285312020552770685409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151422094165388140721827757 56783285312020552770685409)
      ·
        refine ⟨42587463984015414578014057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56783285312020552770685409 42587463984015414578014057)
        ·
          refine ⟨31940597988011560933510543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42587463984015414578014057 31940597988011560933510543)
          ·
            refine ⟨47910896982017341400265815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31940597988011560933510543 47910896982017341400265815)
            ·
              refine ⟨71866345473026012100398723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47910896982017341400265815 71866345473026012100398723)
              ·
                refine ⟨107799518209539018150598085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71866345473026012100398723 107799518209539018150598085)
                ·
                  refine ⟨20212409664288565903237141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107799518209539018150598085 20212409664288565903237141)
                  ·
                    refine ⟨947456703013526526714241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20212409664288565903237141 947456703013526526714241)
                    ·
                      rfl

theorem cell23_5535496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_5535496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535496 prefixEnd_5535496 := by exact prefixLift 5535496
  have htrace : WordTrace (prefixWord ++ tailWord_5535496) baseStart_5535496 baseEnd_5535496 := by
    simpa [prefixWord, tailWord_5535496, baseEnd_5535496] using wordTrace_append hprefix tailTrace_5535496
  have hstable : (prefixWord ++ tailWord_5535496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535496).length < 2 ^ (prefixWord ++ tailWord_5535496).sum := by decide
  have hdescent : baseEnd_5535496 < baseStart_5535496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535540 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_5535540 : Nat := 118140960795 + 5535540 * 2 ^ 59
def prefixEnd_5535540 : Nat := 4983230072969 + 3 ^ 40 * 5535540 * 2
def baseEnd_5535540 : Nat := 2842392702189377407992521

theorem tailTrace_5535540 : CollatzResearch.WordTrace tailWord_5535540 prefixEnd_5535540 2842392702189377407992521 := by
  unfold tailWord_5535540
  simp only [CollatzResearch.WordTrace]
  refine ⟨100948865182845724905186037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134598486910460966540248049 100948865182845724905186037)
  ·
    refine ⟨9463956110891786709861191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100948865182845724905186037 9463956110891786709861191)
    ·
      refine ⟨14195934166337680064791787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9463956110891786709861191 14195934166337680064791787)
      ·
        refine ⟨21293901249506520097187681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14195934166337680064791787 21293901249506520097187681)
        ·
          refine ⟨15970425937129890072890761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21293901249506520097187681 15970425937129890072890761)
          ·
            refine ⟨11977819452847417554668071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15970425937129890072890761 11977819452847417554668071)
            ·
              refine ⟨17966729179271126332002107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11977819452847417554668071 17966729179271126332002107)
              ·
                refine ⟨26950093768906689498003161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17966729179271126332002107 26950093768906689498003161)
                ·
                  refine ⟨20212570326680017123502371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26950093768906689498003161 20212570326680017123502371)
                  ·
                    refine ⟨30318855490020025685253557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20212570326680017123502371 30318855490020025685253557)
                    ·
                      refine ⟨2842392702189377407992521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30318855490020025685253557 2842392702189377407992521)
                      ·
                        rfl

theorem cell23_5535540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_5535540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535540 prefixEnd_5535540 := by exact prefixLift 5535540
  have htrace : WordTrace (prefixWord ++ tailWord_5535540) baseStart_5535540 baseEnd_5535540 := by
    simpa [prefixWord, tailWord_5535540, baseEnd_5535540] using wordTrace_append hprefix tailTrace_5535540
  have hstable : (prefixWord ++ tailWord_5535540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535540).length < 2 ^ (prefixWord ++ tailWord_5535540).sum := by decide
  have hdescent : baseEnd_5535540 < baseStart_5535540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535543 : List Nat := [1, 1, 3, 1, 2, 1, 2, 7, 5]
def baseStart_5535543 : Nat := 118140960795 + 5535543 * 2 ^ 59
def prefixEnd_5535543 : Nat := 4983230072969 + 3 ^ 40 * 5535543 * 2
def baseEnd_5535543 : Nat := 315821582514593432917223

theorem tailTrace_5535543 : CollatzResearch.WordTrace tailWord_5535543 prefixEnd_5535543 315821582514593432917223 := by
  unfold tailWord_5535543
  simp only [CollatzResearch.WordTrace]
  refine ⟨201897839784680581322731283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134598559856453720881820855 201897839784680581322731283)
  ·
    refine ⟨302846759677020871984096925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201897839784680581322731283 302846759677020871984096925)
    ·
      refine ⟨113567534878882826994036347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302846759677020871984096925 113567534878882826994036347)
      ·
        refine ⟨170351302318324240491054521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113567534878882826994036347 170351302318324240491054521)
        ·
          refine ⟨127763476738743180368290891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170351302318324240491054521 127763476738743180368290891)
          ·
            refine ⟨191645215108114770552436337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127763476738743180368290891 191645215108114770552436337)
            ·
              refine ⟨143733911331086077914327253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191645215108114770552436337 143733911331086077914327253)
              ·
                refine ⟨3368763546822329951117045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 143733911331086077914327253 3368763546822329951117045)
                ·
                  refine ⟨315821582514593432917223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3368763546822329951117045 315821582514593432917223)
                  ·
                    rfl

theorem cell23_5535543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 5].length) (baseStart_5535543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535543 prefixEnd_5535543 := by exact prefixLift 5535543
  have htrace : WordTrace (prefixWord ++ tailWord_5535543) baseStart_5535543 baseEnd_5535543 := by
    simpa [prefixWord, tailWord_5535543, baseEnd_5535543] using wordTrace_append hprefix tailTrace_5535543
  have hstable : (prefixWord ++ tailWord_5535543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535543).length < 2 ^ (prefixWord ++ tailWord_5535543).sum := by decide
  have hdescent : baseEnd_5535543 < baseStart_5535543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535613 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_5535613 : Nat := 118140960795 + 5535613 * 2 ^ 59
def prefixEnd_5535613 : Nat := 4983230072969 + 3 ^ 40 * 5535613 * 2
def baseEnd_5535613 : Nat := 2842430186277155622379685

theorem tailTrace_5535613 : CollatzResearch.WordTrace tailWord_5535613 prefixEnd_5535613 2842430186277155622379685 := by
  unfold tailWord_5535613
  simp only [CollatzResearch.WordTrace]
  refine ⟨201900392894426983277779493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134600261929617988851852995 201900392894426983277779493)
  ·
    refine ⟨37856323667705059364583655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201900392894426983277779493 37856323667705059364583655)
    ·
      refine ⟨56784485501557589046875483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37856323667705059364583655 56784485501557589046875483)
      ·
        refine ⟨85176728252336383570313225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56784485501557589046875483 85176728252336383570313225)
        ·
          refine ⟨63882546189252287677734919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85176728252336383570313225 63882546189252287677734919)
          ·
            refine ⟨95823819283878431516602379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63882546189252287677734919 95823819283878431516602379)
            ·
              refine ⟨143735728925817647274903569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95823819283878431516602379 143735728925817647274903569)
              ·
                refine ⟨107801796694363235456177677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143735728925817647274903569 107801796694363235456177677)
                ·
                  refine ⟨40425673760386213296066629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107801796694363235456177677 40425673760386213296066629)
                  ·
                    refine ⟨7579813830072414993012493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40425673760386213296066629 7579813830072414993012493)
                    ·
                      refine ⟨2842430186277155622379685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7579813830072414993012493 2842430186277155622379685)
                      ·
                        rfl

theorem cell23_5535613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_5535613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535613 prefixEnd_5535613 := by exact prefixLift 5535613
  have htrace : WordTrace (prefixWord ++ tailWord_5535613) baseStart_5535613 baseEnd_5535613 := by
    simpa [prefixWord, tailWord_5535613, baseEnd_5535613] using wordTrace_append hprefix tailTrace_5535613
  have hstable : (prefixWord ++ tailWord_5535613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535613).length < 2 ^ (prefixWord ++ tailWord_5535613).sum := by decide
  have hdescent : baseEnd_5535613 < baseStart_5535613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535633 : List Nat := [1, 2, 2, 1, 1, 1, 6, 3, 6]
def baseStart_5535633 : Nat := 118140960795 + 5535633 * 2 ^ 59
def prefixEnd_5535633 : Nat := 4983230072969 + 3 ^ 40 * 5535633 * 2
def baseEnd_5535633 : Nat := 315826717321138393792177

theorem tailTrace_5535633 : CollatzResearch.WordTrace tailWord_5535633 prefixEnd_5535633 315826717321138393792177 := by
  unfold tailWord_5535633
  simp only [CollatzResearch.WordTrace]
  refine ⟨201901122354354526693507553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134600748236236351129005035 201901122354354526693507553)
  ·
    refine ⟨151425841765765895020130665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201901122354354526693507553 151425841765765895020130665)
    ·
      refine ⟨113569381324324421265097999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151425841765765895020130665 113569381324324421265097999)
      ·
        refine ⟨170354071986486631897646999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113569381324324421265097999 170354071986486631897646999)
        ·
          refine ⟨255531107979729947846470499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170354071986486631897646999 255531107979729947846470499)
          ·
            refine ⟨383296661969594921769705749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255531107979729947846470499 383296661969594921769705749)
            ·
              refine ⟨17967031029824761957954957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 383296661969594921769705749 17967031029824761957954957)
              ·
                refine ⟨6737636636184285734233109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17967031029824761957954957 6737636636184285734233109)
                ·
                  refine ⟨315826717321138393792177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6737636636184285734233109 315826717321138393792177)
                  ·
                    rfl

theorem cell23_5535633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 6].length) (baseStart_5535633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535633 prefixEnd_5535633 := by exact prefixLift 5535633
  have htrace : WordTrace (prefixWord ++ tailWord_5535633) baseStart_5535633 baseEnd_5535633 := by
    simpa [prefixWord, tailWord_5535633, baseEnd_5535633] using wordTrace_append hprefix tailTrace_5535633
  have hstable : (prefixWord ++ tailWord_5535633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535633).length < 2 ^ (prefixWord ++ tailWord_5535633).sum := by decide
  have hdescent : baseEnd_5535633 < baseStart_5535633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535677 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_5535677 : Nat := 118140960795 + 5535677 * 2 ^ 59
def prefixEnd_5535677 : Nat := 4983230072969 + 3 ^ 40 * 5535677 * 2
def baseEnd_5535677 : Nat := 2842463049039043371979391

theorem tailTrace_5535677 : CollatzResearch.WordTrace tailWord_5535677 prefixEnd_5535677 2842463049039043371979391 := by
  unfold tailWord_5535677
  simp only [CollatzResearch.WordTrace]
  refine ⟨201902727166195122208109285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134601818110796748138739523 201902727166195122208109285)
  ·
    refine ⟨37856761343661585414020491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201902727166195122208109285 37856761343661585414020491)
    ·
      refine ⟨56785142015492378121030737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37856761343661585414020491 56785142015492378121030737)
      ·
        refine ⟨42588856511619283590773053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56785142015492378121030737 42588856511619283590773053)
        ·
          refine ⟨15970821191857231346539895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42588856511619283590773053 15970821191857231346539895)
          ·
            refine ⟨23956231787785847019809843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15970821191857231346539895 23956231787785847019809843)
            ·
              refine ⟨35934347681678770529714765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23956231787785847019809843 35934347681678770529714765)
              ·
                refine ⟨13475380380629538948643037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35934347681678770529714765 13475380380629538948643037)
                ·
                  refine ⟨5053267642736077105741139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13475380380629538948643037 5053267642736077105741139)
                  ·
                    refine ⟨7579901464104115658611709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5053267642736077105741139 7579901464104115658611709)
                    ·
                      refine ⟨2842463049039043371979391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7579901464104115658611709 2842463049039043371979391)
                      ·
                        rfl

theorem cell23_5535677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_5535677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535677 prefixEnd_5535677 := by exact prefixLift 5535677
  have htrace : WordTrace (prefixWord ++ tailWord_5535677) baseStart_5535677 baseEnd_5535677 := by
    simpa [prefixWord, tailWord_5535677, baseEnd_5535677] using wordTrace_append hprefix tailTrace_5535677
  have hstable : (prefixWord ++ tailWord_5535677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535677).length < 2 ^ (prefixWord ++ tailWord_5535677).sum := by decide
  have hdescent : baseEnd_5535677 < baseStart_5535677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535703 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_5535703 : Nat := 118140960795 + 5535703 * 2 ^ 59
def prefixEnd_5535703 : Nat := 4983230072969 + 3 ^ 40 * 5535703 * 2
def baseEnd_5535703 : Nat := 2842476399536060270254271

theorem tailTrace_5535703 : CollatzResearch.WordTrace tailWord_5535703 prefixEnd_5535703 2842476399536060270254271 := by
  unfold tailWord_5535703
  simp only [CollatzResearch.WordTrace]
  refine ⟨201903675464100928648555763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134602450309400619099037175 201903675464100928648555763)
  ·
    refine ⟨302855513196151392972833645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201903675464100928648555763 302855513196151392972833645)
    ·
      refine ⟨113570817448556772364812617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302855513196151392972833645 113570817448556772364812617)
      ·
        refine ⟨85178113086417579273609463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113570817448556772364812617 85178113086417579273609463)
        ·
          refine ⟨127767169629626368910414195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85178113086417579273609463 127767169629626368910414195)
          ·
            refine ⟨191650754444439553365621293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127767169629626368910414195 191650754444439553365621293)
            ·
              refine ⟨71869032916664832512107985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191650754444439553365621293 71869032916664832512107985)
              ·
                refine ⟨53901774687498624384080989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71869032916664832512107985 53901774687498624384080989)
                ·
                  refine ⟨20213165507811984144030371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53901774687498624384080989 20213165507811984144030371)
                  ·
                    refine ⟨30319748261717976216045557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20213165507811984144030371 30319748261717976216045557)
                    ·
                      refine ⟨2842476399536060270254271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30319748261717976216045557 2842476399536060270254271)
                      ·
                        rfl

theorem cell23_5535703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_5535703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535703 prefixEnd_5535703 := by exact prefixLift 5535703
  have htrace : WordTrace (prefixWord ++ tailWord_5535703) baseStart_5535703 baseEnd_5535703 := by
    simpa [prefixWord, tailWord_5535703, baseEnd_5535703] using wordTrace_append hprefix tailTrace_5535703
  have hstable : (prefixWord ++ tailWord_5535703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535703).length < 2 ^ (prefixWord ++ tailWord_5535703).sum := by decide
  have hdescent : baseEnd_5535703 < baseStart_5535703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535711 : List Nat := [1, 1, 2, 3, 4, 3, 1, 3, 1, 1, 3]
def baseStart_5535711 : Nat := 118140960795 + 5535711 * 2 ^ 59
def prefixEnd_5535711 : Nat := 4983230072969 + 3 ^ 40 * 5535711 * 2
def baseEnd_5535711 : Nat := 2842480507381296238954235

theorem tailTrace_5535711 : CollatzResearch.WordTrace tailWord_5535711 prefixEnd_5535711 2842480507381296238954235 := by
  unfold tailWord_5535711
  simp only [CollatzResearch.WordTrace]
  refine ⟨201903967248071946014846987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134602644832047964009897991 201903967248071946014846987)
  ·
    refine ⟨302855950872107919022270481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201903967248071946014846987 302855950872107919022270481)
    ·
      refine ⟨227141963154080939266702861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302855950872107919022270481 227141963154080939266702861)
      ·
        refine ⟨85178236182780352225013573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227141963154080939266702861 85178236182780352225013573)
        ·
          refine ⟨15970919284271316042190045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85178236182780352225013573 15970919284271316042190045)
          ·
            refine ⟨5989094731601743515821267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15970919284271316042190045 5989094731601743515821267)
            ·
              refine ⟨8983642097402615273731901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5989094731601743515821267 8983642097402615273731901)
              ·
                refine ⟨3368865786525980727649463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8983642097402615273731901 3368865786525980727649463)
                ·
                  refine ⟨5053298679788971091474195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3368865786525980727649463 5053298679788971091474195)
                  ·
                    refine ⟨7579948019683456637211293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5053298679788971091474195 7579948019683456637211293)
                    ·
                      refine ⟨2842480507381296238954235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7579948019683456637211293 2842480507381296238954235)
                      ·
                        rfl

theorem cell23_5535711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_5535711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535711 prefixEnd_5535711 := by exact prefixLift 5535711
  have htrace : WordTrace (prefixWord ++ tailWord_5535711) baseStart_5535711 baseEnd_5535711 := by
    simpa [prefixWord, tailWord_5535711, baseEnd_5535711] using wordTrace_append hprefix tailTrace_5535711
  have hstable : (prefixWord ++ tailWord_5535711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535711).length < 2 ^ (prefixWord ++ tailWord_5535711).sum := by decide
  have hdescent : baseEnd_5535711 < baseStart_5535711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535720 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_5535720 : Nat := 118140960795 + 5535720 * 2 ^ 59
def prefixEnd_5535720 : Nat := 4983230072969 + 3 ^ 40 * 5535720 * 2
def baseEnd_5535720 : Nat := 2842485128707186703741693

theorem tailTrace_5535720 : CollatzResearch.WordTrace tailWord_5535720 prefixEnd_5535720 2842485128707186703741693 := by
  unfold tailWord_5535720
  simp only [CollatzResearch.WordTrace]
  refine ⟨100952147752519670275962307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134602863670026227034616409 100952147752519670275962307)
  ·
    refine ⟨151428221628779505413943461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100952147752519670275962307 151428221628779505413943461)
    ·
      refine ⟨28392791555396157265114399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151428221628779505413943461 28392791555396157265114399)
      ·
        refine ⟨42589187333094235897671599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28392791555396157265114399 42589187333094235897671599)
        ·
          refine ⟨63883780999641353846507399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42589187333094235897671599 63883780999641353846507399)
          ·
            refine ⟨95825671499462030769761099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63883780999641353846507399 95825671499462030769761099)
            ·
              refine ⟨143738507249193046154641649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95825671499462030769761099 143738507249193046154641649)
              ·
                refine ⟨107803880436894784615981237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143738507249193046154641649 107803880436894784615981237)
                ·
                  refine ⟨10106613790958886057748241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107803880436894784615981237 10106613790958886057748241)
                  ·
                    refine ⟨7579960343219164543311181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10106613790958886057748241 7579960343219164543311181)
                    ·
                      refine ⟨2842485128707186703741693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7579960343219164543311181 2842485128707186703741693)
                      ·
                        rfl

theorem cell23_5535720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_5535720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535720 prefixEnd_5535720 := by exact prefixLift 5535720
  have htrace : WordTrace (prefixWord ++ tailWord_5535720) baseStart_5535720 baseEnd_5535720 := by
    simpa [prefixWord, tailWord_5535720, baseEnd_5535720] using wordTrace_append hprefix tailTrace_5535720
  have hstable : (prefixWord ++ tailWord_5535720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535720).length < 2 ^ (prefixWord ++ tailWord_5535720).sum := by decide
  have hdescent : baseEnd_5535720 < baseStart_5535720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535760 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 2, 7, 2]
def baseStart_5535760 : Nat := 118140960795 + 5535760 * 2 ^ 59
def prefixEnd_5535760 : Nat := 4983230072969 + 3 ^ 40 * 5535760 * 2
def baseEnd_5535760 : Nat := 2842505667933366547241509

theorem tailTrace_5535760 : CollatzResearch.WordTrace tailWord_5535760 prefixEnd_5535760 2842505667933366547241509 := by
  unfold tailWord_5535760
  simp only [CollatzResearch.WordTrace]
  refine ⟨100952877212447213691690367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134603836283262951588920489 100952877212447213691690367)
  ·
    refine ⟨151429315818670820537535551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100952877212447213691690367 151429315818670820537535551)
    ·
      refine ⟨227143973728006230806303327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151429315818670820537535551 227143973728006230806303327)
      ·
        refine ⟨340715960592009346209454991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227143973728006230806303327 340715960592009346209454991)
        ·
          refine ⟨511073940888014019314182487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340715960592009346209454991 511073940888014019314182487)
          ·
            refine ⟨766610911332021028971273731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511073940888014019314182487 766610911332021028971273731)
            ·
              refine ⟨1149916366998031543456910597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766610911332021028971273731 1149916366998031543456910597)
              ·
                refine ⟨215609318812130914398170737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1149916366998031543456910597 215609318812130914398170737)
                ·
                  refine ⟨161706989109098185798628053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215609318812130914398170737 161706989109098185798628053)
                  ·
                    refine ⟨3790007557244488729655345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 161706989109098185798628053 3790007557244488729655345)
                    ·
                      refine ⟨2842505667933366547241509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790007557244488729655345 2842505667933366547241509)
                      ·
                        rfl

theorem cell23_5535760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 7, 2].length) (baseStart_5535760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535760 prefixEnd_5535760 := by exact prefixLift 5535760
  have htrace : WordTrace (prefixWord ++ tailWord_5535760) baseStart_5535760 baseEnd_5535760 := by
    simpa [prefixWord, tailWord_5535760, baseEnd_5535760] using wordTrace_append hprefix tailTrace_5535760
  have hstable : (prefixWord ++ tailWord_5535760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535760).length < 2 ^ (prefixWord ++ tailWord_5535760).sum := by decide
  have hdescent : baseEnd_5535760 < baseStart_5535760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535763 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 5]
def baseStart_5535763 : Nat := 118140960795 + 5535763 * 2 ^ 59
def prefixEnd_5535763 : Nat := 4983230072969 + 3 ^ 40 * 5535763 * 2
def baseEnd_5535763 : Nat := 2842507208375330035503995

theorem tailTrace_5535763 : CollatzResearch.WordTrace tailWord_5535763 prefixEnd_5535763 2842507208375330035503995 := by
  unfold tailWord_5535763
  simp only [CollatzResearch.WordTrace]
  refine ⟨201905863843883558895739943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134603909229255705930493295 201905863843883558895739943)
  ·
    refine ⟨302858795765825338343609915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201905863843883558895739943 302858795765825338343609915)
    ·
      refine ⟨454288193648738007515414873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302858795765825338343609915 454288193648738007515414873)
      ·
        refine ⟨340716145236553505636561155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454288193648738007515414873 340716145236553505636561155)
        ·
          refine ⟨511074217854830258454841733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340716145236553505636561155 511074217854830258454841733)
          ·
            refine ⟨95826415847780673460282825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 511074217854830258454841733 95826415847780673460282825)
            ·
              refine ⟨71869811885835505095212119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95826415847780673460282825 71869811885835505095212119)
              ·
                refine ⟨107804717828753257642818179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71869811885835505095212119 107804717828753257642818179)
                ·
                  refine ⟨161707076743129886464227269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107804717828753257642818179 161707076743129886464227269)
                  ·
                    refine ⟨30320076889336853712042613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 161707076743129886464227269 30320076889336853712042613)
                    ·
                      refine ⟨2842507208375330035503995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30320076889336853712042613 2842507208375330035503995)
                      ·
                        rfl

theorem cell23_5535763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_5535763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535763 prefixEnd_5535763 := by exact prefixLift 5535763
  have htrace : WordTrace (prefixWord ++ tailWord_5535763) baseStart_5535763 baseEnd_5535763 := by
    simpa [prefixWord, tailWord_5535763, baseEnd_5535763] using wordTrace_append hprefix tailTrace_5535763
  have hstable : (prefixWord ++ tailWord_5535763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535763).length < 2 ^ (prefixWord ++ tailWord_5535763).sum := by decide
  have hdescent : baseEnd_5535763 < baseStart_5535763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535803 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 6]
def baseStart_5535803 : Nat := 118140960795 + 5535803 * 2 ^ 59
def prefixEnd_5535803 : Nat := 4983230072969 + 3 ^ 40 * 5535803 * 2
def baseEnd_5535803 : Nat := 2842527747601509879003811

theorem tailTrace_5535803 : CollatzResearch.WordTrace tailWord_5535803 prefixEnd_5535803 2842527747601509879003811 := by
  unfold tailWord_5535803
  simp only [CollatzResearch.WordTrace]
  refine ⟨201907322763738645727196063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134604881842492430484797375 201907322763738645727196063)
  ·
    refine ⟨302860984145607968590794095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201907322763738645727196063 302860984145607968590794095)
    ·
      refine ⟨454291476218411952886191143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302860984145607968590794095 454291476218411952886191143)
      ·
        refine ⟨681437214327617929329286715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454291476218411952886191143 681437214327617929329286715)
        ·
          refine ⟨1022155821491426893993930073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681437214327617929329286715 1022155821491426893993930073)
          ·
            refine ⟨766616866118570170495447555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1022155821491426893993930073 766616866118570170495447555)
            ·
              refine ⟨1149925299177855255743171333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766616866118570170495447555 1149925299177855255743171333)
              ·
                refine ⟨215610993595847860451844625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1149925299177855255743171333 215610993595847860451844625)
                ·
                  refine ⟨161708245196885895338883469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215610993595847860451844625 161708245196885895338883469)
                  ·
                    refine ⟨60640591948832210752081301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161708245196885895338883469 60640591948832210752081301)
                    ·
                      refine ⟨2842527747601509879003811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60640591948832210752081301 2842527747601509879003811)
                      ·
                        rfl

theorem cell23_5535803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_5535803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535803 prefixEnd_5535803 := by exact prefixLift 5535803
  have htrace : WordTrace (prefixWord ++ tailWord_5535803) baseStart_5535803 baseEnd_5535803 := by
    simpa [prefixWord, tailWord_5535803, baseEnd_5535803] using wordTrace_append hprefix tailTrace_5535803
  have hstable : (prefixWord ++ tailWord_5535803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535803).length < 2 ^ (prefixWord ++ tailWord_5535803).sum := by decide
  have hdescent : baseEnd_5535803 < baseStart_5535803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535807 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 1, 4, 2]
def baseStart_5535807 : Nat := 118140960795 + 5535807 * 2 ^ 59
def prefixEnd_5535807 : Nat := 4983230072969 + 3 ^ 40 * 5535807 * 2
def baseEnd_5535807 : Nat := 2842529801524127863353793

theorem tailTrace_5535807 : CollatzResearch.WordTrace tailWord_5535807 prefixEnd_5535807 2842529801524127863353793 := by
  unfold tailWord_5535807
  simp only [CollatzResearch.WordTrace]
  refine ⟨201907468655724154410341675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134604979103816102940227783 201907468655724154410341675)
  ·
    refine ⟨302861202983586231615512513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201907468655724154410341675 302861202983586231615512513)
    ·
      refine ⟨227145902237689673711634385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302861202983586231615512513 227145902237689673711634385)
      ·
        refine ⟨170359426678267255283725789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227145902237689673711634385 170359426678267255283725789)
        ·
          refine ⟨63884785004350220731397171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170359426678267255283725789 63884785004350220731397171)
          ·
            refine ⟨95827177506525331097095757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63884785004350220731397171 95827177506525331097095757)
            ·
              refine ⟨35935191564946999161410909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95827177506525331097095757 35935191564946999161410909)
              ·
                refine ⟨13475696836855124685529091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35935191564946999161410909 13475696836855124685529091)
                ·
                  refine ⟨20213545255282687028293637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13475696836855124685529091 20213545255282687028293637)
                  ·
                    refine ⟨3790039735365503817805057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20213545255282687028293637 3790039735365503817805057)
                    ·
                      refine ⟨2842529801524127863353793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790039735365503817805057 2842529801524127863353793)
                      ·
                        rfl

theorem cell23_5535807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 4, 2].length) (baseStart_5535807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535807 prefixEnd_5535807 := by exact prefixLift 5535807
  have htrace : WordTrace (prefixWord ++ tailWord_5535807) baseStart_5535807 baseEnd_5535807 := by
    simpa [prefixWord, tailWord_5535807, baseEnd_5535807] using wordTrace_append hprefix tailTrace_5535807
  have hstable : (prefixWord ++ tailWord_5535807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535807).length < 2 ^ (prefixWord ++ tailWord_5535807).sum := by decide
  have hdescent : baseEnd_5535807 < baseStart_5535807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535847 : List Nat := [1, 1, 5, 1, 1, 2, 1, 6, 5]
def baseStart_5535847 : Nat := 118140960795 + 5535847 * 2 ^ 59
def prefixEnd_5535847 : Nat := 4983230072969 + 3 ^ 40 * 5535847 * 2
def baseEnd_5535847 : Nat := 315838926750034189650401

theorem tailTrace_5535847 : CollatzResearch.WordTrace tailWord_5535847 prefixEnd_5535847 315838926750034189650401 := by
  unfold tailWord_5535847
  simp only [CollatzResearch.WordTrace]
  refine ⟨201908927575579241241797795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134605951717052827494531863 201908927575579241241797795)
  ·
    refine ⟨302863391363368861862696693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201908927575579241241797795 302863391363368861862696693)
    ·
      refine ⟨28393442940315830799627815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 302863391363368861862696693 28393442940315830799627815)
      ·
        refine ⟨42590164410473746199441723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28393442940315830799627815 42590164410473746199441723)
        ·
          refine ⟨63885246615710619299162585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42590164410473746199441723 63885246615710619299162585)
          ·
            refine ⟨47913934961782964474371939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63885246615710619299162585 47913934961782964474371939)
            ·
              refine ⟨71870902442674446711557909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47913934961782964474371939 71870902442674446711557909)
              ·
                refine ⟨3368948552000364689604277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71870902442674446711557909 3368948552000364689604277)
                ·
                  refine ⟨315838926750034189650401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3368948552000364689604277 315838926750034189650401)
                  ·
                    rfl

theorem cell23_5535847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 5].length) (baseStart_5535847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535847 prefixEnd_5535847 := by exact prefixLift 5535847
  have htrace : WordTrace (prefixWord ++ tailWord_5535847) baseStart_5535847 baseEnd_5535847 := by
    simpa [prefixWord, tailWord_5535847, baseEnd_5535847] using wordTrace_append hprefix tailTrace_5535847
  have hstable : (prefixWord ++ tailWord_5535847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535847).length < 2 ^ (prefixWord ++ tailWord_5535847).sum := by decide
  have hdescent : baseEnd_5535847 < baseStart_5535847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535858 : List Nat := [3, 2, 1, 2, 2, 3, 3, 1, 2, 2, 2]
def baseStart_5535858 : Nat := 118140960795 + 5535858 * 2 ^ 59
def prefixEnd_5535858 : Nat := 4983230072969 + 3 ^ 40 * 5535858 * 2
def baseEnd_5535858 : Nat := 2842555989037507163816059

theorem tailTrace_5535858 : CollatzResearch.WordTrace tailWord_5535858 prefixEnd_5535858 2842555989037507163816059 := by
  unfold tailWord_5535858
  simp only [CollatzResearch.WordTrace]
  refine ⟨50477332194634847530112057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134606219185692926746965485 50477332194634847530112057)
  ·
    refine ⟨37857999145976135647584043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50477332194634847530112057 37857999145976135647584043)
    ·
      refine ⟨56786998718964203471376065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37857999145976135647584043 56786998718964203471376065)
      ·
        refine ⟨42590249039223152603532049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56786998718964203471376065 42590249039223152603532049)
        ·
          refine ⟨31942686779417364452649037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42590249039223152603532049 31942686779417364452649037)
          ·
            refine ⟨11978507542281511669743389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31942686779417364452649037 11978507542281511669743389)
            ·
              refine ⟨4491940328355566876153771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11978507542281511669743389 4491940328355566876153771)
              ·
                refine ⟨6737910492533350314230657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4491940328355566876153771 6737910492533350314230657)
                ·
                  refine ⟨5053432869400012735672993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6737910492533350314230657 5053432869400012735672993)
                  ·
                    refine ⟨3790074652050009551754745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5053432869400012735672993 3790074652050009551754745)
                    ·
                      refine ⟨2842555989037507163816059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790074652050009551754745 2842555989037507163816059)
                      ·
                        rfl

theorem cell23_5535858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_5535858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535858 prefixEnd_5535858 := by exact prefixLift 5535858
  have htrace : WordTrace (prefixWord ++ tailWord_5535858) baseStart_5535858 baseEnd_5535858 := by
    simpa [prefixWord, tailWord_5535858, baseEnd_5535858] using wordTrace_append hprefix tailTrace_5535858
  have hstable : (prefixWord ++ tailWord_5535858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535858).length < 2 ^ (prefixWord ++ tailWord_5535858).sum := by decide
  have hdescent : baseEnd_5535858 < baseStart_5535858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535897 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 4, 4, 2]
def baseStart_5535897 : Nat := 118140960795 + 5535897 * 2 ^ 59
def prefixEnd_5535897 : Nat := 4983230072969 + 3 ^ 40 * 5535897 * 2
def baseEnd_5535897 : Nat := 2842576014783032511228379

theorem tailTrace_5535897 : CollatzResearch.WordTrace tailWord_5535897 prefixEnd_5535897 2842576014783032511228379 := by
  unfold tailWord_5535897
  simp only [CollatzResearch.WordTrace]
  refine ⟨201910751225398099781117945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134607167483598733187411963 201910751225398099781117945)
  ·
    refine ⟨151433063419048574835838459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201910751225398099781117945 151433063419048574835838459)
    ·
      refine ⟨227149595128572862253757689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151433063419048574835838459 227149595128572862253757689)
      ·
        refine ⟨170362196346429646690318267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227149595128572862253757689 170362196346429646690318267)
        ·
          refine ⟨255543294519644470035477401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170362196346429646690318267 255543294519644470035477401)
          ·
            refine ⟨191657470889733352526608051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255543294519644470035477401 191657470889733352526608051)
            ·
              refine ⟨287486206334600028789912077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191657470889733352526608051 287486206334600028789912077)
              ·
                refine ⟨107807327375475010796217029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287486206334600028789912077 107807327375475010796217029)
                ·
                  refine ⟨20213873882901564524290693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107807327375475010796217029 20213873882901564524290693)
                  ·
                    refine ⟨3790101353044043348304505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20213873882901564524290693 3790101353044043348304505)
                    ·
                      refine ⟨2842576014783032511228379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790101353044043348304505 2842576014783032511228379)
                      ·
                        rfl

theorem cell23_5535897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 4, 2].length) (baseStart_5535897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535897 prefixEnd_5535897 := by exact prefixLift 5535897
  have htrace : WordTrace (prefixWord ++ tailWord_5535897) baseStart_5535897 baseEnd_5535897 := by
    simpa [prefixWord, tailWord_5535897, baseEnd_5535897] using wordTrace_append hprefix tailTrace_5535897
  have hstable : (prefixWord ++ tailWord_5535897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535897).length < 2 ^ (prefixWord ++ tailWord_5535897).sum := by decide
  have hdescent : baseEnd_5535897 < baseStart_5535897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535954 : List Nat := [3, 2, 2, 2, 1, 3, 2, 2, 6]
def baseStart_5535954 : Nat := 118140960795 + 5535954 * 2 ^ 59
def prefixEnd_5535954 : Nat := 4983230072969 + 3 ^ 40 * 5535954 * 2
def baseEnd_5535954 : Nat := 315845031464482087579513

theorem tailTrace_5535954 : CollatzResearch.WordTrace tailWord_5535954 prefixEnd_5535954 315845031464482087579513 := by
  unfold tailWord_5535954
  simp only [CollatzResearch.WordTrace]
  refine ⟨50478207546547899628985729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134608553457461065677295277 50478207546547899628985729)
  ·
    refine ⟨37858655659910924721739297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50478207546547899628985729 37858655659910924721739297)
    ·
      refine ⟨28393991744933193541304473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37858655659910924721739297 28393991744933193541304473)
      ·
        refine ⟨21295493808699895155978355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28393991744933193541304473 21295493808699895155978355)
        ·
          refine ⟨31943240713049842733967533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21295493808699895155978355 31943240713049842733967533)
          ·
            refine ⟨11978715267393691025237825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31943240713049842733967533 11978715267393691025237825)
            ·
              refine ⟨8984036450545268268928369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11978715267393691025237825 8984036450545268268928369)
              ·
                refine ⟨6738027337908951201696277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8984036450545268268928369 6738027337908951201696277)
                ·
                  refine ⟨315845031464482087579513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6738027337908951201696277 315845031464482087579513)
                  ·
                    rfl

theorem cell23_5535954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_5535954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535954 prefixEnd_5535954 := by exact prefixLift 5535954
  have htrace : WordTrace (prefixWord ++ tailWord_5535954) baseStart_5535954 baseEnd_5535954 := by
    simpa [prefixWord, tailWord_5535954, baseEnd_5535954] using wordTrace_append hprefix tailTrace_5535954
  have hstable : (prefixWord ++ tailWord_5535954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535954).length < 2 ^ (prefixWord ++ tailWord_5535954).sum := by decide
  have hdescent : baseEnd_5535954 < baseStart_5535954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5535987 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 4]
def baseStart_5535987 : Nat := 118140960795 + 5535987 * 2 ^ 59
def prefixEnd_5535987 : Nat := 4983230072969 + 3 ^ 40 * 5535987 * 2
def baseEnd_5535987 : Nat := 2842622228041937159102965

theorem tailTrace_5535987 : CollatzResearch.WordTrace tailWord_5535987 prefixEnd_5535987 2842622228041937159102965 := by
  unfold tailWord_5535987
  simp only [CollatzResearch.WordTrace]
  refine ⟨201914033795072045151894215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134609355863381363434596143 201914033795072045151894215)
  ·
    refine ⟨302871050692608067727841323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201914033795072045151894215 302871050692608067727841323)
    ·
      refine ⟨454306576038912101591761985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302871050692608067727841323 454306576038912101591761985)
      ·
        refine ⟨340729932029184076193821489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454306576038912101591761985 340729932029184076193821489)
        ·
          refine ⟨255547449021888057145366117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340729932029184076193821489 255547449021888057145366117)
          ·
            refine ⟨47915146691604010714756147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255547449021888057145366117 47915146691604010714756147)
            ·
              refine ⟨71872720037406016072134221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47915146691604010714756147 71872720037406016072134221)
              ·
                refine ⟨26952270014027256027050333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71872720037406016072134221 26952270014027256027050333)
                ·
                  refine ⟨10107101255260221010143875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26952270014027256027050333 10107101255260221010143875)
                  ·
                    refine ⟨15160651882890331515215813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10107101255260221010143875 15160651882890331515215813)
                    ·
                      refine ⟨2842622228041937159102965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15160651882890331515215813 2842622228041937159102965)
                      ·
                        rfl

theorem cell23_5535987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_5535987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5535987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5535987 prefixEnd_5535987 := by exact prefixLift 5535987
  have htrace : WordTrace (prefixWord ++ tailWord_5535987) baseStart_5535987 baseEnd_5535987 := by
    simpa [prefixWord, tailWord_5535987, baseEnd_5535987] using wordTrace_append hprefix tailTrace_5535987
  have hstable : (prefixWord ++ tailWord_5535987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5535987).length < 2 ^ (prefixWord ++ tailWord_5535987).sum := by decide
  have hdescent : baseEnd_5535987 < baseStart_5535987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5535987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536014 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_5536014 : Nat := 118140960795 + 5536014 * 2 ^ 59
def prefixEnd_5536014 : Nat := 4983230072969 + 3 ^ 40 * 5536014 * 2
def baseEnd_5536014 : Nat := 947545364006536184488447

theorem tailTrace_5536014 : CollatzResearch.WordTrace tailWord_5536014 prefixEnd_5536014 947545364006536184488447 := by
  unfold tailWord_5536014
  simp only [CollatzResearch.WordTrace]
  refine ⟨25239377320746778595390887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134610012377316152508751397 25239377320746778595390887)
  ·
    refine ⟨37859065981120167893086331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25239377320746778595390887 37859065981120167893086331)
    ·
      refine ⟨56788598971680251839629497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37859065981120167893086331 56788598971680251839629497)
      ·
        refine ⟨42591449228760188879722123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56788598971680251839629497 42591449228760188879722123)
        ·
          refine ⟨63887173843140283319583185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42591449228760188879722123 63887173843140283319583185)
          ·
            refine ⟨47915380382355212489687389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63887173843140283319583185 47915380382355212489687389)
            ·
              refine ⟨17968267643383204683632771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47915380382355212489687389 17968267643383204683632771)
              ·
                refine ⟨26952401465074807025449157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17968267643383204683632771 26952401465074807025449157)
                ·
                  refine ⟨5053575274701526317271717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26952401465074807025449157 5053575274701526317271717)
                  ·
                    refine ⟨947545364006536184488447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5053575274701526317271717 947545364006536184488447)
                    ·
                      rfl

theorem cell23_5536014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_5536014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536014 prefixEnd_5536014 := by exact prefixLift 5536014
  have htrace : WordTrace (prefixWord ++ tailWord_5536014) baseStart_5536014 baseEnd_5536014 := by
    simpa [prefixWord, tailWord_5536014, baseEnd_5536014] using wordTrace_append hprefix tailTrace_5536014
  have hstable : (prefixWord ++ tailWord_5536014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536014).length < 2 ^ (prefixWord ++ tailWord_5536014).sum := by decide
  have hdescent : baseEnd_5536014 < baseStart_5536014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536021 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 3, 2, 2]
def baseStart_5536021 : Nat := 118140960795 + 5536021 * 2 ^ 59
def prefixEnd_5536021 : Nat := 4983230072969 + 3 ^ 40 * 5536021 * 2
def baseEnd_5536021 : Nat := 2842639686384190026077809

theorem tailTrace_5536021 : CollatzResearch.WordTrace tailWord_5536021 prefixEnd_5536021 2842639686384190026077809 := by
  unfold tailWord_5536021
  simp only [CollatzResearch.WordTrace]
  refine ⟨201915273876948868958631917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134610182584632579305754611 201915273876948868958631917)
  ·
    refine ⟨75718227703855825859486969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201915273876948868958631917 75718227703855825859486969)
    ·
      refine ⟨56788670777891869394615227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75718227703855825859486969 56788670777891869394615227)
      ·
        refine ⟨85183006166837804091922841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56788670777891869394615227 85183006166837804091922841)
        ·
          refine ⟨63887254625128353068942131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85183006166837804091922841 63887254625128353068942131)
          ·
            refine ⟨95830881937692529603413197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63887254625128353068942131 95830881937692529603413197)
            ·
              refine ⟨35936580726634698601279949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95830881937692529603413197 35936580726634698601279949)
              ·
                refine ⟨13476217772488011975479981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35936580726634698601279949 13476217772488011975479981)
                ·
                  refine ⟨5053581664683004490804993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13476217772488011975479981 5053581664683004490804993)
                  ·
                    refine ⟨3790186248512253368103745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5053581664683004490804993 3790186248512253368103745)
                    ·
                      refine ⟨2842639686384190026077809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790186248512253368103745 2842639686384190026077809)
                      ·
                        rfl

theorem cell23_5536021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_5536021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536021 prefixEnd_5536021 := by exact prefixLift 5536021
  have htrace : WordTrace (prefixWord ++ tailWord_5536021) baseStart_5536021 baseEnd_5536021 := by
    simpa [prefixWord, tailWord_5536021, baseEnd_5536021] using wordTrace_append hprefix tailTrace_5536021
  have hstable : (prefixWord ++ tailWord_5536021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536021).length < 2 ^ (prefixWord ++ tailWord_5536021).sum := by decide
  have hdescent : baseEnd_5536021 < baseStart_5536021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536034 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_5536034 : Nat := 118140960795 + 5536034 * 2 ^ 59
def prefixEnd_5536034 : Nat := 4983230072969 + 3 ^ 40 * 5536034 * 2
def baseEnd_5536034 : Nat := 2842646361632698475215249

theorem tailTrace_5536034 : CollatzResearch.WordTrace tailWord_5536034 prefixEnd_5536034 2842646361632698475215249 := by
  unfold tailWord_5536034
  simp only [CollatzResearch.WordTrace]
  refine ⟨50478937006475443044713789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134610498683934514785903437 50478937006475443044713789)
  ·
    refine ⟨18929601377428291141767671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50478937006475443044713789 18929601377428291141767671)
    ·
      refine ⟨28394402066142436712651507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18929601377428291141767671 28394402066142436712651507)
      ·
        refine ⟨42591603099213655068977261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28394402066142436712651507 42591603099213655068977261)
        ·
          refine ⟨15971851162205120650866473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42591603099213655068977261 15971851162205120650866473)
          ·
            refine ⟨11978888371653840488149855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15971851162205120650866473 11978888371653840488149855)
            ·
              refine ⟨17968332557480760732224783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11978888371653840488149855 17968332557480760732224783)
              ·
                refine ⟨26952498836221141098337175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17968332557480760732224783 26952498836221141098337175)
                ·
                  refine ⟨40428748254331711647505763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26952498836221141098337175 40428748254331711647505763)
                  ·
                    refine ⟨60643122381497567471258645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40428748254331711647505763 60643122381497567471258645)
                    ·
                      refine ⟨2842646361632698475215249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60643122381497567471258645 2842646361632698475215249)
                      ·
                        rfl

theorem cell23_5536034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_5536034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536034 prefixEnd_5536034 := by exact prefixLift 5536034
  have htrace : WordTrace (prefixWord ++ tailWord_5536034) baseStart_5536034 baseEnd_5536034 := by
    simpa [prefixWord, tailWord_5536034, baseEnd_5536034] using wordTrace_append hprefix tailTrace_5536034
  have hstable : (prefixWord ++ tailWord_5536034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536034).length < 2 ^ (prefixWord ++ tailWord_5536034).sum := by decide
  have hdescent : baseEnd_5536034 < baseStart_5536034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536071 : List Nat := [1, 1, 4, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_5536071 : Nat := 118140960795 + 5536071 * 2 ^ 59
def prefixEnd_5536071 : Nat := 4983230072969 + 3 ^ 40 * 5536071 * 2
def baseEnd_5536071 : Nat := 2842665360416914830452579

theorem tailTrace_5536071 : CollatzResearch.WordTrace tailWord_5536071 prefixEnd_5536071 2842665360416914830452579 := by
  unfold tailWord_5536071
  simp only [CollatzResearch.WordTrace]
  refine ⟨201917097526767727497952067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134611398351178484998634711 201917097526767727497952067)
  ·
    refine ⟨302875646290151591246928101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201917097526767727497952067 302875646290151591246928101)
    ·
      refine ⟨56789183679403423358799019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302875646290151591246928101 56789183679403423358799019)
      ·
        refine ⟨85183775519105135038198529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56789183679403423358799019 85183775519105135038198529)
        ·
          refine ⟨63887831639328851278648897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85183775519105135038198529 63887831639328851278648897)
          ·
            refine ⟨47915873729496638458986673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63887831639328851278648897 47915873729496638458986673)
            ·
              refine ⟨35936905297122478844240005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47915873729496638458986673 35936905297122478844240005)
              ·
                refine ⟨6738169743210464783295001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35936905297122478844240005 6738169743210464783295001)
                ·
                  refine ⟨5053627307407848587471251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6738169743210464783295001 5053627307407848587471251)
                  ·
                    refine ⟨7580440961111772881206877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5053627307407848587471251 7580440961111772881206877)
                    ·
                      refine ⟨2842665360416914830452579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7580440961111772881206877 2842665360416914830452579)
                      ·
                        rfl

theorem cell23_5536071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_5536071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536071 prefixEnd_5536071 := by exact prefixLift 5536071
  have htrace : WordTrace (prefixWord ++ tailWord_5536071) baseStart_5536071 baseEnd_5536071 := by
    simpa [prefixWord, tailWord_5536071, baseEnd_5536071] using wordTrace_append hprefix tailTrace_5536071
  have hstable : (prefixWord ++ tailWord_5536071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536071).length < 2 ^ (prefixWord ++ tailWord_5536071).sum := by decide
  have hdescent : baseEnd_5536071 < baseStart_5536071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536087 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 1, 8]
def baseStart_5536087 : Nat := 118140960795 + 5536087 * 2 ^ 59
def prefixEnd_5536087 : Nat := 4983230072969 + 3 ^ 40 * 5536087 * 2
def baseEnd_5536087 : Nat := 947557858702462255950835

theorem tailTrace_5536087 : CollatzResearch.WordTrace tailWord_5536087 prefixEnd_5536087 947557858702462255950835 := by
  unfold tailWord_5536087
  simp only [CollatzResearch.WordTrace]
  refine ⟨201917681094709762230534515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134611787396473174820356343 201917681094709762230534515)
  ·
    refine ⟨302876521642064643345801773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201917681094709762230534515 302876521642064643345801773)
    ·
      refine ⟨113578695615774241254675665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302876521642064643345801773 113578695615774241254675665)
      ·
        refine ⟨85184021711830680941006749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113578695615774241254675665 85184021711830680941006749)
        ·
          refine ⟨31944008141936505352877531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85184021711830680941006749 31944008141936505352877531)
          ·
            refine ⟨47916012212904758029316297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31944008141936505352877531 47916012212904758029316297)
            ·
              refine ⟨35937009159678568521987223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47916012212904758029316297 35937009159678568521987223)
              ·
                refine ⟨53905513739517852782980835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35937009159678568521987223 53905513739517852782980835)
                ·
                  refine ⟨80858270609276779174471253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53905513739517852782980835 80858270609276779174471253)
                  ·
                    refine ⟨947557858702462255950835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80858270609276779174471253 947557858702462255950835)
                    ·
                      rfl

theorem cell23_5536087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_5536087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536087 prefixEnd_5536087 := by exact prefixLift 5536087
  have htrace : WordTrace (prefixWord ++ tailWord_5536087) baseStart_5536087 baseEnd_5536087 := by
    simpa [prefixWord, tailWord_5536087, baseEnd_5536087] using wordTrace_append hprefix tailTrace_5536087
  have hstable : (prefixWord ++ tailWord_5536087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536087).length < 2 ^ (prefixWord ++ tailWord_5536087).sum := by decide
  have hdescent : baseEnd_5536087 < baseStart_5536087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536092 : List Nat := [2, 2, 4, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_5536092 : Nat := 118140960795 + 5536092 * 2 ^ 59
def prefixEnd_5536092 : Nat := 4983230072969 + 3 ^ 40 * 5536092 * 2
def baseEnd_5536092 : Nat := 2842676143510659248289983

theorem tailTrace_5536092 : CollatzResearch.WordTrace tailWord_5536092 prefixEnd_5536092 2842676143510659248289983 := by
  unfold tailWord_5536092
  simp only [CollatzResearch.WordTrace]
  refine ⟨100958931729845824042233265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134611908973127765389644353 100958931729845824042233265)
  ·
    refine ⟨75719198797384368031674949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100958931729845824042233265 75719198797384368031674949)
    ·
      refine ⟨14197349774509569005939053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75719198797384368031674949 14197349774509569005939053)
      ·
        refine ⟨5324006165441088377227145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14197349774509569005939053 5324006165441088377227145)
        ·
          refine ⟨3993004624080816282920359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5324006165441088377227145 3993004624080816282920359)
          ·
            refine ⟨5989506936121224424380539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3993004624080816282920359 5989506936121224424380539)
            ·
              refine ⟨8984260404181836636570809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5989506936121224424380539 8984260404181836636570809)
              ·
                refine ⟨6738195303136377477428107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8984260404181836636570809 6738195303136377477428107)
                ·
                  refine ⟨10107292954704566216142161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6738195303136377477428107 10107292954704566216142161)
                  ·
                    refine ⟨7580469716028424662106621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10107292954704566216142161 7580469716028424662106621)
                    ·
                      refine ⟨2842676143510659248289983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7580469716028424662106621 2842676143510659248289983)
                      ·
                        rfl

theorem cell23_5536092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_5536092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536092 prefixEnd_5536092 := by exact prefixLift 5536092
  have htrace : WordTrace (prefixWord ++ tailWord_5536092) baseStart_5536092 baseEnd_5536092 := by
    simpa [prefixWord, tailWord_5536092, baseEnd_5536092] using wordTrace_append hprefix tailTrace_5536092
  have hstable : (prefixWord ++ tailWord_5536092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536092).length < 2 ^ (prefixWord ++ tailWord_5536092).sum := by decide
  have hdescent : baseEnd_5536092 < baseStart_5536092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536098 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_5536098 : Nat := 118140960795 + 5536098 * 2 ^ 59
def prefixEnd_5536098 : Nat := 4983230072969 + 3 ^ 40 * 5536098 * 2
def baseEnd_5536098 : Nat := 2842679224394586224814955

theorem tailTrace_5536098 : CollatzResearch.WordTrace tailWord_5536098 prefixEnd_5536098 2842679224394586224814955 := by
  unfold tailWord_5536098
  simp only [CollatzResearch.WordTrace]
  refine ⟨50479520574417477777296237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134612054865113274072789965 50479520574417477777296237)
  ·
    refine ⟨18929820215406554166486089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50479520574417477777296237 18929820215406554166486089)
    ·
      refine ⟨14197365161554915624864567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18929820215406554166486089 14197365161554915624864567)
      ·
        refine ⟨21296047742332373437296851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14197365161554915624864567 21296047742332373437296851)
        ·
          refine ⟨31944071613498560155945277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21296047742332373437296851 31944071613498560155945277)
          ·
            refine ⟨11979026855061960058479479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31944071613498560155945277 11979026855061960058479479)
            ·
              refine ⟨17968540282592940087719219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11979026855061960058479479 17968540282592940087719219)
              ·
                refine ⟨26952810423889410131578829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17968540282592940087719219 26952810423889410131578829)
                ·
                  refine ⟨10107303908958528799342061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26952810423889410131578829 10107303908958528799342061)
                  ·
                    refine ⟨3790238965859448299753273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10107303908958528799342061 3790238965859448299753273)
                    ·
                      refine ⟨2842679224394586224814955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790238965859448299753273 2842679224394586224814955)
                      ·
                        rfl

theorem cell23_5536098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_5536098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536098 prefixEnd_5536098 := by exact prefixLift 5536098
  have htrace : WordTrace (prefixWord ++ tailWord_5536098) baseStart_5536098 baseEnd_5536098 := by
    simpa [prefixWord, tailWord_5536098, baseEnd_5536098] using wordTrace_append hprefix tailTrace_5536098
  have hstable : (prefixWord ++ tailWord_5536098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536098).length < 2 ^ (prefixWord ++ tailWord_5536098).sum := by decide
  have hdescent : baseEnd_5536098 < baseStart_5536098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536107 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 4]
def baseStart_5536107 : Nat := 118140960795 + 5536107 * 2 ^ 59
def prefixEnd_5536107 : Nat := 4983230072969 + 3 ^ 40 * 5536107 * 2
def baseEnd_5536107 : Nat := 2842683845720476689602413

theorem tailTrace_5536107 : CollatzResearch.WordTrace tailWord_5536107 prefixEnd_5536107 2842683845720476689602413 := by
  unfold tailWord_5536107
  simp only [CollatzResearch.WordTrace]
  refine ⟨201918410554637305646262575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134612273703091537097508383 201918410554637305646262575)
  ·
    refine ⟨302877615831955958469393863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201918410554637305646262575 302877615831955958469393863)
    ·
      refine ⟨454316423747933937704090795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302877615831955958469393863 454316423747933937704090795)
      ·
        refine ⟨681474635621900906556136193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454316423747933937704090795 681474635621900906556136193)
        ·
          refine ⟨511105976716425679917102145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 681474635621900906556136193 511105976716425679917102145)
          ·
            refine ⟨383329482537319259937826609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511105976716425679917102145 383329482537319259937826609)
            ·
              refine ⟨287497111902989444953369957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383329482537319259937826609 287497111902989444953369957)
              ·
                refine ⟨53905708481810520928756867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 287497111902989444953369957 53905708481810520928756867)
                ·
                  refine ⟨80858562722715781393135301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53905708481810520928756867 80858562722715781393135301)
                  ·
                    refine ⟨15160980510509209011212869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80858562722715781393135301 15160980510509209011212869)
                    ·
                      refine ⟨2842683845720476689602413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15160980510509209011212869 2842683845720476689602413)
                      ·
                        rfl

theorem cell23_5536107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 4].length) (baseStart_5536107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536107 prefixEnd_5536107 := by exact prefixLift 5536107
  have htrace : WordTrace (prefixWord ++ tailWord_5536107) baseStart_5536107 baseEnd_5536107 := by
    simpa [prefixWord, tailWord_5536107, baseEnd_5536107] using wordTrace_append hprefix tailTrace_5536107
  have hstable : (prefixWord ++ tailWord_5536107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536107).length < 2 ^ (prefixWord ++ tailWord_5536107).sum := by decide
  have hdescent : baseEnd_5536107 < baseStart_5536107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536111 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 4, 2, 2]
def baseStart_5536111 : Nat := 118140960795 + 5536111 * 2 ^ 59
def prefixEnd_5536111 : Nat := 4983230072969 + 3 ^ 40 * 5536111 * 2
def baseEnd_5536111 : Nat := 2842685899643094673952395

theorem tailTrace_5536111 : CollatzResearch.WordTrace tailWord_5536111 prefixEnd_5536111 2842685899643094673952395 := by
  unfold tailWord_5536111
  simp only [CollatzResearch.WordTrace]
  refine ⟨201918556446622814329408187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134612370964415209552938791 201918556446622814329408187)
  ·
    refine ⟨302877834669934221494112281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201918556446622814329408187 302877834669934221494112281)
    ·
      refine ⟨227158376002450666120584211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302877834669934221494112281 227158376002450666120584211)
      ·
        refine ⟨340737564003675999180876317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227158376002450666120584211 340737564003675999180876317)
        ·
          refine ⟨127776586501378499692828619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340737564003675999180876317 127776586501378499692828619)
          ·
            refine ⟨191664879752067749539242929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127776586501378499692828619 191664879752067749539242929)
            ·
              refine ⟨143748659814050812154432197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191664879752067749539242929 143748659814050812154432197)
              ·
                refine ⟨26952873715134527278956037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143748659814050812154432197 26952873715134527278956037)
                ·
                  refine ⟨5053663821587723864804257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26952873715134527278956037 5053663821587723864804257)
                  ·
                    refine ⟨3790247866190792898603193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5053663821587723864804257 3790247866190792898603193)
                    ·
                      refine ⟨2842685899643094673952395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790247866190792898603193 2842685899643094673952395)
                      ·
                        rfl

theorem cell23_5536111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 2, 2].length) (baseStart_5536111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536111 prefixEnd_5536111 := by exact prefixLift 5536111
  have htrace : WordTrace (prefixWord ++ tailWord_5536111) baseStart_5536111 baseEnd_5536111 := by
    simpa [prefixWord, tailWord_5536111, baseEnd_5536111] using wordTrace_append hprefix tailTrace_5536111
  have hstable : (prefixWord ++ tailWord_5536111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536111).length < 2 ^ (prefixWord ++ tailWord_5536111).sum := by decide
  have hdescent : baseEnd_5536111 < baseStart_5536111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536114 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_5536114 : Nat := 118140960795 + 5536114 * 2 ^ 59
def prefixEnd_5536114 : Nat := 4983230072969 + 3 ^ 40 * 5536114 * 2
def baseEnd_5536114 : Nat := 2842687440085058162214881

theorem tailTrace_5536114 : CollatzResearch.WordTrace tailWord_5536114 prefixEnd_5536114 2842687440085058162214881 := by
  unfold tailWord_5536114
  simp only [CollatzResearch.WordTrace]
  refine ⟨50479666466402986460441849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134612443910407963894511597 50479666466402986460441849)
  ·
    refine ⟨37859749849802239845331387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50479666466402986460441849 37859749849802239845331387)
    ·
      refine ⟨56789624774703359767997081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37859749849802239845331387 56789624774703359767997081)
      ·
        refine ⟨42592218581027519825997811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56789624774703359767997081 42592218581027519825997811)
        ·
          refine ⟨63888327871541279738996717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42592218581027519825997811 63888327871541279738996717)
          ·
            refine ⟨23958122951827979902123769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63888327871541279738996717 23958122951827979902123769)
            ·
              refine ⟨17968592213870984926592827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23958122951827979902123769 17968592213870984926592827)
              ·
                refine ⟨26952888320806477389889241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17968592213870984926592827 26952888320806477389889241)
                ·
                  refine ⟨20214666240604858042416931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26952888320806477389889241 20214666240604858042416931)
                  ·
                    refine ⟨30321999360907287063625397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20214666240604858042416931 30321999360907287063625397)
                    ·
                      refine ⟨2842687440085058162214881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30321999360907287063625397 2842687440085058162214881)
                      ·
                        rfl

theorem cell23_5536114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_5536114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536114 prefixEnd_5536114 := by exact prefixLift 5536114
  have htrace : WordTrace (prefixWord ++ tailWord_5536114) baseStart_5536114 baseEnd_5536114 := by
    simpa [prefixWord, tailWord_5536114, baseEnd_5536114] using wordTrace_append hprefix tailTrace_5536114
  have hstable : (prefixWord ++ tailWord_5536114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536114).length < 2 ^ (prefixWord ++ tailWord_5536114).sum := by decide
  have hdescent : baseEnd_5536114 < baseStart_5536114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536168 : List Nat := [2, 1, 6, 1, 1, 1, 1, 5, 5]
def baseStart_5536168 : Nat := 118140960795 + 5536168 * 2 ^ 59
def prefixEnd_5536168 : Nat := 4983230072969 + 3 ^ 40 * 5536168 * 2
def baseEnd_5536168 : Nat := 315857240893377883437737

theorem tailTrace_5536168 : CollatzResearch.WordTrace tailWord_5536168 prefixEnd_5536168 315857240893377883437737 := by
  unfold tailWord_5536168
  simp only [CollatzResearch.WordTrace]
  refine ⟨100960317703708156532116579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134613756938277542042822105 100960317703708156532116579)
  ·
    refine ⟨151440476555562234798174869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100960317703708156532116579 151440476555562234798174869)
    ·
      refine ⟨7098772338541979756164447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 151440476555562234798174869 7098772338541979756164447)
      ·
        refine ⟨10648158507812969634246671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7098772338541979756164447 10648158507812969634246671)
        ·
          refine ⟨15972237761719454451370007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10648158507812969634246671 15972237761719454451370007)
          ·
            refine ⟨23958356642579181677055011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15972237761719454451370007 23958356642579181677055011)
            ·
              refine ⟨35937534963868772515582517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23958356642579181677055011 35937534963868772515582517)
              ·
                refine ⟨3369143902862697423335861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35937534963868772515582517 3369143902862697423335861)
                ·
                  refine ⟨315857240893377883437737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3369143902862697423335861 315857240893377883437737)
                  ·
                    rfl

theorem cell23_5536168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 5].length) (baseStart_5536168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536168 prefixEnd_5536168 := by exact prefixLift 5536168
  have htrace : WordTrace (prefixWord ++ tailWord_5536168) baseStart_5536168 baseEnd_5536168 := by
    simpa [prefixWord, tailWord_5536168, baseEnd_5536168] using wordTrace_append hprefix tailTrace_5536168
  have hstable : (prefixWord ++ tailWord_5536168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536168).length < 2 ^ (prefixWord ++ tailWord_5536168).sum := by decide
  have hdescent : baseEnd_5536168 < baseStart_5536168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536184 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_5536184 : Nat := 118140960795 + 5536184 * 2 ^ 59
def prefixEnd_5536184 : Nat := 4983230072969 + 3 ^ 40 * 5536184 * 2
def baseEnd_5536184 : Nat := 2842723383730872888339559

theorem tailTrace_5536184 : CollatzResearch.WordTrace tailWord_5536184 prefixEnd_5536184 2842723383730872888339559 := by
  unfold tailWord_5536184
  simp only [CollatzResearch.WordTrace]
  refine ⟨100960609487679173898407803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134614145983572231864543737 100960609487679173898407803)
  ·
    refine ⟨151440914231518760847611705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100960609487679173898407803 151440914231518760847611705)
    ·
      refine ⟨113580685673639070635708779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151440914231518760847611705 113580685673639070635708779)
      ·
        refine ⟨170371028510458605953563169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113580685673639070635708779 170371028510458605953563169)
        ·
          refine ⟨127778271382843954465172377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170371028510458605953563169 127778271382843954465172377)
          ·
            refine ⟨95833703537132965848879283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127778271382843954465172377 95833703537132965848879283)
            ·
              refine ⟨143750555305699448773318925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95833703537132965848879283 143750555305699448773318925)
              ·
                refine ⟨53906458239637293289994597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143750555305699448773318925 53906458239637293289994597)
                ·
                  refine ⟨10107460919931992491873987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53906458239637293289994597 10107460919931992491873987)
                  ·
                    refine ⟨15161191379897988737810981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10107460919931992491873987 15161191379897988737810981)
                    ·
                      refine ⟨2842723383730872888339559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15161191379897988737810981 2842723383730872888339559)
                      ·
                        rfl

theorem cell23_5536184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_5536184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536184 prefixEnd_5536184 := by exact prefixLift 5536184
  have htrace : WordTrace (prefixWord ++ tailWord_5536184) baseStart_5536184 baseEnd_5536184 := by
    simpa [prefixWord, tailWord_5536184, baseEnd_5536184] using wordTrace_append hprefix tailTrace_5536184
  have hstable : (prefixWord ++ tailWord_5536184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536184).length < 2 ^ (prefixWord ++ tailWord_5536184).sum := by decide
  have hdescent : baseEnd_5536184 < baseStart_5536184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536201 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 2, 4, 2]
def baseStart_5536201 : Nat := 118140960795 + 5536201 * 2 ^ 59
def prefixEnd_5536201 : Nat := 4983230072969 + 3 ^ 40 * 5536201 * 2
def baseEnd_5536201 : Nat := 2842732112901999321826981

theorem tailTrace_5536201 : CollatzResearch.WordTrace tailWord_5536201 prefixEnd_5536201 2842732112901999321826981 := by
  unfold tailWord_5536201
  simp only [CollatzResearch.WordTrace]
  refine ⟨201921839016296759700184457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134614559344197839800122971 201921839016296759700184457)
  ·
    refine ⟨151441379262222569775138343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201921839016296759700184457 151441379262222569775138343)
    ·
      refine ⟨227162068893333854662707515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151441379262222569775138343 227162068893333854662707515)
      ·
        refine ⟨340743103340000781994061273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227162068893333854662707515 340743103340000781994061273)
        ·
          refine ⟨255557327505000586495545955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340743103340000781994061273 255557327505000586495545955)
          ·
            refine ⟨383335991257500879743318933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255557327505000586495545955 383335991257500879743318933)
            ·
              refine ⟨17968874590195353737968075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 383335991257500879743318933 17968874590195353737968075)
              ·
                refine ⟨26953311885293030606952113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17968874590195353737968075 26953311885293030606952113)
                ·
                  refine ⟨20214983913969772955214085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26953311885293030606952113 20214983913969772955214085)
                  ·
                    refine ⟨3790309483869332429102641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20214983913969772955214085 3790309483869332429102641)
                    ·
                      refine ⟨2842732112901999321826981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790309483869332429102641 2842732112901999321826981)
                      ·
                        rfl

theorem cell23_5536201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 4, 2].length) (baseStart_5536201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536201 prefixEnd_5536201 := by exact prefixLift 5536201
  have htrace : WordTrace (prefixWord ++ tailWord_5536201) baseStart_5536201 baseEnd_5536201 := by
    simpa [prefixWord, tailWord_5536201, baseEnd_5536201] using wordTrace_append hprefix tailTrace_5536201
  have hstable : (prefixWord ++ tailWord_5536201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536201).length < 2 ^ (prefixWord ++ tailWord_5536201).sum := by decide
  have hdescent : baseEnd_5536201 < baseStart_5536201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536221 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_5536221 : Nat := 118140960795 + 5536221 * 2 ^ 59
def prefixEnd_5536221 : Nat := 4983230072969 + 3 ^ 40 * 5536221 * 2
def baseEnd_5536221 : Nat := 2842742382515089243576889

theorem tailTrace_5536221 : CollatzResearch.WordTrace tailWord_5536221 prefixEnd_5536221 2842742382515089243576889 := by
  unfold tailWord_5536221
  simp only [CollatzResearch.WordTrace]
  refine ⟨201922568476224303115912517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134615045650816202077275011 201922568476224303115912517)
  ·
    refine ⟨37860481589292056834233597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201922568476224303115912517 37860481589292056834233597)
    ·
      refine ⟨14197680595984521312837599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37860481589292056834233597 14197680595984521312837599)
      ·
        refine ⟨21296520893976781969256399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14197680595984521312837599 21296520893976781969256399)
        ·
          refine ⟨31944781340965172953884599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21296520893976781969256399 31944781340965172953884599)
          ·
            refine ⟨47917172011447759430826899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31944781340965172953884599 47917172011447759430826899)
            ·
              refine ⟨71875758017171639146240349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47917172011447759430826899 71875758017171639146240349)
              ·
                refine ⟨26953409256439364679840131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71875758017171639146240349 26953409256439364679840131)
                ·
                  refine ⟨40430113884659047019760197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26953409256439364679840131 40430113884659047019760197)
                  ·
                    refine ⟨7580646353373571316205037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40430113884659047019760197 7580646353373571316205037)
                    ·
                      refine ⟨2842742382515089243576889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7580646353373571316205037 2842742382515089243576889)
                      ·
                        rfl

theorem cell23_5536221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_5536221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536221 prefixEnd_5536221 := by exact prefixLift 5536221
  have htrace : WordTrace (prefixWord ++ tailWord_5536221) baseStart_5536221 baseEnd_5536221 := by
    simpa [prefixWord, tailWord_5536221, baseEnd_5536221] using wordTrace_append hprefix tailTrace_5536221
  have hstable : (prefixWord ++ tailWord_5536221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536221).length < 2 ^ (prefixWord ++ tailWord_5536221).sum := by decide
  have hdescent : baseEnd_5536221 < baseStart_5536221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536238 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_5536238 : Nat := 118140960795 + 5536238 * 2 ^ 59
def prefixEnd_5536238 : Nat := 4983230072969 + 3 ^ 40 * 5536238 * 2
def baseEnd_5536238 : Nat := 2842751111686215677064311

theorem tailTrace_5536238 : CollatzResearch.WordTrace tailWord_5536238 prefixEnd_5536238 2842751111686215677064311 := by
  unfold tailWord_5536238
  simp only [CollatzResearch.WordTrace]
  refine ⟨25240398564645339377410171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134615459011441810012854245 25240398564645339377410171)
  ·
    refine ⟨37860597846968009066115257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25240398564645339377410171 37860597846968009066115257)
    ·
      refine ⟨28395448385226006799586443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37860597846968009066115257 28395448385226006799586443)
      ·
        refine ⟨42593172577839010199379665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28395448385226006799586443 42593172577839010199379665)
        ·
          refine ⟨31944879433379257649534749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42593172577839010199379665 31944879433379257649534749)
          ·
            refine ⟨11979329787517221618575531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31944879433379257649534749 11979329787517221618575531)
            ·
              refine ⟨17968994681275832427863297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11979329787517221618575531 17968994681275832427863297)
              ·
                refine ⟨13476746010956874320897473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17968994681275832427863297 13476746010956874320897473)
                ·
                  refine ⟨10107559508217655740673105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13476746010956874320897473 10107559508217655740673105)
                  ·
                    refine ⟨7580669631163241805504829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10107559508217655740673105 7580669631163241805504829)
                    ·
                      refine ⟨2842751111686215677064311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7580669631163241805504829 2842751111686215677064311)
                      ·
                        rfl

theorem cell23_5536238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_5536238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536238 prefixEnd_5536238 := by exact prefixLift 5536238
  have htrace : WordTrace (prefixWord ++ tailWord_5536238) baseStart_5536238 baseEnd_5536238 := by
    simpa [prefixWord, tailWord_5536238, baseEnd_5536238] using wordTrace_append hprefix tailTrace_5536238
  have hstable : (prefixWord ++ tailWord_5536238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536238).length < 2 ^ (prefixWord ++ tailWord_5536238).sum := by decide
  have hdescent : baseEnd_5536238 < baseStart_5536238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536261 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 3, 5, 2]
def baseStart_5536261 : Nat := 118140960795 + 5536261 * 2 ^ 59
def prefixEnd_5536261 : Nat := 4983230072969 + 3 ^ 40 * 5536261 * 2
def baseEnd_5536261 : Nat := 2842762921741269087076705

theorem tailTrace_5536261 : CollatzResearch.WordTrace tailWord_5536261 prefixEnd_5536261 2842762921741269087076705 := by
  unfold tailWord_5536261
  simp only [CollatzResearch.WordTrace]
  refine ⟨201924027396079389947368637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134616018264052926631579091 201924027396079389947368637)
  ·
    refine ⟨75721510273529771230263239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201924027396079389947368637 75721510273529771230263239)
    ·
      refine ⟨113582265410294656845394859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75721510273529771230263239 113582265410294656845394859)
      ·
        refine ⟨170373398115441985268092289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113582265410294656845394859 170373398115441985268092289)
        ·
          refine ⟨127780048586581488951069217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170373398115441985268092289 127780048586581488951069217)
          ·
            refine ⟨95835036439936116713301913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127780048586581488951069217 95835036439936116713301913)
            ·
              refine ⟨71876277329952087534976435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95835036439936116713301913 71876277329952087534976435)
              ·
                refine ⟨107814415994928131302464653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71876277329952087534976435 107814415994928131302464653)
                ·
                  refine ⟨40430405998098049238424245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107814415994928131302464653 40430405998098049238424245)
                  ·
                    refine ⟨3790350562321692116102273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40430405998098049238424245 3790350562321692116102273)
                    ·
                      refine ⟨2842762921741269087076705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790350562321692116102273 2842762921741269087076705)
                      ·
                        rfl

theorem cell23_5536261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 5, 2].length) (baseStart_5536261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536261 prefixEnd_5536261 := by exact prefixLift 5536261
  have htrace : WordTrace (prefixWord ++ tailWord_5536261) baseStart_5536261 baseEnd_5536261 := by
    simpa [prefixWord, tailWord_5536261, baseEnd_5536261] using wordTrace_append hprefix tailTrace_5536261
  have hstable : (prefixWord ++ tailWord_5536261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536261).length < 2 ^ (prefixWord ++ tailWord_5536261).sum := by decide
  have hdescent : baseEnd_5536261 < baseStart_5536261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536304 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 6]
def baseStart_5536304 : Nat := 118140960795 + 5536304 * 2 ^ 59
def prefixEnd_5536304 : Nat := 4983230072969 + 3 ^ 40 * 5536304 * 2
def baseEnd_5536304 : Nat := 2842785001409412418839007

theorem tailTrace_5536304 : CollatzResearch.WordTrace tailWord_5536304 prefixEnd_5536304 2842785001409412418839007 := by
  unfold tailWord_5536304
  simp only [CollatzResearch.WordTrace]
  refine ⟨100962797867461804145591983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134617063823282405527455977 100962797867461804145591983)
  ·
    refine ⟨151444196801192706218387975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100962797867461804145591983 151444196801192706218387975)
    ·
      refine ⟨227166295201789059327581963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151444196801192706218387975 227166295201789059327581963)
      ·
        refine ⟨340749442802683588991372945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227166295201789059327581963 340749442802683588991372945)
        ·
          refine ⟨255562082102012691743529709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340749442802683588991372945 255562082102012691743529709)
          ·
            refine ⟨95835780788254759403823641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255562082102012691743529709 95835780788254759403823641)
            ·
              refine ⟨71876835591191069552867731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95835780788254759403823641 71876835591191069552867731)
              ·
                refine ⟨107815253386786604329301597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71876835591191069552867731 107815253386786604329301597)
                ·
                  refine ⟨40430720020044976623488099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107815253386786604329301597 40430720020044976623488099)
                  ·
                    refine ⟨60646080030067464935232149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40430720020044976623488099 60646080030067464935232149)
                    ·
                      refine ⟨2842785001409412418839007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60646080030067464935232149 2842785001409412418839007)
                      ·
                        rfl

theorem cell23_5536304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_5536304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536304 prefixEnd_5536304 := by exact prefixLift 5536304
  have htrace : WordTrace (prefixWord ++ tailWord_5536304) baseStart_5536304 baseEnd_5536304 := by
    simpa [prefixWord, tailWord_5536304, baseEnd_5536304] using wordTrace_append hprefix tailTrace_5536304
  have hstable : (prefixWord ++ tailWord_5536304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536304).length < 2 ^ (prefixWord ++ tailWord_5536304).sum := by decide
  have hdescent : baseEnd_5536304 < baseStart_5536304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536311 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 3]
def baseStart_5536311 : Nat := 118140960795 + 5536311 * 2 ^ 59
def prefixEnd_5536311 : Nat := 4983230072969 + 3 ^ 40 * 5536311 * 2
def baseEnd_5536311 : Nat := 2842788595773993891451475

theorem tailTrace_5536311 : CollatzResearch.WordTrace tailWord_5536311 prefixEnd_5536311 2842788595773993891451475 := by
  unfold tailWord_5536311
  simp only [CollatzResearch.WordTrace]
  refine ⟨201925851045898248486688787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134617234030598832324459191 201925851045898248486688787)
  ·
    refine ⟨302888776568847372730033181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201925851045898248486688787 302888776568847372730033181)
    ·
      refine ⟨113583291213317764773762443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302888776568847372730033181 113583291213317764773762443)
      ·
        refine ⟨170374936819976647160643665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113583291213317764773762443 170374936819976647160643665)
        ·
          refine ⟨127781202614982485370482749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170374936819976647160643665 127781202614982485370482749)
          ·
            refine ⟨47917950980618432013931031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127781202614982485370482749 47917950980618432013931031)
            ·
              refine ⟨71876926470927648020896547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47917950980618432013931031 71876926470927648020896547)
              ·
                refine ⟨107815389706391472031344821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71876926470927648020896547 107815389706391472031344821)
                ·
                  refine ⟨10107692784974200502938577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107815389706391472031344821 10107692784974200502938577)
                  ·
                    refine ⟨7580769588730650377203933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10107692784974200502938577 7580769588730650377203933)
                    ·
                      refine ⟨2842788595773993891451475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7580769588730650377203933 2842788595773993891451475)
                      ·
                        rfl

theorem cell23_5536311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_5536311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536311 prefixEnd_5536311 := by exact prefixLift 5536311
  have htrace : WordTrace (prefixWord ++ tailWord_5536311) baseStart_5536311 baseEnd_5536311 := by
    simpa [prefixWord, tailWord_5536311, baseEnd_5536311] using wordTrace_append hprefix tailTrace_5536311
  have hstable : (prefixWord ++ tailWord_5536311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536311).length < 2 ^ (prefixWord ++ tailWord_5536311).sum := by decide
  have hdescent : baseEnd_5536311 < baseStart_5536311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536325 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 3, 2, 2]
def baseStart_5536325 : Nat := 118140960795 + 5536325 * 2 ^ 59
def prefixEnd_5536325 : Nat := 4983230072969 + 3 ^ 40 * 5536325 * 2
def baseEnd_5536325 : Nat := 2842795784503156836676411

theorem tailTrace_5536325 : CollatzResearch.WordTrace tailWord_5536325 prefixEnd_5536325 2842795784503156836676411 := by
  unfold tailWord_5536325
  simp only [CollatzResearch.WordTrace]
  refine ⟨201926361667847528877698429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134617574445231685918465619 201926361667847528877698429)
  ·
    refine ⟨75722385625442823329136911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201926361667847528877698429 75722385625442823329136911)
    ·
      refine ⟨113583578438164234993705367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75722385625442823329136911 113583578438164234993705367)
      ·
        refine ⟨170375367657246352490558051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113583578438164234993705367 170375367657246352490558051)
        ·
          refine ⟨255563051485869528735837077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170375367657246352490558051 255563051485869528735837077)
          ·
            refine ⟨11979518038400134159492363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 255563051485869528735837077 11979518038400134159492363)
            ·
              refine ⟨17969277057600201239238545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11979518038400134159492363 17969277057600201239238545)
              ·
                refine ⟨13476957793200150929428909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17969277057600201239238545 13476957793200150929428909)
                ·
                  refine ⟨5053859172450056598535841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13476957793200150929428909 5053859172450056598535841)
                  ·
                    refine ⟨3790394379337542448901881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5053859172450056598535841 3790394379337542448901881)
                    ·
                      refine ⟨2842795784503156836676411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790394379337542448901881 2842795784503156836676411)
                      ·
                        rfl

theorem cell23_5536325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 2, 2].length) (baseStart_5536325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536325 prefixEnd_5536325 := by exact prefixLift 5536325
  have htrace : WordTrace (prefixWord ++ tailWord_5536325) baseStart_5536325 baseEnd_5536325 := by
    simpa [prefixWord, tailWord_5536325, baseEnd_5536325] using wordTrace_append hprefix tailTrace_5536325
  have hstable : (prefixWord ++ tailWord_5536325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536325).length < 2 ^ (prefixWord ++ tailWord_5536325).sum := by decide
  have hdescent : baseEnd_5536325 < baseStart_5536325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536402 : List Nat := [3, 2, 3, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_5536402 : Nat := 118140960795 + 5536402 * 2 ^ 59
def prefixEnd_5536402 : Nat := 4983230072969 + 3 ^ 40 * 5536402 * 2
def baseEnd_5536402 : Nat := 2842835322513553035413557

theorem tailTrace_5536402 : CollatzResearch.WordTrace tailWord_5536402 prefixEnd_5536402 2842835322513553035413557 := by
  unfold tailWord_5536402
  simp only [CollatzResearch.WordTrace]
  refine ⟨50482292522142142757062865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134619446725712380685500973 50482292522142142757062865)
  ·
    refine ⟨37861719391606607067797149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50482292522142142757062865 37861719391606607067797149)
    ·
      refine ⟨14198144771852477650423931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37861719391606607067797149 14198144771852477650423931)
      ·
        refine ⟨21297217157778716475635897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14198144771852477650423931 21297217157778716475635897)
        ·
          refine ⟨15972912868334037356726923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21297217157778716475635897 15972912868334037356726923)
          ·
            refine ⟨23959369302501056035090385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15972912868334037356726923 23959369302501056035090385)
            ·
              refine ⟨17969526976875792026317789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23959369302501056035090385 17969526976875792026317789)
              ·
                refine ⟨6738572616328422009869171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17969526976875792026317789 6738572616328422009869171)
                ·
                  refine ⟨10107858924492633014803757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6738572616328422009869171 10107858924492633014803757)
                  ·
                    refine ⟨3790447096684737380551409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10107858924492633014803757 3790447096684737380551409)
                    ·
                      refine ⟨2842835322513553035413557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790447096684737380551409 2842835322513553035413557)
                      ·
                        rfl

theorem cell23_5536402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_5536402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536402 prefixEnd_5536402 := by exact prefixLift 5536402
  have htrace : WordTrace (prefixWord ++ tailWord_5536402) baseStart_5536402 baseEnd_5536402 := by
    simpa [prefixWord, tailWord_5536402, baseEnd_5536402] using wordTrace_append hprefix tailTrace_5536402
  have hstable : (prefixWord ++ tailWord_5536402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536402).length < 2 ^ (prefixWord ++ tailWord_5536402).sum := by decide
  have hdescent : baseEnd_5536402 < baseStart_5536402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536449 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_5536449 : Nat := 118140960795 + 5536449 * 2 ^ 59
def prefixEnd_5536449 : Nat := 4983230072969 + 3 ^ 40 * 5536449 * 2
def baseEnd_5536449 : Nat := 2842859456104314351525841

theorem tailTrace_5536449 : CollatzResearch.WordTrace tailWord_5536449 prefixEnd_5536449 2842859456104314351525841 := by
  unfold tailWord_5536449
  simp only [CollatzResearch.WordTrace]
  refine ⟨201930884319398298055212401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134620589546265532036808267 201930884319398298055212401)
  ·
    refine ⟨151448163239548723541409301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201930884319398298055212401 151448163239548723541409301)
    ·
      refine ⟨7099132651853846416003561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 151448163239548723541409301 7099132651853846416003561)
      ·
        refine ⟨5324349488890384812002671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7099132651853846416003561 5324349488890384812002671)
        ·
          refine ⟨7986524233335577218004007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5324349488890384812002671 7986524233335577218004007)
          ·
            refine ⟨11979786350003365827006011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7986524233335577218004007 11979786350003365827006011)
            ·
              refine ⟨17969679525005048740509017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11979786350003365827006011 17969679525005048740509017)
              ·
                refine ⟨13477259643753786555381763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17969679525005048740509017 13477259643753786555381763)
                ·
                  refine ⟨20215889465630679833072645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13477259643753786555381763 20215889465630679833072645)
                  ·
                    refine ⟨3790479274805752468701121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20215889465630679833072645 3790479274805752468701121)
                    ·
                      refine ⟨2842859456104314351525841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790479274805752468701121 2842859456104314351525841)
                      ·
                        rfl

theorem cell23_5536449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_5536449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536449 prefixEnd_5536449 := by exact prefixLift 5536449
  have htrace : WordTrace (prefixWord ++ tailWord_5536449) baseStart_5536449 baseEnd_5536449 := by
    simpa [prefixWord, tailWord_5536449, baseEnd_5536449] using wordTrace_append hprefix tailTrace_5536449
  have hstable : (prefixWord ++ tailWord_5536449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536449).length < 2 ^ (prefixWord ++ tailWord_5536449).sum := by decide
  have hdescent : baseEnd_5536449 < baseStart_5536449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536472 : List Nat := [2, 1, 2, 2, 3, 4, 2, 2, 5]
def baseStart_5536472 : Nat := 118140960795 + 5536472 * 2 ^ 59
def prefixEnd_5536472 : Nat := 4983230072969 + 3 ^ 40 * 5536472 * 2
def baseEnd_5536472 : Nat := 315874585128818640170915

theorem tailTrace_5536472 : CollatzResearch.WordTrace tailWord_5536472 prefixEnd_5536472 315874585128818640170915 := by
  unfold tailWord_5536472
  simp only [CollatzResearch.WordTrace]
  refine ⟨100965861599157486491649835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134621148798876648655533113 100965861599157486491649835)
  ·
    refine ⟨151448792398736229737474753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100965861599157486491649835 151448792398736229737474753)
    ·
      refine ⟨113586594299052172303106065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151448792398736229737474753 113586594299052172303106065)
      ·
        refine ⟨85189945724289129227329549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113586594299052172303106065 85189945724289129227329549)
        ·
          refine ⟨31946229646608423460248581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85189945724289129227329549 31946229646608423460248581)
          ·
            refine ⟨5989918058739079398796609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31946229646608423460248581 5989918058739079398796609)
            ·
              refine ⟨4492438544054309549097457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5989918058739079398796609 4492438544054309549097457)
              ·
                refine ⟨3369328908040732161823093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4492438544054309549097457 3369328908040732161823093)
                ·
                  refine ⟨315874585128818640170915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3369328908040732161823093 315874585128818640170915)
                  ·
                    rfl

theorem cell23_5536472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 5].length) (baseStart_5536472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536472 prefixEnd_5536472 := by exact prefixLift 5536472
  have htrace : WordTrace (prefixWord ++ tailWord_5536472) baseStart_5536472 baseEnd_5536472 := by
    simpa [prefixWord, tailWord_5536472, baseEnd_5536472] using wordTrace_append hprefix tailTrace_5536472
  have hstable : (prefixWord ++ tailWord_5536472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536472).length < 2 ^ (prefixWord ++ tailWord_5536472).sum := by decide
  have hdescent : baseEnd_5536472 < baseStart_5536472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536511 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 8]
def baseStart_5536511 : Nat := 118140960795 + 5536511 * 2 ^ 59
def prefixEnd_5536511 : Nat := 4983230072969 + 3 ^ 40 * 5536511 * 2
def baseEnd_5536511 : Nat := 315876810211654789883395

theorem tailTrace_5536511 : CollatzResearch.WordTrace tailWord_5536511 prefixEnd_5536511 315876810211654789883395 := by
  unfold tailWord_5536511
  simp only [CollatzResearch.WordTrace]
  refine ⟨201933145645173682643969387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134622097096782455095979591 201933145645173682643969387)
  ·
    refine ⟨302899718467760523965954081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201933145645173682643969387 302899718467760523965954081)
    ·
      refine ⟨227174788850820392974465561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302899718467760523965954081 227174788850820392974465561)
      ·
        refine ⟨170381091638115294730849171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227174788850820392974465561 170381091638115294730849171)
        ·
          refine ⟨255571637457172942096273757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170381091638115294730849171 255571637457172942096273757)
          ·
            refine ⟨95839364046439853286102659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255571637457172942096273757 95839364046439853286102659)
            ·
              refine ⟨143759046069659779929153989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95839364046439853286102659 143759046069659779929153989)
              ·
                refine ⟨26954821138061208736716373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143759046069659779929153989 26954821138061208736716373)
                ·
                  refine ⟨315876810211654789883395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26954821138061208736716373 315876810211654789883395)
                  ·
                    rfl

theorem cell23_5536511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 8].length) (baseStart_5536511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536511 prefixEnd_5536511 := by exact prefixLift 5536511
  have htrace : WordTrace (prefixWord ++ tailWord_5536511) baseStart_5536511 baseEnd_5536511 := by
    simpa [prefixWord, tailWord_5536511, baseEnd_5536511] using wordTrace_append hprefix tailTrace_5536511
  have hstable : (prefixWord ++ tailWord_5536511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536511).length < 2 ^ (prefixWord ++ tailWord_5536511).sum := by decide
  have hdescent : baseEnd_5536511 < baseStart_5536511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536531 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 8]
def baseStart_5536531 : Nat := 118140960795 + 5536531 * 2 ^ 59
def prefixEnd_5536531 : Nat := 4983230072969 + 3 ^ 40 * 5536531 * 2
def baseEnd_5536531 : Nat := 2842901561517983030700463

theorem tailTrace_5536531 : CollatzResearch.WordTrace tailWord_5536531 prefixEnd_5536531 2842901561517983030700463 := by
  unfold tailWord_5536531
  simp only [CollatzResearch.WordTrace]
  refine ⟨201933875105101226059697447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134622583403400817373131631 201933875105101226059697447)
  ·
    refine ⟨302900812657651839089546171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201933875105101226059697447 302900812657651839089546171)
    ·
      refine ⟨454351218986477758634319257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302900812657651839089546171 454351218986477758634319257)
      ·
        refine ⟨340763414239858318975739443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454351218986477758634319257 340763414239858318975739443)
        ·
          refine ⟨511145121359787478463609165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340763414239858318975739443 511145121359787478463609165)
          ·
            refine ⟨191679420509920304423853437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 511145121359787478463609165 191679420509920304423853437)
            ·
              refine ⟨71879782691220114158945039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191679420509920304423853437 71879782691220114158945039)
              ·
                refine ⟨107819674036830171238417559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71879782691220114158945039 107819674036830171238417559)
                ·
                  refine ⟨161729511055245256857626339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107819674036830171238417559 161729511055245256857626339)
                  ·
                    refine ⟨242594266582867885286439509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161729511055245256857626339 242594266582867885286439509)
                    ·
                      refine ⟨2842901561517983030700463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 242594266582867885286439509 2842901561517983030700463)
                      ·
                        rfl

theorem cell23_5536531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_5536531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536531 prefixEnd_5536531 := by exact prefixLift 5536531
  have htrace : WordTrace (prefixWord ++ tailWord_5536531) baseStart_5536531 baseEnd_5536531 := by
    simpa [prefixWord, tailWord_5536531, baseEnd_5536531] using wordTrace_append hprefix tailTrace_5536531
  have hstable : (prefixWord ++ tailWord_5536531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536531).length < 2 ^ (prefixWord ++ tailWord_5536531).sum := by decide
  have hdescent : baseEnd_5536531 < baseStart_5536531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536545 : List Nat := [1, 2, 3, 2, 1, 2, 5, 1, 6]
def baseStart_5536545 : Nat := 118140960795 + 5536545 * 2 ^ 59
def prefixEnd_5536545 : Nat := 4983230072969 + 3 ^ 40 * 5536545 * 2
def baseEnd_5536545 : Nat := 315878750027460663991711

theorem tailTrace_5536545 : CollatzResearch.WordTrace tailWord_5536545 prefixEnd_5536545 315878750027460663991711 := by
  unfold tailWord_5536545
  simp only [CollatzResearch.WordTrace]
  refine ⟨201934385727050506450707089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134622923818033670967138059 201934385727050506450707089)
  ·
    refine ⟨151450789295287879838030317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201934385727050506450707089 151450789295287879838030317)
    ·
      refine ⟨56794045985732954939261369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151450789295287879838030317 56794045985732954939261369)
      ·
        refine ⟨42595534489299716204446027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56794045985732954939261369 42595534489299716204446027)
        ·
          refine ⟨63893301733949574306669041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42595534489299716204446027 63893301733949574306669041)
          ·
            refine ⟨47919976300462180730001781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63893301733949574306669041 47919976300462180730001781)
            ·
              refine ⟨4492497778168329443437667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47919976300462180730001781 4492497778168329443437667)
              ·
                refine ⟨6738746667252494165156501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4492497778168329443437667 6738746667252494165156501)
                ·
                  refine ⟨315878750027460663991711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6738746667252494165156501 315878750027460663991711)
                  ·
                    rfl

theorem cell23_5536545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 6].length) (baseStart_5536545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536545 prefixEnd_5536545 := by exact prefixLift 5536545
  have htrace : WordTrace (prefixWord ++ tailWord_5536545) baseStart_5536545 baseEnd_5536545 := by
    simpa [prefixWord, tailWord_5536545, baseEnd_5536545] using wordTrace_append hprefix tailTrace_5536545
  have hstable : (prefixWord ++ tailWord_5536545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536545).length < 2 ^ (prefixWord ++ tailWord_5536545).sum := by decide
  have hdescent : baseEnd_5536545 < baseStart_5536545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536575 : List Nat := [1, 1, 2, 2, 5, 1, 2, 3, 1, 5]
def baseStart_5536575 : Nat := 118140960795 + 5536575 * 2 ^ 59
def prefixEnd_5536575 : Nat := 4983230072969 + 3 ^ 40 * 5536575 * 2
def baseEnd_5536575 : Nat := 947641384888926952850087

theorem tailTrace_5536575 : CollatzResearch.WordTrace tailWord_5536575 prefixEnd_5536575 947641384888926952850087 := by
  unfold tailWord_5536575
  simp only [CollatzResearch.WordTrace]
  refine ⟨201935479916941821574299179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134623653277961214382866119 201935479916941821574299179)
  ·
    refine ⟨302903219875412732361448769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201935479916941821574299179 302903219875412732361448769)
    ·
      refine ⟨227177414906559549271086577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302903219875412732361448769 227177414906559549271086577)
      ·
        refine ⟨170383061179919661953314933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227177414906559549271086577 170383061179919661953314933)
        ·
          refine ⟨15973411985617468308123275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170383061179919661953314933 15973411985617468308123275)
          ·
            refine ⟨23960117978426202462184913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15973411985617468308123275 23960117978426202462184913)
            ·
              refine ⟨17970088483819651846638685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23960117978426202462184913 17970088483819651846638685)
              ·
                refine ⟨6738783181432369442489507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17970088483819651846638685 6738783181432369442489507)
                ·
                  refine ⟨10108174772148554163734261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6738783181432369442489507 10108174772148554163734261)
                  ·
                    refine ⟨947641384888926952850087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10108174772148554163734261 947641384888926952850087)
                    ·
                      rfl

theorem cell23_5536575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 5].length) (baseStart_5536575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536575 prefixEnd_5536575 := by exact prefixLift 5536575
  have htrace : WordTrace (prefixWord ++ tailWord_5536575) baseStart_5536575 baseEnd_5536575 := by
    simpa [prefixWord, tailWord_5536575, baseEnd_5536575] using wordTrace_append hprefix tailTrace_5536575
  have hstable : (prefixWord ++ tailWord_5536575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536575).length < 2 ^ (prefixWord ++ tailWord_5536575).sum := by decide
  have hdescent : baseEnd_5536575 < baseStart_5536575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536608 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 6]
def baseStart_5536608 : Nat := 118140960795 + 5536608 * 2 ^ 59
def prefixEnd_5536608 : Nat := 4983230072969 + 3 ^ 40 * 5536608 * 2
def baseEnd_5536608 : Nat := 2842941099528379229437609

theorem tailTrace_5536608 : CollatzResearch.WordTrace tailWord_5536608 prefixEnd_5536608 2842941099528379229437609 := by
  unfold tailWord_5536608
  simp only [CollatzResearch.WordTrace]
  refine ⟨100968341762911134105125239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134624455683881512140166985 100968341762911134105125239)
  ·
    refine ⟨151452512644366701157687859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100968341762911134105125239 151452512644366701157687859)
    ·
      refine ⟨227178768966550051736531789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151452512644366701157687859 227178768966550051736531789)
      ·
        refine ⟨85192038362456269401199421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227178768966550051736531789 85192038362456269401199421)
        ·
          refine ⟨31947014385921101025449783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85192038362456269401199421 31947014385921101025449783)
          ·
            refine ⟨47920521578881651538174675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31947014385921101025449783 47920521578881651538174675)
            ·
              refine ⟨71880782368322477307262013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47920521578881651538174675 71880782368322477307262013)
              ·
                refine ⟨26955293388120928990223255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71880782368322477307262013 26955293388120928990223255)
                ·
                  refine ⟨40432940082181393485334883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26955293388120928990223255 40432940082181393485334883)
                  ·
                    refine ⟨60649410123272090228002325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40432940082181393485334883 60649410123272090228002325)
                    ·
                      refine ⟨2842941099528379229437609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60649410123272090228002325 2842941099528379229437609)
                      ·
                        rfl

theorem cell23_5536608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_5536608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536608 prefixEnd_5536608 := by exact prefixLift 5536608
  have htrace : WordTrace (prefixWord ++ tailWord_5536608) baseStart_5536608 baseEnd_5536608 := by
    simpa [prefixWord, tailWord_5536608, baseEnd_5536608] using wordTrace_append hprefix tailTrace_5536608
  have hstable : (prefixWord ++ tailWord_5536608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536608).length < 2 ^ (prefixWord ++ tailWord_5536608).sum := by decide
  have hdescent : baseEnd_5536608 < baseStart_5536608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536612 : List Nat := [2, 3, 1, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_5536612 : Nat := 118140960795 + 5536612 * 2 ^ 59
def prefixEnd_5536612 : Nat := 4983230072969 + 3 ^ 40 * 5536612 * 2
def baseEnd_5536612 : Nat := 2842943153450997213787591

theorem tailTrace_5536612 : CollatzResearch.WordTrace tailWord_5536612 prefixEnd_5536612 2842943153450997213787591 := by
  unfold tailWord_5536612
  simp only [CollatzResearch.WordTrace]
  refine ⟨100968414708903888446698045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134624552945205184595597393 100968414708903888446698045)
  ·
    refine ⟨37863155515838958167511767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100968414708903888446698045 37863155515838958167511767)
    ·
      refine ⟨56794733273758437251267651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37863155515838958167511767 56794733273758437251267651)
      ·
        refine ⟨85192099910637655876901477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56794733273758437251267651 85192099910637655876901477)
        ·
          refine ⟨15973518733244560476919027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85192099910637655876901477 15973518733244560476919027)
          ·
            refine ⟨23960278099866840715378541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15973518733244560476919027 23960278099866840715378541)
            ·
              refine ⟨8985104287450065268266953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23960278099866840715378541 8985104287450065268266953)
              ·
                refine ⟨6738828215587548951200215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8985104287450065268266953 6738828215587548951200215)
                ·
                  refine ⟨10108242323381323426800323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6738828215587548951200215 10108242323381323426800323)
                  ·
                    refine ⟨15162363485071985140200485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10108242323381323426800323 15162363485071985140200485)
                    ·
                      refine ⟨2842943153450997213787591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15162363485071985140200485 2842943153450997213787591)
                      ·
                        rfl

theorem cell23_5536612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_5536612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536612 prefixEnd_5536612 := by exact prefixLift 5536612
  have htrace : WordTrace (prefixWord ++ tailWord_5536612) baseStart_5536612 baseEnd_5536612 := by
    simpa [prefixWord, tailWord_5536612, baseEnd_5536612] using wordTrace_append hprefix tailTrace_5536612
  have hstable : (prefixWord ++ tailWord_5536612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536612).length < 2 ^ (prefixWord ++ tailWord_5536612).sum := by decide
  have hdescent : baseEnd_5536612 < baseStart_5536612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536622 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_5536622 : Nat := 118140960795 + 5536622 * 2 ^ 59
def prefixEnd_5536622 : Nat := 4983230072969 + 3 ^ 40 * 5536622 * 2
def baseEnd_5536622 : Nat := 947649429419180724887515

theorem tailTrace_5536622 : CollatzResearch.WordTrace tailWord_5536622 prefixEnd_5536622 947649429419180724887515 := by
  unfold tailWord_5536622
  simp only [CollatzResearch.WordTrace]
  refine ⟨25242149268471443575157515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134624796098514365734173413 25242149268471443575157515)
  ·
    refine ⟨37863223902707165362736273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25242149268471443575157515 37863223902707165362736273)
    ·
      refine ⟨28397417927030374022052205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37863223902707165362736273 28397417927030374022052205)
      ·
        refine ⟨10649031722636390258269577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28397417927030374022052205 10649031722636390258269577)
        ·
          refine ⟨7986773791977292693702183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10649031722636390258269577 7986773791977292693702183)
          ·
            refine ⟨11980160687965939040553275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7986773791977292693702183 11980160687965939040553275)
            ·
              refine ⟨17970241031948908560829913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11980160687965939040553275 17970241031948908560829913)
              ·
                refine ⟨13477680773961681420622435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17970241031948908560829913 13477680773961681420622435)
                ·
                  refine ⟨20216521160942522130933653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13477680773961681420622435 20216521160942522130933653)
                  ·
                    refine ⟨947649429419180724887515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20216521160942522130933653 947649429419180724887515)
                    ·
                      rfl

theorem cell23_5536622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_5536622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536622 prefixEnd_5536622 := by exact prefixLift 5536622
  have htrace : WordTrace (prefixWord ++ tailWord_5536622) baseStart_5536622 baseEnd_5536622 := by
    simpa [prefixWord, tailWord_5536622, baseEnd_5536622] using wordTrace_append hprefix tailTrace_5536622
  have hstable : (prefixWord ++ tailWord_5536622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536622).length < 2 ^ (prefixWord ++ tailWord_5536622).sum := by decide
  have hdescent : baseEnd_5536622 < baseStart_5536622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536625 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_5536625 : Nat := 118140960795 + 5536625 * 2 ^ 59
def prefixEnd_5536625 : Nat := 4983230072969 + 3 ^ 40 * 5536625 * 2
def baseEnd_5536625 : Nat := 2842949828699505662925031

theorem tailTrace_5536625 : CollatzResearch.WordTrace tailWord_5536625 prefixEnd_5536625 2842949828699505662925031 := by
  unfold tailWord_5536625
  simp only [CollatzResearch.WordTrace]
  refine ⟨201937303566760680113619329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134624869044507120075746219 201937303566760680113619329)
  ·
    refine ⟨151452977675070510085214497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201937303566760680113619329 151452977675070510085214497)
    ·
      refine ⟨113589733256302882563910873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151452977675070510085214497 113589733256302882563910873)
      ·
        refine ⟨85192299942227161922933155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113589733256302882563910873 85192299942227161922933155)
        ·
          refine ⟨127788449913340742884399733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85192299942227161922933155 127788449913340742884399733)
          ·
            refine ⟨11980167179375694645412475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127788449913340742884399733 11980167179375694645412475)
            ·
              refine ⟨17970250769063541968118713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11980167179375694645412475 17970250769063541968118713)
              ·
                refine ⟨13477688076797656476089035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17970250769063541968118713 13477688076797656476089035)
                ·
                  refine ⟨20216532115196484714133553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13477688076797656476089035 20216532115196484714133553)
                  ·
                    refine ⟨15162399086397363535600165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20216532115196484714133553 15162399086397363535600165)
                    ·
                      refine ⟨2842949828699505662925031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15162399086397363535600165 2842949828699505662925031)
                      ·
                        rfl

theorem cell23_5536625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_5536625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536625 prefixEnd_5536625 := by exact prefixLift 5536625
  have htrace : WordTrace (prefixWord ++ tailWord_5536625) baseStart_5536625 baseEnd_5536625 := by
    simpa [prefixWord, tailWord_5536625, baseEnd_5536625] using wordTrace_append hprefix tailTrace_5536625
  have hstable : (prefixWord ++ tailWord_5536625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536625).length < 2 ^ (prefixWord ++ tailWord_5536625).sum := by decide
  have hdescent : baseEnd_5536625 < baseStart_5536625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536629 : List Nat := [1, 3, 4, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_5536629 : Nat := 118140960795 + 5536629 * 2 ^ 59
def prefixEnd_5536629 : Nat := 4983230072969 + 3 ^ 40 * 5536629 * 2
def baseEnd_5536629 : Nat := 2842951882622123647275013

theorem tailTrace_5536629 : CollatzResearch.WordTrace tailWord_5536629 prefixEnd_5536629 2842951882622123647275013 := by
  unfold tailWord_5536629
  simp only [CollatzResearch.WordTrace]
  refine ⟨201937449458746188796764941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134624966305830792531176627 201937449458746188796764941)
  ·
    refine ⟨75726543547029820798786853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201937449458746188796764941 75726543547029820798786853)
    ·
      refine ⟨14198726915068091399772535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75726543547029820798786853 14198726915068091399772535)
      ·
        refine ⟨21298090372602137099658803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14198726915068091399772535 21298090372602137099658803)
        ·
          refine ⟨31947135558903205649488205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21298090372602137099658803 31947135558903205649488205)
          ·
            refine ⟨11980175834588702118558077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31947135558903205649488205 11980175834588702118558077)
            ·
              refine ⟨4492565937970763294459279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11980175834588702118558077 4492565937970763294459279)
              ·
                refine ⟨6738848906956144941688919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4492565937970763294459279 6738848906956144941688919)
                ·
                  refine ⟨10108273360434217412533379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6738848906956144941688919 10108273360434217412533379)
                  ·
                    refine ⟨15162410040651326118800069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10108273360434217412533379 15162410040651326118800069)
                    ·
                      refine ⟨2842951882622123647275013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15162410040651326118800069 2842951882622123647275013)
                      ·
                        rfl

theorem cell23_5536629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_5536629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536629 prefixEnd_5536629 := by exact prefixLift 5536629
  have htrace : WordTrace (prefixWord ++ tailWord_5536629) baseStart_5536629 baseEnd_5536629 := by
    simpa [prefixWord, tailWord_5536629, baseEnd_5536629] using wordTrace_append hprefix tailTrace_5536629
  have hstable : (prefixWord ++ tailWord_5536629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536629).length < 2 ^ (prefixWord ++ tailWord_5536629).sum := by decide
  have hdescent : baseEnd_5536629 < baseStart_5536629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536672 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 3, 3, 2]
def baseStart_5536672 : Nat := 118140960795 + 5536672 * 2 ^ 59
def prefixEnd_5536672 : Nat := 4983230072969 + 3 ^ 40 * 5536672 * 2
def baseEnd_5536672 : Nat := 2842973962290266979037315

theorem tailTrace_5536672 : CollatzResearch.WordTrace tailWord_5536672 prefixEnd_5536672 2842973962290266979037315 := by
  unfold tailWord_5536672
  simp only [CollatzResearch.WordTrace]
  refine ⟨100969508898795203570290135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134626011865060271427053513 100969508898795203570290135)
  ·
    refine ⟨151454263348192805355435203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100969508898795203570290135 151454263348192805355435203)
    ·
      refine ⟨227181395022289208033152805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151454263348192805355435203 227181395022289208033152805)
      ·
        refine ⟨42596511566679226506216151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227181395022289208033152805 42596511566679226506216151)
        ·
          refine ⟨63894767350018839759324227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42596511566679226506216151 63894767350018839759324227)
          ·
            refine ⟨95842151025028259638986341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63894767350018839759324227 95842151025028259638986341)
            ·
              refine ⟨17970403317192798682309939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95842151025028259638986341 17970403317192798682309939)
              ·
                refine ⟨26955604975789198023464909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17970403317192798682309939 26955604975789198023464909)
                ·
                  refine ⟨10108351865920949258799341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26955604975789198023464909 10108351865920949258799341)
                  ·
                    refine ⟨3790631949720355972049753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10108351865920949258799341 3790631949720355972049753)
                    ·
                      refine ⟨2842973962290266979037315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790631949720355972049753 2842973962290266979037315)
                      ·
                        rfl

theorem cell23_5536672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_5536672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536672 prefixEnd_5536672 := by exact prefixLift 5536672
  have htrace : WordTrace (prefixWord ++ tailWord_5536672) baseStart_5536672 baseEnd_5536672 := by
    simpa [prefixWord, tailWord_5536672, baseEnd_5536672] using wordTrace_append hprefix tailTrace_5536672
  have hstable : (prefixWord ++ tailWord_5536672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536672).length < 2 ^ (prefixWord ++ tailWord_5536672).sum := by decide
  have hdescent : baseEnd_5536672 < baseStart_5536672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536710 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_5536710 : Nat := 118140960795 + 5536710 * 2 ^ 59
def prefixEnd_5536710 : Nat := 4983230072969 + 3 ^ 40 * 5536710 * 2
def baseEnd_5536710 : Nat := 2842993474555137830362141

theorem tailTrace_5536710 : CollatzResearch.WordTrace tailWord_5536710 prefixEnd_5536710 2842993474555137830362141 := by
  unfold tailWord_5536710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6310637617857898113451987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 134626935847635159753642389 6310637617857898113451987)
  ·
    refine ⟨9465956426786847170177981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6310637617857898113451987 9465956426786847170177981)
    ·
      refine ⟨3549733660045067688816743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9465956426786847170177981 3549733660045067688816743)
      ·
        refine ⟨5324600490067601533225115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3549733660045067688816743 5324600490067601533225115)
        ·
          refine ⟨7986900735101402299837673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5324600490067601533225115 7986900735101402299837673)
          ·
            refine ⟨5990175551326051724878255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7986900735101402299837673 5990175551326051724878255)
            ·
              refine ⟨8985263326989077587317383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5990175551326051724878255 8985263326989077587317383)
              ·
                refine ⟨13477894990483616380976075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8985263326989077587317383 13477894990483616380976075)
                ·
                  refine ⟨20216842485725424571464113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13477894990483616380976075 20216842485725424571464113)
                  ·
                    refine ⟨15162631864294068428598085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20216842485725424571464113 15162631864294068428598085)
                    ·
                      refine ⟨2842993474555137830362141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15162631864294068428598085 2842993474555137830362141)
                      ·
                        rfl

theorem cell23_5536710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_5536710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536710 prefixEnd_5536710 := by exact prefixLift 5536710
  have htrace : WordTrace (prefixWord ++ tailWord_5536710) baseStart_5536710 baseEnd_5536710 := by
    simpa [prefixWord, tailWord_5536710, baseEnd_5536710] using wordTrace_append hprefix tailTrace_5536710
  have hstable : (prefixWord ++ tailWord_5536710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536710).length < 2 ^ (prefixWord ++ tailWord_5536710).sum := by decide
  have hdescent : baseEnd_5536710 < baseStart_5536710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536715 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 4]
def baseStart_5536715 : Nat := 118140960795 + 5536715 * 2 ^ 59
def prefixEnd_5536715 : Nat := 4983230072969 + 3 ^ 40 * 5536715 * 2
def baseEnd_5536715 : Nat := 2842996041958410310799617

theorem tailTrace_5536715 : CollatzResearch.WordTrace tailWord_5536715 prefixEnd_5536715 2842996041958410310799617 := by
  unfold tailWord_5536715
  simp only [CollatzResearch.WordTrace]
  refine ⟨201940586136434625484395599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134627057424289750322930399 201940586136434625484395599)
  ·
    refine ⟨302910879204651938226593399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201940586136434625484395599 302910879204651938226593399)
    ·
      refine ⟨454366318806977907339890099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302910879204651938226593399 454366318806977907339890099)
      ·
        refine ⟨681549478210466861009835149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454366318806977907339890099 681549478210466861009835149)
        ·
          refine ⟨255581054328925072878688181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 681549478210466861009835149 255581054328925072878688181)
          ·
            refine ⟨23960723843336725582377017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 255581054328925072878688181 23960723843336725582377017)
            ·
              refine ⟨17970542882502544186782763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23960723843336725582377017 17970542882502544186782763)
              ·
                refine ⟨26955814323753816280174145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17970542882502544186782763 26955814323753816280174145)
                ·
                  refine ⟨20216860742815362210130609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26955814323753816280174145 20216860742815362210130609)
                  ·
                    refine ⟨15162645557111521657597957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20216860742815362210130609 15162645557111521657597957)
                    ·
                      refine ⟨2842996041958410310799617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15162645557111521657597957 2842996041958410310799617)
                      ·
                        rfl

theorem cell23_5536715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 4].length) (baseStart_5536715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536715 prefixEnd_5536715 := by exact prefixLift 5536715
  have htrace : WordTrace (prefixWord ++ tailWord_5536715) baseStart_5536715 baseEnd_5536715 := by
    simpa [prefixWord, tailWord_5536715, baseEnd_5536715] using wordTrace_append hprefix tailTrace_5536715
  have hstable : (prefixWord ++ tailWord_5536715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536715).length < 2 ^ (prefixWord ++ tailWord_5536715).sum := by decide
  have hdescent : baseEnd_5536715 < baseStart_5536715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536719 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 1, 4, 2]
def baseStart_5536719 : Nat := 118140960795 + 5536719 * 2 ^ 59
def prefixEnd_5536719 : Nat := 4983230072969 + 3 ^ 40 * 5536719 * 2
def baseEnd_5536719 : Nat := 2842998095881028295149599

theorem tailTrace_5536719 : CollatzResearch.WordTrace tailWord_5536719 prefixEnd_5536719 2842998095881028295149599 := by
  unfold tailWord_5536719
  simp only [CollatzResearch.WordTrace]
  refine ⟨201940732028420134167541211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134627154685613422778360807 201940732028420134167541211)
  ·
    refine ⟨302911098042630201251311817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201940732028420134167541211 302911098042630201251311817)
    ·
      refine ⟨227183323531972650938483863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302911098042630201251311817 227183323531972650938483863)
      ·
        refine ⟨340774985297958976407725795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227183323531972650938483863 340774985297958976407725795)
        ·
          refine ⟨511162477946938464611588693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340774985297958976407725795 511162477946938464611588693)
          ·
            refine ⟨5990185288440685132167055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 511162477946938464611588693 5990185288440685132167055)
            ·
              refine ⟨8985277932661027698250583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5990185288440685132167055 8985277932661027698250583)
              ·
                refine ⟨13477916898991541547375875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8985277932661027698250583 13477916898991541547375875)
                ·
                  refine ⟨20216875348487312321063813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13477916898991541547375875 20216875348487312321063813)
                  ·
                    refine ⟨3790664127841371060199465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20216875348487312321063813 3790664127841371060199465)
                    ·
                      refine ⟨2842998095881028295149599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790664127841371060199465 2842998095881028295149599)
                      ·
                        rfl

theorem cell23_5536719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 4, 2].length) (baseStart_5536719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536719 prefixEnd_5536719 := by exact prefixLift 5536719
  have htrace : WordTrace (prefixWord ++ tailWord_5536719) baseStart_5536719 baseEnd_5536719 := by
    simpa [prefixWord, tailWord_5536719, baseEnd_5536719] using wordTrace_append hprefix tailTrace_5536719
  have hstable : (prefixWord ++ tailWord_5536719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536719).length < 2 ^ (prefixWord ++ tailWord_5536719).sum := by decide
  have hdescent : baseEnd_5536719 < baseStart_5536719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536770 : List Nat := [3, 4, 1, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_5536770 : Nat := 118140960795 + 5536770 * 2 ^ 59
def prefixEnd_5536770 : Nat := 4983230072969 + 3 ^ 40 * 5536770 * 2
def baseEnd_5536770 : Nat := 2843024283394407595611865

theorem tailTrace_5536770 : CollatzResearch.WordTrace tailWord_5536770 prefixEnd_5536770 2843024283394407595611865 := by
  unfold tailWord_5536770
  simp only [CollatzResearch.WordTrace]
  refine ⟨50485648037808842469411941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134628394767490246585098509 50485648037808842469411941)
  ·
    refine ⟨9466059007089157963014739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50485648037808842469411941 9466059007089157963014739)
    ·
      refine ⟨14199088510633736944522109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9466059007089157963014739 14199088510633736944522109)
      ·
        refine ⟨5324658191487651354195791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14199088510633736944522109 5324658191487651354195791)
        ·
          refine ⟨7986987287231477031293687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5324658191487651354195791 7986987287231477031293687)
          ·
            refine ⟨11980480930847215546940531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7986987287231477031293687 11980480930847215546940531)
            ·
              refine ⟨17970721396270823320410797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11980480930847215546940531 17970721396270823320410797)
              ·
                refine ⟨6739020523601558745154049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17970721396270823320410797 6739020523601558745154049)
                ·
                  refine ⟨5054265392701169058865537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6739020523601558745154049 5054265392701169058865537)
                  ·
                    refine ⟨3790699044525876794149153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5054265392701169058865537 3790699044525876794149153)
                    ·
                      refine ⟨2843024283394407595611865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790699044525876794149153 2843024283394407595611865)
                      ·
                        rfl

theorem cell23_5536770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_5536770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536770 prefixEnd_5536770 := by exact prefixLift 5536770
  have htrace : WordTrace (prefixWord ++ tailWord_5536770) baseStart_5536770 baseEnd_5536770 := by
    simpa [prefixWord, tailWord_5536770, baseEnd_5536770] using wordTrace_append hprefix tailTrace_5536770
  have hstable : (prefixWord ++ tailWord_5536770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536770).length < 2 ^ (prefixWord ++ tailWord_5536770).sum := by decide
  have hdescent : baseEnd_5536770 < baseStart_5536770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536792 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_5536792 : Nat := 118140960795 + 5536792 * 2 ^ 59
def prefixEnd_5536792 : Nat := 4983230072969 + 3 ^ 40 * 5536792 * 2
def baseEnd_5536792 : Nat := 2843035579968806509536763

theorem tailTrace_5536792 : CollatzResearch.WordTrace tailWord_5536792 prefixEnd_5536792 2843035579968806509536763 := by
  unfold tailWord_5536792
  simp only [CollatzResearch.WordTrace]
  refine ⟨100971697278577833817474315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134628929704770445089965753 100971697278577833817474315)
  ·
    refine ⟨151457545917866750726211473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100971697278577833817474315 151457545917866750726211473)
    ·
      refine ⟨113593159438400063044658605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151457545917866750726211473 113593159438400063044658605)
      ·
        refine ⟨42597434789400023641746977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113593159438400063044658605 42597434789400023641746977)
        ·
          refine ⟨31948076092050017731310233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42597434789400023641746977 31948076092050017731310233)
          ·
            refine ⟨23961057069037513298482675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31948076092050017731310233 23961057069037513298482675)
            ·
              refine ⟨35941585603556269947724013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23961057069037513298482675 35941585603556269947724013)
              ·
                refine ⟨13478094601333601230396505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35941585603556269947724013 13478094601333601230396505)
                ·
                  refine ⟨10108570951000200922797379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13478094601333601230396505 10108570951000200922797379)
                  ·
                    refine ⟨15162856426500301384196069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10108570951000200922797379 15162856426500301384196069)
                    ·
                      refine ⟨2843035579968806509536763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15162856426500301384196069 2843035579968806509536763)
                      ·
                        rfl

theorem cell23_5536792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_5536792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536792 prefixEnd_5536792 := by exact prefixLift 5536792
  have htrace : WordTrace (prefixWord ++ tailWord_5536792) baseStart_5536792 baseEnd_5536792 := by
    simpa [prefixWord, tailWord_5536792, baseEnd_5536792] using wordTrace_append hprefix tailTrace_5536792
  have hstable : (prefixWord ++ tailWord_5536792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536792).length < 2 ^ (prefixWord ++ tailWord_5536792).sum := by decide
  have hdescent : baseEnd_5536792 < baseStart_5536792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536795 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 3]
def baseStart_5536795 : Nat := 118140960795 + 5536795 * 2 ^ 59
def prefixEnd_5536795 : Nat := 4983230072969 + 3 ^ 40 * 5536795 * 2
def baseEnd_5536795 : Nat := 2843037120410769997799249

theorem tailTrace_5536795 : CollatzResearch.WordTrace tailWord_5536795 prefixEnd_5536795 2843037120410769997799249 := by
  unfold tailWord_5536795
  simp only [CollatzResearch.WordTrace]
  refine ⟨201943503976144799147307839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134629002650763199431538559 201943503976144799147307839)
  ·
    refine ⟨302915255964217198720961759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201943503976144799147307839 302915255964217198720961759)
    ·
      refine ⟨454372883946325798081442639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302915255964217198720961759 454372883946325798081442639)
      ·
        refine ⟨681559325919488697122163959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454372883946325798081442639 681559325919488697122163959)
        ·
          refine ⟨1022338988879233045683245939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681559325919488697122163959 1022338988879233045683245939)
          ·
            refine ⟨1533508483318849568524868909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022338988879233045683245939 1533508483318849568524868909)
            ·
              refine ⟨575065681244568588196825841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1533508483318849568524868909 575065681244568588196825841)
              ·
                refine ⟨431299260933426441147619381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575065681244568588196825841 431299260933426441147619381)
                ·
                  refine ⟨40434305712508728857589317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 431299260933426441147619381 40434305712508728857589317)
                  ·
                    refine ⟨7581432321095386660797997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40434305712508728857589317 7581432321095386660797997)
                    ·
                      refine ⟨2843037120410769997799249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7581432321095386660797997 2843037120410769997799249)
                      ·
                        rfl

theorem cell23_5536795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 3].length) (baseStart_5536795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536795 prefixEnd_5536795 := by exact prefixLift 5536795
  have htrace : WordTrace (prefixWord ++ tailWord_5536795) baseStart_5536795 baseEnd_5536795 := by
    simpa [prefixWord, tailWord_5536795, baseEnd_5536795] using wordTrace_append hprefix tailTrace_5536795
  have hstable : (prefixWord ++ tailWord_5536795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536795).length < 2 ^ (prefixWord ++ tailWord_5536795).sum := by decide
  have hdescent : baseEnd_5536795 < baseStart_5536795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536805 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_5536805 : Nat := 118140960795 + 5536805 * 2 ^ 59
def prefixEnd_5536805 : Nat := 4983230072969 + 3 ^ 40 * 5536805 * 2
def baseEnd_5536805 : Nat := 2843042255217314958674203

theorem tailTrace_5536805 : CollatzResearch.WordTrace tailWord_5536805 prefixEnd_5536805 2843042255217314958674203 := by
  unfold tailWord_5536805
  simp only [CollatzResearch.WordTrace]
  refine ⟨201943868706108570855171869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134629245804072380570114579 201943868706108570855171869)
  ·
    refine ⟨75728950764790714070689451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201943868706108570855171869 75728950764790714070689451)
    ·
      refine ⟨113593426147186071106034177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75728950764790714070689451 113593426147186071106034177)
      ·
        refine ⟨85195069610389553329525633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113593426147186071106034177 85195069610389553329525633)
        ·
          refine ⟨63896302207792164997144225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85195069610389553329525633 63896302207792164997144225)
          ·
            refine ⟨47922226655844123747858169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63896302207792164997144225 47922226655844123747858169)
            ·
              refine ⟨35941669991883092810893627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47922226655844123747858169 35941669991883092810893627)
              ·
                refine ⟨53912504987824639216340441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35941669991883092810893627 53912504987824639216340441)
                ·
                  refine ⟨40434378740868479412255331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53912504987824639216340441 40434378740868479412255331)
                  ·
                    refine ⟨60651568111302719118382997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40434378740868479412255331 60651568111302719118382997)
                    ·
                      refine ⟨2843042255217314958674203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60651568111302719118382997 2843042255217314958674203)
                      ·
                        rfl

theorem cell23_5536805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_5536805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536805 prefixEnd_5536805 := by exact prefixLift 5536805
  have htrace : WordTrace (prefixWord ++ tailWord_5536805) baseStart_5536805 baseEnd_5536805 := by
    simpa [prefixWord, tailWord_5536805, baseEnd_5536805] using wordTrace_append hprefix tailTrace_5536805
  have hstable : (prefixWord ++ tailWord_5536805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536805).length < 2 ^ (prefixWord ++ tailWord_5536805).sum := by decide
  have hdescent : baseEnd_5536805 < baseStart_5536805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536812 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 3]
def baseStart_5536812 : Nat := 118140960795 + 5536812 * 2 ^ 59
def prefixEnd_5536812 : Nat := 4983230072969 + 3 ^ 40 * 5536812 * 2
def baseEnd_5536812 : Nat := 2843045849581896431286671

theorem tailTrace_5536812 : CollatzResearch.WordTrace tailWord_5536812 prefixEnd_5536812 2843045849581896431286671 := by
  unfold tailWord_5536812
  simp only [CollatzResearch.WordTrace]
  refine ⟨100972062008541605525338345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134629416011388807367117793 100972062008541605525338345)
  ·
    refine ⟨75729046506406204144003759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100972062008541605525338345 75729046506406204144003759)
    ·
      refine ⟨113593569759609306216005639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75729046506406204144003759 113593569759609306216005639)
      ·
        refine ⟨170390354639413959324008459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113593569759609306216005639 170390354639413959324008459)
        ·
          refine ⟨255585531959120938986012689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170390354639413959324008459 255585531959120938986012689)
          ·
            refine ⟨191689148969340704239509517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255585531959120938986012689 191689148969340704239509517)
            ·
              refine ⟨71883430863502764089816069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191689148969340704239509517 71883430863502764089816069)
              ·
                refine ⟨13478143286906768266840513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71883430863502764089816069 13478143286906768266840513)
                ·
                  refine ⟨10108607465180076200130385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13478143286906768266840513 10108607465180076200130385)
                  ·
                    refine ⟨7581455598885057150097789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10108607465180076200130385 7581455598885057150097789)
                    ·
                      refine ⟨2843045849581896431286671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7581455598885057150097789 2843045849581896431286671)
                      ·
                        rfl

theorem cell23_5536812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_5536812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536812 prefixEnd_5536812 := by exact prefixLift 5536812
  have htrace : WordTrace (prefixWord ++ tailWord_5536812) baseStart_5536812 baseEnd_5536812 := by
    simpa [prefixWord, tailWord_5536812, baseEnd_5536812] using wordTrace_append hprefix tailTrace_5536812
  have hstable : (prefixWord ++ tailWord_5536812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536812).length < 2 ^ (prefixWord ++ tailWord_5536812).sum := by decide
  have hdescent : baseEnd_5536812 < baseStart_5536812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536855 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_5536855 : Nat := 118140960795 + 5536855 * 2 ^ 59
def prefixEnd_5536855 : Nat := 4983230072969 + 3 ^ 40 * 5536855 * 2
def baseEnd_5536855 : Nat := 2843067929250039763048973

theorem tailTrace_5536855 : CollatzResearch.WordTrace tailWord_5536855 prefixEnd_5536855 2843067929250039763048973 := by
  unfold tailWord_5536855
  simp only [CollatzResearch.WordTrace]
  refine ⟨201945692355927429394492019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134630461570618286262994679 201945692355927429394492019)
  ·
    refine ⟨302918538533891144091738029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201945692355927429394492019 302918538533891144091738029)
    ·
      refine ⟨113594451950209179034401761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302918538533891144091738029 113594451950209179034401761)
      ·
        refine ⟨85195838962656884275801321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113594451950209179034401761 85195838962656884275801321)
        ·
          refine ⟨63896879221992663206850991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85195838962656884275801321 63896879221992663206850991)
          ·
            refine ⟨95845318832988994810276487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63896879221992663206850991 95845318832988994810276487)
            ·
              refine ⟨143767978249483492215414731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95845318832988994810276487 143767978249483492215414731)
              ·
                refine ⟨215651967374225238323122097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143767978249483492215414731 215651967374225238323122097)
                ·
                  refine ⟨161738975530668928742341573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215651967374225238323122097 161738975530668928742341573)
                  ·
                    refine ⟨30326057912000424139189045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 161738975530668928742341573 30326057912000424139189045)
                    ·
                      refine ⟨2843067929250039763048973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30326057912000424139189045 2843067929250039763048973)
                      ·
                        rfl

theorem cell23_5536855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_5536855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536855 prefixEnd_5536855 := by exact prefixLift 5536855
  have htrace : WordTrace (prefixWord ++ tailWord_5536855) baseStart_5536855 baseEnd_5536855 := by
    simpa [prefixWord, tailWord_5536855, baseEnd_5536855] using wordTrace_append hprefix tailTrace_5536855
  have hstable : (prefixWord ++ tailWord_5536855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536855).length < 2 ^ (prefixWord ++ tailWord_5536855).sum := by decide
  have hdescent : baseEnd_5536855 < baseStart_5536855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536866 : List Nat := [3, 3, 2, 2, 1, 3, 1, 2, 6]
def baseStart_5536866 : Nat := 118140960795 + 5536866 * 2 ^ 59
def prefixEnd_5536866 : Nat := 4983230072969 + 3 ^ 40 * 5536866 * 2
def baseEnd_5536866 : Nat := 315897064170804357779047

theorem tailTrace_5536866 : CollatzResearch.WordTrace tailWord_5536866 prefixEnd_5536866 315897064170804357779047 := by
  unfold tailWord_5536866
  simp only [CollatzResearch.WordTrace]
  refine ⟨50486523389721894568285613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134630729039258385515428301 50486523389721894568285613)
  ·
    refine ⟨18932446271145710463107105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50486523389721894568285613 18932446271145710463107105)
    ·
      refine ⟨14199334703359282847330329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18932446271145710463107105 14199334703359282847330329)
      ·
        refine ⟨10649501027519462135497747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14199334703359282847330329 10649501027519462135497747)
        ·
          refine ⟨15974251541279193203246621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10649501027519462135497747 15974251541279193203246621)
          ·
            refine ⟨5990344327979697451217483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15974251541279193203246621 5990344327979697451217483)
            ·
              refine ⟨8985516491969546176826225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5990344327979697451217483 8985516491969546176826225)
              ·
                refine ⟨6739137368977159632619669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8985516491969546176826225 6739137368977159632619669)
                ·
                  refine ⟨315897064170804357779047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6739137368977159632619669 315897064170804357779047)
                  ·
                    rfl

theorem cell23_5536866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_5536866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536866 prefixEnd_5536866 := by exact prefixLift 5536866
  have htrace : WordTrace (prefixWord ++ tailWord_5536866) baseStart_5536866 baseEnd_5536866 := by
    simpa [prefixWord, tailWord_5536866, baseEnd_5536866] using wordTrace_append hprefix tailTrace_5536866
  have hstable : (prefixWord ++ tailWord_5536866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536866).length < 2 ^ (prefixWord ++ tailWord_5536866).sum := by decide
  have hdescent : baseEnd_5536866 < baseStart_5536866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536869 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 4, 3, 2]
def baseStart_5536869 : Nat := 118140960795 + 5536869 * 2 ^ 59
def prefixEnd_5536869 : Nat := 4983230072969 + 3 ^ 40 * 5536869 * 2
def baseEnd_5536869 : Nat := 2843075117979202708273909

theorem tailTrace_5536869 : CollatzResearch.WordTrace tailWord_5536869 prefixEnd_5536869 2843075117979202708273909 := by
  unfold tailWord_5536869
  simp only [CollatzResearch.WordTrace]
  refine ⟨201946202977876709785501661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134630801985251139857001107 201946202977876709785501661)
  ·
    refine ⟨75729826116703766169563123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201946202977876709785501661 75729826116703766169563123)
    ·
      refine ⟨113594739175055649254344685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75729826116703766169563123 113594739175055649254344685)
      ·
        refine ⟨42598027190645868470379257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113594739175055649254344685 42598027190645868470379257)
        ·
          refine ⟨31948520392984401352784443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42598027190645868470379257 31948520392984401352784443)
          ·
            refine ⟨47922780589476602029176665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31948520392984401352784443 47922780589476602029176665)
            ·
              refine ⟨35942085442107451521882499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47922780589476602029176665 35942085442107451521882499)
              ·
                refine ⟨53913128163161177282823749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35942085442107451521882499 53913128163161177282823749)
                ·
                  refine ⟨10108711530592720740529453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53913128163161177282823749 10108711530592720740529453)
                  ·
                    refine ⟨3790766823972270277698545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10108711530592720740529453 3790766823972270277698545)
                    ·
                      refine ⟨2843075117979202708273909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790766823972270277698545 2843075117979202708273909)
                      ·
                        rfl

theorem cell23_5536869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_5536869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536869 prefixEnd_5536869 := by exact prefixLift 5536869
  have htrace : WordTrace (prefixWord ++ tailWord_5536869) baseStart_5536869 baseEnd_5536869 := by
    simpa [prefixWord, tailWord_5536869, baseEnd_5536869] using wordTrace_append hprefix tailTrace_5536869
  have hstable : (prefixWord ++ tailWord_5536869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536869).length < 2 ^ (prefixWord ++ tailWord_5536869).sum := by decide
  have hdescent : baseEnd_5536869 < baseStart_5536869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536876 : List Nat := [2, 2, 1, 1, 3, 2, 1, 6, 1, 1, 3]
def baseStart_5536876 : Nat := 118140960795 + 5536876 * 2 ^ 59
def prefixEnd_5536876 : Nat := 4983230072969 + 3 ^ 40 * 5536876 * 2
def baseEnd_5536876 : Nat := 2843078712343784180886377

theorem tailTrace_5536876 : CollatzResearch.WordTrace tailWord_5536876 prefixEnd_5536876 2843078712343784180886377 := by
  unfold tailWord_5536876
  simp only [CollatzResearch.WordTrace]
  refine ⟨100973229144425674990503241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134630972192567566654004321 100973229144425674990503241)
  ·
    refine ⟨75729921858319256242877431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100973229144425674990503241 75729921858319256242877431)
    ·
      refine ⟨113594882787478884364316147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75729921858319256242877431 113594882787478884364316147)
      ·
        refine ⟨170392324181218326546474221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113594882787478884364316147 170392324181218326546474221)
        ·
          refine ⟨63897121567956872454927833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170392324181218326546474221 63897121567956872454927833)
          ·
            refine ⟨47922841175967654341195875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63897121567956872454927833 47922841175967654341195875)
            ·
              refine ⟨71884261763951481511793813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47922841175967654341195875 71884261763951481511793813)
              ·
                refine ⟨3369574770185225695865335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71884261763951481511793813 3369574770185225695865335)
                ·
                  refine ⟨5054362155277838543798003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3369574770185225695865335 5054362155277838543798003)
                  ·
                    refine ⟨7581543232916757815697005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5054362155277838543798003 7581543232916757815697005)
                    ·
                      refine ⟨2843078712343784180886377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7581543232916757815697005 2843078712343784180886377)
                      ·
                        rfl

theorem cell23_5536876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 1, 1, 3].length) (baseStart_5536876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536876 prefixEnd_5536876 := by exact prefixLift 5536876
  have htrace : WordTrace (prefixWord ++ tailWord_5536876) baseStart_5536876 baseEnd_5536876 := by
    simpa [prefixWord, tailWord_5536876, baseEnd_5536876] using wordTrace_append hprefix tailTrace_5536876
  have hstable : (prefixWord ++ tailWord_5536876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536876).length < 2 ^ (prefixWord ++ tailWord_5536876).sum := by decide
  have hdescent : baseEnd_5536876 < baseStart_5536876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536899 : List Nat := [1, 1, 1, 3, 3, 2, 4, 2, 1, 1, 4]
def baseStart_5536899 : Nat := 118140960795 + 5536899 * 2 ^ 59
def prefixEnd_5536899 : Nat := 4983230072969 + 3 ^ 40 * 5536899 * 2
def baseEnd_5536899 : Nat := 2843090522398837590898771

theorem tailTrace_5536899 : CollatzResearch.WordTrace tailWord_5536899 prefixEnd_5536899 2843090522398837590898771 := by
  unfold tailWord_5536899
  simp only [CollatzResearch.WordTrace]
  refine ⟨201947297167768024909093751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134631531445178683272729167 201947297167768024909093751)
  ·
    refine ⟨302920945751652037363640627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201947297167768024909093751 302920945751652037363640627)
    ·
      refine ⟨454381418627478056045460941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302920945751652037363640627 454381418627478056045460941)
      ·
        refine ⟨170393031985304271017047853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 454381418627478056045460941 170393031985304271017047853)
        ·
          refine ⟨63897386994489101631392945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170393031985304271017047853 63897386994489101631392945)
          ·
            refine ⟨47923040245866826223544709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63897386994489101631392945 47923040245866826223544709)
            ·
              refine ⟨8985570046100029916914633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47923040245866826223544709 8985570046100029916914633)
              ·
                refine ⟨6739177534575022437685975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8985570046100029916914633 6739177534575022437685975)
                ·
                  refine ⟨10108766301862533656528963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6739177534575022437685975 10108766301862533656528963)
                  ·
                    refine ⟨15163149452793800484793445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10108766301862533656528963 15163149452793800484793445)
                    ·
                      refine ⟨2843090522398837590898771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15163149452793800484793445 2843090522398837590898771)
                      ·
                        rfl

theorem cell23_5536899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_5536899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536899 prefixEnd_5536899 := by exact prefixLift 5536899
  have htrace : WordTrace (prefixWord ++ tailWord_5536899) baseStart_5536899 baseEnd_5536899 := by
    simpa [prefixWord, tailWord_5536899, baseEnd_5536899] using wordTrace_append hprefix tailTrace_5536899
  have hstable : (prefixWord ++ tailWord_5536899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536899).length < 2 ^ (prefixWord ++ tailWord_5536899).sum := by decide
  have hdescent : baseEnd_5536899 < baseStart_5536899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536910 : List Nat := [4, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3]
def baseStart_5536910 : Nat := 118140960795 + 5536910 * 2 ^ 59
def prefixEnd_5536910 : Nat := 4983230072969 + 3 ^ 40 * 5536910 * 2
def baseEnd_5536910 : Nat := 2843096170686037047861221

theorem tailTrace_5536910 : CollatzResearch.WordTrace tailWord_5536910 prefixEnd_5536910 2843096170686037047861221 := by
  unfold tailWord_5536910
  simp only [CollatzResearch.WordTrace]
  refine ⟨25243462296341021723468023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134631798913818782525162789 25243462296341021723468023)
  ·
    refine ⟨37865193444511532585202035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25243462296341021723468023 37865193444511532585202035)
    ·
      refine ⟨56797790166767298877803053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37865193444511532585202035 56797790166767298877803053)
      ·
        refine ⟨21299171312537737079176145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56797790166767298877803053 21299171312537737079176145)
        ·
          refine ⟨15974378484403302809382109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21299171312537737079176145 15974378484403302809382109)
          ·
            refine ⟨5990391931651238553518291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15974378484403302809382109 5990391931651238553518291)
            ·
              refine ⟨8985587897476857830277437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5990391931651238553518291 8985587897476857830277437)
              ·
                refine ⟨3369595461553821686354039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8985587897476857830277437 3369595461553821686354039)
                ·
                  refine ⟨5054393192330732529531059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3369595461553821686354039 5054393192330732529531059)
                  ·
                    refine ⟨7581589788496098794296589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5054393192330732529531059 7581589788496098794296589)
                    ·
                      refine ⟨2843096170686037047861221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7581589788496098794296589 2843096170686037047861221)
                      ·
                        rfl

theorem cell23_5536910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_5536910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536910 prefixEnd_5536910 := by exact prefixLift 5536910
  have htrace : WordTrace (prefixWord ++ tailWord_5536910) baseStart_5536910 baseEnd_5536910 := by
    simpa [prefixWord, tailWord_5536910, baseEnd_5536910] using wordTrace_append hprefix tailTrace_5536910
  have hstable : (prefixWord ++ tailWord_5536910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536910).length < 2 ^ (prefixWord ++ tailWord_5536910).sum := by decide
  have hdescent : baseEnd_5536910 < baseStart_5536910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536919 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 5]
def baseStart_5536919 : Nat := 118140960795 + 5536919 * 2 ^ 59
def prefixEnd_5536919 : Nat := 4983230072969 + 3 ^ 40 * 5536919 * 2
def baseEnd_5536919 : Nat := 2843100792011927512648679

theorem tailTrace_5536919 : CollatzResearch.WordTrace tailWord_5536919 prefixEnd_5536919 2843100792011927512648679 := by
  unfold tailWord_5536919
  simp only [CollatzResearch.WordTrace]
  refine ⟨201948026627695568324821811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134632017751797045549881207 201948026627695568324821811)
  ·
    refine ⟨302922039941543352487232717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201948026627695568324821811 302922039941543352487232717)
    ·
      refine ⟨113595764978078757182712269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302922039941543352487232717 113595764978078757182712269)
      ·
        refine ⟨42598411866779533943517101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113595764978078757182712269 42598411866779533943517101)
        ·
          refine ⟨15974404450042325228818913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42598411866779533943517101 15974404450042325228818913)
          ·
            refine ⟨11980803337531743921614185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15974404450042325228818913 11980803337531743921614185)
            ·
              refine ⟨8985602503148807941210639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11980803337531743921614185 8985602503148807941210639)
              ·
                refine ⟨13478403754723211911815959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8985602503148807941210639 13478403754723211911815959)
                ·
                  refine ⟨20217605632084817867723939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13478403754723211911815959 20217605632084817867723939)
                  ·
                    refine ⟨30326408448127226801585909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20217605632084817867723939 30326408448127226801585909)
                    ·
                      refine ⟨2843100792011927512648679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30326408448127226801585909 2843100792011927512648679)
                      ·
                        rfl

theorem cell23_5536919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_5536919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536919 prefixEnd_5536919 := by exact prefixLift 5536919
  have htrace : WordTrace (prefixWord ++ tailWord_5536919) baseStart_5536919 baseEnd_5536919 := by
    simpa [prefixWord, tailWord_5536919, baseEnd_5536919] using wordTrace_append hprefix tailTrace_5536919
  have hstable : (prefixWord ++ tailWord_5536919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536919).length < 2 ^ (prefixWord ++ tailWord_5536919).sum := by decide
  have hdescent : baseEnd_5536919 < baseStart_5536919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536922 : List Nat := [3, 1, 1, 5, 1, 1, 11]
def baseStart_5536922 : Nat := 118140960795 + 5536922 * 2 ^ 59
def prefixEnd_5536922 : Nat := 4983230072969 + 3 ^ 40 * 5536922 * 2
def baseEnd_5536922 : Nat := 35100028795727049393965

theorem tailTrace_5536922 : CollatzResearch.WordTrace tailWord_5536922 prefixEnd_5536922 35100028795727049393965 := by
  unfold tailWord_5536922
  simp only [CollatzResearch.WordTrace]
  refine ⟨50487034011671174959295255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134632090697789799891454013 50487034011671174959295255)
  ·
    refine ⟨75730551017506762438942883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50487034011671174959295255 75730551017506762438942883)
    ·
      refine ⟨113595826526260143658414325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75730551017506762438942883 113595826526260143658414325)
      ·
        refine ⟨10649608736836888467976343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113595826526260143658414325 10649608736836888467976343)
        ·
          refine ⟨15974413105255332701964515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10649608736836888467976343 15974413105255332701964515)
          ·
            refine ⟨23961619657882999052946773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15974413105255332701964515 23961619657882999052946773)
            ·
              refine ⟨35100028795727049393965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23961619657882999052946773 35100028795727049393965)
              ·
                rfl

theorem cell23_5536922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 11].length) (baseStart_5536922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536922 prefixEnd_5536922 := by exact prefixLift 5536922
  have htrace : WordTrace (prefixWord ++ tailWord_5536922) baseStart_5536922 baseEnd_5536922 := by
    simpa [prefixWord, tailWord_5536922, baseEnd_5536922] using wordTrace_append hprefix tailTrace_5536922
  have hstable : (prefixWord ++ tailWord_5536922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536922).length < 2 ^ (prefixWord ++ tailWord_5536922).sum := by decide
  have hdescent : baseEnd_5536922 < baseStart_5536922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536926 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_5536926 : Nat := 118140960795 + 5536926 * 2 ^ 59
def prefixEnd_5536926 : Nat := 4983230072969 + 3 ^ 40 * 5536926 * 2
def baseEnd_5536926 : Nat := 947701462125502995087049

theorem tailTrace_5536926 : CollatzResearch.WordTrace tailWord_5536926 prefixEnd_5536926 947701462125502995087049 := by
  unfold tailWord_5536926
  simp only [CollatzResearch.WordTrace]
  refine ⟨25243535242333776065040829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134632187959113472346884421 25243535242333776065040829)
  ·
    refine ⟨9466325715875166024390311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25243535242333776065040829 9466325715875166024390311)
    ·
      refine ⟨14199488573812749036585467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9466325715875166024390311 14199488573812749036585467)
      ·
        refine ⟨21299232860719123554878201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14199488573812749036585467 21299232860719123554878201)
        ·
          refine ⟨15974424645539342666158651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21299232860719123554878201 15974424645539342666158651)
          ·
            refine ⟨23961636968309013999237977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15974424645539342666158651 23961636968309013999237977)
            ·
              refine ⟨17971227726231760499428483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23961636968309013999237977 17971227726231760499428483)
              ·
                refine ⟨26956841589347640749142725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17971227726231760499428483 26956841589347640749142725)
                ·
                  refine ⟨5054407798002682640464261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26956841589347640749142725 5054407798002682640464261)
                  ·
                    refine ⟨947701462125502995087049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5054407798002682640464261 947701462125502995087049)
                    ·
                      rfl

theorem cell23_5536926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_5536926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536926 prefixEnd_5536926 := by exact prefixLift 5536926
  have htrace : WordTrace (prefixWord ++ tailWord_5536926) baseStart_5536926 baseEnd_5536926 := by
    simpa [prefixWord, tailWord_5536926, baseEnd_5536926] using wordTrace_append hprefix tailTrace_5536926
  have hstable : (prefixWord ++ tailWord_5536926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536926).length < 2 ^ (prefixWord ++ tailWord_5536926).sum := by decide
  have hdescent : baseEnd_5536926 < baseStart_5536926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536933 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 3, 2, 2]
def baseStart_5536933 : Nat := 118140960795 + 5536933 * 2 ^ 59
def prefixEnd_5536933 : Nat := 4983230072969 + 3 ^ 40 * 5536933 * 2
def baseEnd_5536933 : Nat := 2843107980741090457873615

theorem tailTrace_5536933 : CollatzResearch.WordTrace tailWord_5536933 prefixEnd_5536933 2843107980741090457873615 := by
  unfold tailWord_5536933
  simp only [CollatzResearch.WordTrace]
  refine ⟨201948537249644848715831453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134632358166429899143887635 201948537249644848715831453)
  ·
    refine ⟨75730701468616818268436795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201948537249644848715831453 75730701468616818268436795)
    ·
      refine ⟨113596052202925227402655193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75730701468616818268436795 113596052202925227402655193)
      ·
        refine ⟨85197039152193920551991395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113596052202925227402655193 85197039152193920551991395)
        ·
          refine ⟨127795558728290880827987093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85197039152193920551991395 127795558728290880827987093)
          ·
            refine ⟨5990416815388635038811895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127795558728290880827987093 5990416815388635038811895)
            ·
              refine ⟨8985625223082952558217843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5990416815388635038811895 8985625223082952558217843)
              ·
                refine ⟨13478437834624428837326765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8985625223082952558217843 13478437834624428837326765)
                ·
                  refine ⟨5054414187984160813997537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13478437834624428837326765 5054414187984160813997537)
                  ·
                    refine ⟨3790810640988120610498153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5054414187984160813997537 3790810640988120610498153)
                    ·
                      refine ⟨2843107980741090457873615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790810640988120610498153 2843107980741090457873615)
                      ·
                        rfl

theorem cell23_5536933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_5536933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536933 prefixEnd_5536933 := by exact prefixLift 5536933
  have htrace : WordTrace (prefixWord ++ tailWord_5536933) baseStart_5536933 baseEnd_5536933 := by
    simpa [prefixWord, tailWord_5536933, baseEnd_5536933] using wordTrace_append hprefix tailTrace_5536933
  have hstable : (prefixWord ++ tailWord_5536933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536933).length < 2 ^ (prefixWord ++ tailWord_5536933).sum := by decide
  have hdescent : baseEnd_5536933 < baseStart_5536933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5536984 : List Nat := [2, 1, 2, 2, 6, 1, 2, 2, 1, 2, 2]
def baseStart_5536984 : Nat := 118140960795 + 5536984 * 2 ^ 59
def prefixEnd_5536984 : Nat := 4983230072969 + 3 ^ 40 * 5536984 * 2
def baseEnd_5536984 : Nat := 2843134168254469758335881

theorem tailTrace_5536984 : CollatzResearch.WordTrace tailWord_5536984 prefixEnd_5536984 2843134168254469758335881 := by
  unfold tailWord_5536984
  simp only [CollatzResearch.WordTrace]
  refine ⟨100975198686230042212969003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134633598248306722950625337 100975198686230042212969003)
  ·
    refine ⟨151462798029345063319453505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100975198686230042212969003 151462798029345063319453505)
    ·
      refine ⟨113597098522008797489590129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151462798029345063319453505 113597098522008797489590129)
      ·
        refine ⟨85197823891506598117192597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113597098522008797489590129 85197823891506598117192597)
        ·
          refine ⟨3993647994914371786743403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85197823891506598117192597 3993647994914371786743403)
          ·
            refine ⟨5990471992371557680115105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3993647994914371786743403 5990471992371557680115105)
            ·
              refine ⟨4492853994278668260086329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5990471992371557680115105 4492853994278668260086329)
              ·
                refine ⟨3369640495709001195064747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4492853994278668260086329 3369640495709001195064747)
                ·
                  refine ⟨5054460743563501792597121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3369640495709001195064747 5054460743563501792597121)
                  ·
                    refine ⟨3790845557672626344447841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5054460743563501792597121 3790845557672626344447841)
                    ·
                      refine ⟨2843134168254469758335881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790845557672626344447841 2843134168254469758335881)
                      ·
                        rfl

theorem cell23_5536984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_5536984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5536984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5536984 prefixEnd_5536984 := by exact prefixLift 5536984
  have htrace : WordTrace (prefixWord ++ tailWord_5536984) baseStart_5536984 baseEnd_5536984 := by
    simpa [prefixWord, tailWord_5536984, baseEnd_5536984] using wordTrace_append hprefix tailTrace_5536984
  have hstable : (prefixWord ++ tailWord_5536984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5536984).length < 2 ^ (prefixWord ++ tailWord_5536984).sum := by decide
  have hdescent : baseEnd_5536984 < baseStart_5536984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5536984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537006 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_5537006 : Nat := 118140960795 + 5537006 * 2 ^ 59
def prefixEnd_5537006 : Nat := 4983230072969 + 3 ^ 40 * 5537006 * 2
def baseEnd_5537006 : Nat := 2843145464828868672260779

theorem tailTrace_5537006 : CollatzResearch.WordTrace tailWord_5537006 prefixEnd_5537006 2843145464828868672260779 := by
  unfold tailWord_5537006
  simp only [CollatzResearch.WordTrace]
  refine ⟨25243899972297547772904859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134634133185586921455492581 25243899972297547772904859)
  ·
    refine ⟨37865849958446321659357289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25243899972297547772904859 37865849958446321659357289)
    ·
      refine ⟨28399387468834741244517967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37865849958446321659357289 28399387468834741244517967)
      ·
        refine ⟨42599081203252111866776951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28399387468834741244517967 42599081203252111866776951)
        ·
          refine ⟨63898621804878167800165427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42599081203252111866776951 63898621804878167800165427)
          ·
            refine ⟨95847932707317251700248141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63898621804878167800165427 95847932707317251700248141)
            ·
              refine ⟨35942974765243969387593053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95847932707317251700248141 35942974765243969387593053)
              ·
                refine ⟨13478615536966488520347395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35942974765243969387593053 13478615536966488520347395)
                ·
                  refine ⟨20217923305449732780521093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13478615536966488520347395 20217923305449732780521093)
                  ·
                    refine ⟨3790860619771824896347705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20217923305449732780521093 3790860619771824896347705)
                    ·
                      refine ⟨2843145464828868672260779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3790860619771824896347705 2843145464828868672260779)
                      ·
                        rfl

theorem cell23_5537006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_5537006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537006 prefixEnd_5537006 := by exact prefixLift 5537006
  have htrace : WordTrace (prefixWord ++ tailWord_5537006) baseStart_5537006 baseEnd_5537006 := by
    simpa [prefixWord, tailWord_5537006, baseEnd_5537006] using wordTrace_append hprefix tailTrace_5537006
  have hstable : (prefixWord ++ tailWord_5537006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537006).length < 2 ^ (prefixWord ++ tailWord_5537006).sum := by decide
  have hdescent : baseEnd_5537006 < baseStart_5537006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537072 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 2, 8]
def baseStart_5537072 : Nat := 118140960795 + 5537072 * 2 ^ 59
def prefixEnd_5537072 : Nat := 4983230072969 + 3 ^ 40 * 5537072 * 2
def baseEnd_5537072 : Nat := 947726451517355138011825

theorem tailTrace_5537072 : CollatzResearch.WordTrace tailWord_5537072 prefixEnd_5537072 947726451517355138011825 := by
  unfold tailWord_5537072
  simp only [CollatzResearch.WordTrace]
  refine ⟨100976803498070637727570735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134635737997427516970094313 100976803498070637727570735)
  ·
    refine ⟨151465205247105956591356103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100976803498070637727570735 151465205247105956591356103)
    ·
      refine ⟨227197807870658934887034155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151465205247105956591356103 227197807870658934887034155)
      ·
        refine ⟨340796711805988402330551233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227197807870658934887034155 340796711805988402330551233)
        ·
          refine ⟨255597533854491301747913425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340796711805988402330551233 255597533854491301747913425)
          ·
            refine ⟨191698150390868476310935069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255597533854491301747913425 191698150390868476310935069)
            ·
              refine ⟨71886806396575678616600651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191698150390868476310935069 71886806396575678616600651)
              ·
                refine ⟨107830209594863517924900977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71886806396575678616600651 107830209594863517924900977)
                ·
                  refine ⟨80872657196147638443675733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107830209594863517924900977 80872657196147638443675733)
                  ·
                    refine ⟨947726451517355138011825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80872657196147638443675733 947726451517355138011825)
                    ·
                      rfl

theorem cell23_5537072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_5537072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537072 prefixEnd_5537072 := by exact prefixLift 5537072
  have htrace : WordTrace (prefixWord ++ tailWord_5537072) baseStart_5537072 baseEnd_5537072 := by
    simpa [prefixWord, tailWord_5537072, baseEnd_5537072] using wordTrace_append hprefix tailTrace_5537072
  have hstable : (prefixWord ++ tailWord_5537072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537072).length < 2 ^ (prefixWord ++ tailWord_5537072).sum := by decide
  have hdescent : baseEnd_5537072 < baseStart_5537072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537076 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_5537076 : Nat := 118140960795 + 5537076 * 2 ^ 59
def prefixEnd_5537076 : Nat := 4983230072969 + 3 ^ 40 * 5537076 * 2
def baseEnd_5537076 : Nat := 947727136158227799461819

theorem tailTrace_5537076 : CollatzResearch.WordTrace tailWord_5537076 prefixEnd_5537076 947727136158227799461819 := by
  unfold tailWord_5537076
  simp only [CollatzResearch.WordTrace]
  refine ⟨100976876444063392069143541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134635835258751189425524721 100976876444063392069143541)
  ·
    refine ⟨9466582166630943006482207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100976876444063392069143541 9466582166630943006482207)
    ·
      refine ⟨14199873249946414509723311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9466582166630943006482207 14199873249946414509723311)
      ·
        refine ⟨21299809874919621764584967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14199873249946414509723311 21299809874919621764584967)
        ·
          refine ⟨31949714812379432646877451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21299809874919621764584967 31949714812379432646877451)
          ·
            refine ⟨47924572218569148970316177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31949714812379432646877451 47924572218569148970316177)
            ·
              refine ⟨35943429163926861727737133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47924572218569148970316177 35943429163926861727737133)
              ·
                refine ⟨13478785936472573147901425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35943429163926861727737133 13478785936472573147901425)
                ·
                  refine ⟨10109089452354429860926069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13478785936472573147901425 10109089452354429860926069)
                  ·
                    refine ⟨947727136158227799461819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10109089452354429860926069 947727136158227799461819)
                    ·
                      rfl

theorem cell23_5537076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_5537076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537076 prefixEnd_5537076 := by exact prefixLift 5537076
  have htrace : WordTrace (prefixWord ++ tailWord_5537076) baseStart_5537076 baseEnd_5537076 := by
    simpa [prefixWord, tailWord_5537076, baseEnd_5537076] using wordTrace_append hprefix tailTrace_5537076
  have hstable : (prefixWord ++ tailWord_5537076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537076).length < 2 ^ (prefixWord ++ tailWord_5537076).sum := by decide
  have hdescent : baseEnd_5537076 < baseStart_5537076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537133 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_5537133 : Nat := 118140960795 + 5537133 * 2 ^ 59
def prefixEnd_5537133 : Nat := 4983230072969 + 3 ^ 40 * 5537133 * 2
def baseEnd_5537133 : Nat := 2843210676871989675372695

theorem tailTrace_5537133 : CollatzResearch.WordTrace tailWord_5537133 prefixEnd_5537133 2843210676871989675372695 := by
  unfold tailWord_5537133
  simp only [CollatzResearch.WordTrace]
  refine ⟨201955831848920282873112053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134637221232613521915408035 201955831848920282873112053)
  ·
    refine ⟨18933359235836276519354255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201955831848920282873112053 18933359235836276519354255)
    ·
      refine ⟨28400038853754414779031383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18933359235836276519354255 28400038853754414779031383)
      ·
        refine ⟨42600058280631622168547075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28400038853754414779031383 42600058280631622168547075)
        ·
          refine ⟨63900087420947433252820613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42600058280631622168547075 63900087420947433252820613)
          ·
            refine ⟨11981266391427643734903865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63900087420947433252820613 11981266391427643734903865)
            ·
              refine ⟨8985949793570732801177899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11981266391427643734903865 8985949793570732801177899)
              ·
                refine ⟨13478924690356099201766849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8985949793570732801177899 13478924690356099201766849)
                ·
                  refine ⟨10109193517767074401325137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13478924690356099201766849 10109193517767074401325137)
                  ·
                    refine ⟨7581895138325305800993853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10109193517767074401325137 7581895138325305800993853)
                    ·
                      refine ⟨2843210676871989675372695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7581895138325305800993853 2843210676871989675372695)
                      ·
                        rfl

theorem cell23_5537133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_5537133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537133 prefixEnd_5537133 := by exact prefixLift 5537133
  have htrace : WordTrace (prefixWord ++ tailWord_5537133) baseStart_5537133 baseEnd_5537133 := by
    simpa [prefixWord, tailWord_5537133, baseEnd_5537133] using wordTrace_append hprefix tailTrace_5537133
  have hstable : (prefixWord ++ tailWord_5537133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537133).length < 2 ^ (prefixWord ++ tailWord_5537133).sum := by decide
  have hdescent : baseEnd_5537133 < baseStart_5537133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537146 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3]
def baseStart_5537146 : Nat := 118140960795 + 5537146 * 2 ^ 59
def prefixEnd_5537146 : Nat := 4983230072969 + 3 ^ 40 * 5537146 * 2
def baseEnd_5537146 : Nat := 2843217352120498124510135

theorem tailTrace_5537146 : CollatzResearch.WordTrace tailWord_5537146 prefixEnd_5537146 2843217352120498124510135 := by
  unfold tailWord_5537146
  simp only [CollatzResearch.WordTrace]
  refine ⟨50489076499468296523333823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134637537331915457395556861 50489076499468296523333823)
  ·
    refine ⟨75733614749202444785000735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50489076499468296523333823 75733614749202444785000735)
    ·
      refine ⟨113600422123803667177501103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75733614749202444785000735 113600422123803667177501103)
      ·
        refine ⟨170400633185705500766251655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113600422123803667177501103 170400633185705500766251655)
        ·
          refine ⟨255600949778558251149377483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170400633185705500766251655 255600949778558251149377483)
          ·
            refine ⟨383401424667837376724066225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255600949778558251149377483 383401424667837376724066225)
            ·
              refine ⟨287551068500878032543049669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383401424667837376724066225 287551068500878032543049669)
              ·
                refine ⟨53915825343914631101821813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 287551068500878032543049669 53915825343914631101821813)
                ·
                  refine ⟨5054608625991996665795795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53915825343914631101821813 5054608625991996665795795)
                  ·
                    refine ⟨7581912938987994998693693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5054608625991996665795795 7581912938987994998693693)
                    ·
                      refine ⟨2843217352120498124510135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7581912938987994998693693 2843217352120498124510135)
                      ·
                        rfl

theorem cell23_5537146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_5537146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537146 prefixEnd_5537146 := by exact prefixLift 5537146
  have htrace : WordTrace (prefixWord ++ tailWord_5537146) baseStart_5537146 baseEnd_5537146 := by
    simpa [prefixWord, tailWord_5537146, baseEnd_5537146] using wordTrace_append hprefix tailTrace_5537146
  have hstable : (prefixWord ++ tailWord_5537146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537146).length < 2 ^ (prefixWord ++ tailWord_5537146).sum := by decide
  have hdescent : baseEnd_5537146 < baseStart_5537146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537153 : List Nat := [1, 2, 4, 3, 2, 1, 2, 2, 6]
def baseStart_5537153 : Nat := 118140960795 + 5537153 * 2 ^ 59
def prefixEnd_5537153 : Nat := 4983230072969 + 3 ^ 40 * 5537153 * 2
def baseEnd_5537153 : Nat := 315913438498342177458067

theorem tailTrace_5537153 : CollatzResearch.WordTrace tailWord_5537153 prefixEnd_5537153 315913438498342177458067 := by
  unfold tailWord_5537153
  simp only [CollatzResearch.WordTrace]
  refine ⟨201956561308847826288840113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134637707539231884192560075 201956561308847826288840113)
  ·
    refine ⟨151467420981635869716630085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201956561308847826288840113 151467420981635869716630085)
    ·
      refine ⟨28400141434056725571868141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151467420981635869716630085 28400141434056725571868141)
      ·
        refine ⟨10650053037771272089450553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28400141434056725571868141 10650053037771272089450553)
        ·
          refine ⟨7987539778328454067087915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10650053037771272089450553 7987539778328454067087915)
          ·
            refine ⟨11981309667492681100631873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7987539778328454067087915 11981309667492681100631873)
            ·
              refine ⟨8985982250619510825473905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11981309667492681100631873 8985982250619510825473905)
              ·
                refine ⟨6739486687964633119105429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8985982250619510825473905 6739486687964633119105429)
                ·
                  refine ⟨315913438498342177458067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6739486687964633119105429 315913438498342177458067)
                  ·
                    rfl

theorem cell23_5537153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 6].length) (baseStart_5537153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537153 prefixEnd_5537153 := by exact prefixLift 5537153
  have htrace : WordTrace (prefixWord ++ tailWord_5537153) baseStart_5537153 baseEnd_5537153 := by
    simpa [prefixWord, tailWord_5537153, baseEnd_5537153] using wordTrace_append hprefix tailTrace_5537153
  have hstable : (prefixWord ++ tailWord_5537153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537153).length < 2 ^ (prefixWord ++ tailWord_5537153).sum := by decide
  have hdescent : baseEnd_5537153 < baseStart_5537153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537189 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_5537189 : Nat := 118140960795 + 5537189 * 2 ^ 59
def prefixEnd_5537189 : Nat := 4983230072969 + 3 ^ 40 * 5537189 * 2
def baseEnd_5537189 : Nat := 2843239431788641456272437

theorem tailTrace_5537189 : CollatzResearch.WordTrace tailWord_5537189 prefixEnd_5537189 2843239431788641456272437 := by
  unfold tailWord_5537189
  simp only [CollatzResearch.WordTrace]
  refine ⟨201957874336717404437150621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134638582891144936291433747 201957874336717404437150621)
  ·
    refine ⟨75734202876269026663931483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201957874336717404437150621 75734202876269026663931483)
    ·
      refine ⟨113601304314403539995897225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75734202876269026663931483 113601304314403539995897225)
      ·
        refine ⟨85200978235802654996922919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113601304314403539995897225 85200978235802654996922919)
        ·
          refine ⟨127801467353703982495384379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85200978235802654996922919 127801467353703982495384379)
          ·
            refine ⟨191702201030555973743076569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127801467353703982495384379 191702201030555973743076569)
            ·
              refine ⟨143776650772916980307307427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191702201030555973743076569 143776650772916980307307427)
              ·
                refine ⟨215664976159375470460961141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143776650772916980307307427 215664976159375470460961141)
                ·
                  refine ⟨20218591514941450355715107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 215664976159375470460961141 20218591514941450355715107)
                  ·
                    refine ⟨30327887272412175533572661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20218591514941450355715107 30327887272412175533572661)
                    ·
                      refine ⟨2843239431788641456272437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30327887272412175533572661 2843239431788641456272437)
                      ·
                        rfl

theorem cell23_5537189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_5537189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537189 prefixEnd_5537189 := by exact prefixLift 5537189
  have htrace : WordTrace (prefixWord ++ tailWord_5537189) baseStart_5537189 baseEnd_5537189 := by
    simpa [prefixWord, tailWord_5537189, baseEnd_5537189] using wordTrace_append hprefix tailTrace_5537189
  have hstable : (prefixWord ++ tailWord_5537189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537189).length < 2 ^ (prefixWord ++ tailWord_5537189).sum := by decide
  have hdescent : baseEnd_5537189 < baseStart_5537189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537197 : List Nat := [1, 5, 2, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_5537197 : Nat := 118140960795 + 5537197 * 2 ^ 59
def prefixEnd_5537197 : Nat := 4983230072969 + 3 ^ 40 * 5537197 * 2
def baseEnd_5537197 : Nat := 2843243539633877424972401

theorem tailTrace_5537197 : CollatzResearch.WordTrace tailWord_5537197 prefixEnd_5537197 2843243539633877424972401 := by
  unfold tailWord_5537197
  simp only [CollatzResearch.WordTrace]
  refine ⟨201958166120688421803441845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134638777413792281202294563 201958166120688421803441845)
  ·
    refine ⟨18933578073814539544072673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201958166120688421803441845 18933578073814539544072673)
    ·
      refine ⟨14200183555360904658054505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18933578073814539544072673 14200183555360904658054505)
      ·
        refine ⟨10650137666520678493540879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14200183555360904658054505 10650137666520678493540879)
        ·
          refine ⟨15975206499781017740311319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10650137666520678493540879 15975206499781017740311319)
          ·
            refine ⟨23962809749671526610466979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15975206499781017740311319 23962809749671526610466979)
            ·
              refine ⟨35944214624507289915700469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23962809749671526610466979 35944214624507289915700469)
              ·
                refine ⟨3369770121047558429596919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35944214624507289915700469 3369770121047558429596919)
                ·
                  refine ⟨5054655181571337644395379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3369770121047558429596919 5054655181571337644395379)
                  ·
                    refine ⟨7581982772357006466593069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5054655181571337644395379 7581982772357006466593069)
                    ·
                      refine ⟨2843243539633877424972401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7581982772357006466593069 2843243539633877424972401)
                      ·
                        rfl

theorem cell23_5537197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_5537197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537197 prefixEnd_5537197 := by exact prefixLift 5537197
  have htrace : WordTrace (prefixWord ++ tailWord_5537197) baseStart_5537197 baseEnd_5537197 := by
    simpa [prefixWord, tailWord_5537197, baseEnd_5537197] using wordTrace_append hprefix tailTrace_5537197
  have hstable : (prefixWord ++ tailWord_5537197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537197).length < 2 ^ (prefixWord ++ tailWord_5537197).sum := by decide
  have hdescent : baseEnd_5537197 < baseStart_5537197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537239 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 2, 7]
def baseStart_5537239 : Nat := 118140960795 + 5537239 * 2 ^ 59
def prefixEnd_5537239 : Nat := 4983230072969 + 3 ^ 40 * 5537239 * 2
def baseEnd_5537239 : Nat := 947755035273788753549069

theorem tailTrace_5537239 : CollatzResearch.WordTrace tailWord_5537239 prefixEnd_5537239 947755035273788753549069 := by
  unfold tailWord_5537239
  simp only [CollatzResearch.WordTrace]
  refine ⟨201959697986536262976470771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134639798657690841984313847 201959697986536262976470771)
  ·
    refine ⟨302939546979804394464706157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201959697986536262976470771 302939546979804394464706157)
    ·
      refine ⟨113602330117426647924264809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302939546979804394464706157 113602330117426647924264809)
      ·
        refine ⟨85201747588069985943198607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113602330117426647924264809 85201747588069985943198607)
        ·
          refine ⟨127802621382104978914797911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85201747588069985943198607 127802621382104978914797911)
          ·
            refine ⟨191703932073157468372196867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127802621382104978914797911 191703932073157468372196867)
            ·
              refine ⟨287555898109736202558295301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191703932073157468372196867 287555898109736202558295301)
              ·
                refine ⟨53916730895575537979680369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 287555898109736202558295301 53916730895575537979680369)
                ·
                  refine ⟨40437548171681653484760277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53916730895575537979680369 40437548171681653484760277)
                  ·
                    refine ⟨947755035273788753549069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40437548171681653484760277 947755035273788753549069)
                    ·
                      rfl

theorem cell23_5537239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_5537239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537239 prefixEnd_5537239 := by exact prefixLift 5537239
  have htrace : WordTrace (prefixWord ++ tailWord_5537239) baseStart_5537239 baseEnd_5537239 := by
    simpa [prefixWord, tailWord_5537239, baseEnd_5537239] using wordTrace_append hprefix tailTrace_5537239
  have hstable : (prefixWord ++ tailWord_5537239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537239).length < 2 ^ (prefixWord ++ tailWord_5537239).sum := by decide
  have hdescent : baseEnd_5537239 < baseStart_5537239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537270 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_5537270 : Nat := 118140960795 + 5537270 * 2 ^ 59
def prefixEnd_5537270 : Nat := 4983230072969 + 3 ^ 40 * 5537270 * 2
def baseEnd_5537270 : Nat := 2843281023721655639359565

theorem tailTrace_5537270 : CollatzResearch.WordTrace tailWord_5537270 prefixEnd_5537270 2843281023721655639359565 := by
  unfold tailWord_5537270
  simp only [CollatzResearch.WordTrace]
  refine ⟨12622551790588997204428079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134640552432949303513899509 12622551790588997204428079)
  ·
    refine ⟨18933827685883495806642119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12622551790588997204428079 18933827685883495806642119)
    ·
      refine ⟨28400741528825243709963179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18933827685883495806642119 28400741528825243709963179)
      ·
        refine ⟨42601112293237865564944769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28400741528825243709963179 42601112293237865564944769)
        ·
          refine ⟨31950834219928399173708577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42601112293237865564944769 31950834219928399173708577)
          ·
            refine ⟨23963125664946299380281433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31950834219928399173708577 23963125664946299380281433)
            ·
              refine ⟨17972344248709724535211075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23963125664946299380281433 17972344248709724535211075)
              ·
                refine ⟨26958516373064586802816613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17972344248709724535211075 26958516373064586802816613)
                ·
                  refine ⟨5054721819949610025528115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26958516373064586802816613 5054721819949610025528115)
                  ·
                    refine ⟨7582082729924415038292173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5054721819949610025528115 7582082729924415038292173)
                    ·
                      refine ⟨2843281023721655639359565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7582082729924415038292173 2843281023721655639359565)
                      ·
                        rfl

theorem cell23_5537270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_5537270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537270 prefixEnd_5537270 := by exact prefixLift 5537270
  have htrace : WordTrace (prefixWord ++ tailWord_5537270) baseStart_5537270 baseEnd_5537270 := by
    simpa [prefixWord, tailWord_5537270, baseEnd_5537270] using wordTrace_append hprefix tailTrace_5537270
  have hstable : (prefixWord ++ tailWord_5537270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537270).length < 2 ^ (prefixWord ++ tailWord_5537270).sum := by decide
  have hdescent : baseEnd_5537270 < baseStart_5537270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537287 : List Nat := [1, 1, 4, 3, 2, 1, 4, 1, 2, 1, 3]
def baseStart_5537287 : Nat := 118140960795 + 5537287 * 2 ^ 59
def prefixEnd_5537287 : Nat := 4983230072969 + 3 ^ 40 * 5537287 * 2
def baseEnd_5537287 : Nat := 2843289752892782072846987

theorem tailTrace_5537287 : CollatzResearch.WordTrace tailWord_5537287 prefixEnd_5537287 2843289752892782072846987 := by
  unfold tailWord_5537287
  simp only [CollatzResearch.WordTrace]
  refine ⟨201961448690362367174218115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134640965793574911449478743 201961448690362367174218115)
  ·
    refine ⟨302942173035543550761327173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201961448690362367174218115 302942173035543550761327173)
    ·
      refine ⟨56801657444164415767748845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302942173035543550761327173 56801657444164415767748845)
      ·
        refine ⟨21300621541561655912905817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56801657444164415767748845 21300621541561655912905817)
        ·
          refine ⟨15975466156171241934679363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21300621541561655912905817 15975466156171241934679363)
          ·
            refine ⟨23963199234256862902019045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15975466156171241934679363 23963199234256862902019045)
            ·
              refine ⟨4493099856423161794128571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23963199234256862902019045 4493099856423161794128571)
              ·
                refine ⟨6739649784634742691192857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4493099856423161794128571 6739649784634742691192857)
                ·
                  refine ⟨5054737338476057018394643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6739649784634742691192857 5054737338476057018394643)
                  ·
                    refine ⟨7582106007714085527591965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5054737338476057018394643 7582106007714085527591965)
                    ·
                      refine ⟨2843289752892782072846987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7582106007714085527591965 2843289752892782072846987)
                      ·
                        rfl

theorem cell23_5537287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_5537287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537287 prefixEnd_5537287 := by exact prefixLift 5537287
  have htrace : WordTrace (prefixWord ++ tailWord_5537287) baseStart_5537287 baseEnd_5537287 := by
    simpa [prefixWord, tailWord_5537287, baseEnd_5537287] using wordTrace_append hprefix tailTrace_5537287
  have hstable : (prefixWord ++ tailWord_5537287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537287).length < 2 ^ (prefixWord ++ tailWord_5537287).sum := by decide
  have hdescent : baseEnd_5537287 < baseStart_5537287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537306 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_5537306 : Nat := 118140960795 + 5537306 * 2 ^ 59
def prefixEnd_5537306 : Nat := 4983230072969 + 3 ^ 40 * 5537306 * 2
def baseEnd_5537306 : Nat := 2843299509025217498509399

theorem tailTrace_5537306 : CollatzResearch.WordTrace tailWord_5537306 prefixEnd_5537306 2843299509025217498509399 := by
  unfold tailWord_5537306
  simp only [CollatzResearch.WordTrace]
  refine ⟨50490535419323383354789943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134641427784862355612773181 50490535419323383354789943)
  ·
    refine ⟨75735803128985075032184915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50490535419323383354789943 75735803128985075032184915)
    ·
      refine ⟨113603704693477612548277373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75735803128985075032184915 113603704693477612548277373)
      ·
        refine ⟨42601389260054104705604015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113603704693477612548277373 42601389260054104705604015)
        ·
          refine ⟨63902083890081157058406023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42601389260054104705604015 63902083890081157058406023)
          ·
            refine ⟨95853125835121735587609035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63902083890081157058406023 95853125835121735587609035)
            ·
              refine ⟨143779688752682603381413553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95853125835121735587609035 143779688752682603381413553)
              ·
                refine ⟨107834766564511952536060165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143779688752682603381413553 107834766564511952536060165)
                ·
                  refine ⟨20219018730845991100511281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107834766564511952536060165 20219018730845991100511281)
                  ·
                    refine ⟨15164264048134493325383461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20219018730845991100511281 15164264048134493325383461)
                    ·
                      refine ⟨2843299509025217498509399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15164264048134493325383461 2843299509025217498509399)
                      ·
                        rfl

theorem cell23_5537306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_5537306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537306 prefixEnd_5537306 := by exact prefixLift 5537306
  have htrace : WordTrace (prefixWord ++ tailWord_5537306) baseStart_5537306 baseEnd_5537306 := by
    simpa [prefixWord, tailWord_5537306, baseEnd_5537306] using wordTrace_append hprefix tailTrace_5537306
  have hstable : (prefixWord ++ tailWord_5537306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537306).length < 2 ^ (prefixWord ++ tailWord_5537306).sum := by decide
  have hdescent : baseEnd_5537306 < baseStart_5537306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537343 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 3]
def baseStart_5537343 : Nat := 118140960795 + 5537343 * 2 ^ 59
def prefixEnd_5537343 : Nat := 4983230072969 + 3 ^ 40 * 5537343 * 2
def baseEnd_5537343 : Nat := 2843318507809433853746729

theorem tailTrace_5537343 : CollatzResearch.WordTrace tailWord_5537343 prefixEnd_5537343 2843318507809433853746729 := by
  unfold tailWord_5537343
  simp only [CollatzResearch.WordTrace]
  refine ⟨201963491178159488738256683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134642327452106325825504455 201963491178159488738256683)
  ·
    refine ⟨302945236767239233107385025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201963491178159488738256683 302945236767239233107385025)
    ·
      refine ⟨227208927575429424830538769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302945236767239233107385025 227208927575429424830538769)
      ·
        refine ⟨170406695681572068622904077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227208927575429424830538769 170406695681572068622904077)
        ·
          refine ⟨63902510880589525733589029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170406695681572068622904077 63902510880589525733589029)
          ·
            refine ⟨11981720790110536075047943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63902510880589525733589029 11981720790110536075047943)
            ·
              refine ⟨17972581185165804112571915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11981720790110536075047943 17972581185165804112571915)
              ·
                refine ⟨26958871777748706168857873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17972581185165804112571915 26958871777748706168857873)
                ·
                  refine ⟨20219153833311529626643405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26958871777748706168857873 20219153833311529626643405)
                  ·
                    refine ⟨7582182687491823609991277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20219153833311529626643405 7582182687491823609991277)
                    ·
                      refine ⟨2843318507809433853746729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7582182687491823609991277 2843318507809433853746729)
                      ·
                        rfl

theorem cell23_5537343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_5537343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537343 prefixEnd_5537343 := by exact prefixLift 5537343
  have htrace : WordTrace (prefixWord ++ tailWord_5537343) baseStart_5537343 baseEnd_5537343 := by
    simpa [prefixWord, tailWord_5537343, baseEnd_5537343] using wordTrace_append hprefix tailTrace_5537343
  have hstable : (prefixWord ++ tailWord_5537343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537343).length < 2 ^ (prefixWord ++ tailWord_5537343).sum := by decide
  have hdescent : baseEnd_5537343 < baseStart_5537343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537383 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_5537383 : Nat := 118140960795 + 5537383 * 2 ^ 59
def prefixEnd_5537383 : Nat := 4983230072969 + 3 ^ 40 * 5537383 * 2
def baseEnd_5537383 : Nat := 2843339047035613697246545

theorem tailTrace_5537383 : CollatzResearch.WordTrace tailWord_5537383 prefixEnd_5537383 2843339047035613697246545 := by
  unfold tailWord_5537383
  simp only [CollatzResearch.WordTrace]
  refine ⟨201964950098014575569712803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134643300065343050379808535 201964950098014575569712803)
  ·
    refine ⟨302947425147021863354569205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201964950098014575569712803 302947425147021863354569205)
    ·
      refine ⟨28401321107533299689490863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 302947425147021863354569205 28401321107533299689490863)
      ·
        refine ⟨42601981661299949534236295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28401321107533299689490863 42601981661299949534236295)
        ·
          refine ⟨63902972491949924301354443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42601981661299949534236295 63902972491949924301354443)
          ·
            refine ⟨95854458737924886452031665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63902972491949924301354443 95854458737924886452031665)
            ·
              refine ⟨71890844053443664839023749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95854458737924886452031665 71890844053443664839023749)
              ·
                refine ⟨13479533260020687157316953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71890844053443664839023749 13479533260020687157316953)
                ·
                  refine ⟨10109649945015515367987715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13479533260020687157316953 10109649945015515367987715)
                  ·
                    refine ⟨15164474917523273051981573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10109649945015515367987715 15164474917523273051981573)
                    ·
                      refine ⟨2843339047035613697246545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15164474917523273051981573 2843339047035613697246545)
                      ·
                        rfl

theorem cell23_5537383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_5537383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537383 prefixEnd_5537383 := by exact prefixLift 5537383
  have htrace : WordTrace (prefixWord ++ tailWord_5537383) baseStart_5537383 baseEnd_5537383 := by
    simpa [prefixWord, tailWord_5537383, baseEnd_5537383] using wordTrace_append hprefix tailTrace_5537383
  have hstable : (prefixWord ++ tailWord_5537383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537383).length < 2 ^ (prefixWord ++ tailWord_5537383).sum := by decide
  have hdescent : baseEnd_5537383 < baseStart_5537383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537444 : List Nat := [2, 3, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_5537444 : Nat := 118140960795 + 5537444 * 2 ^ 59
def prefixEnd_5537444 : Nat := 4983230072969 + 3 ^ 40 * 5537444 * 2
def baseEnd_5537444 : Nat := 947790123118512652861255

theorem tailTrace_5537444 : CollatzResearch.WordTrace tailWord_5537444 prefixEnd_5537444 947790123118512652861255 := by
  unfold tailWord_5537444
  simp only [CollatzResearch.WordTrace]
  refine ⟨100983587475396791493841693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134644783300529055325122257 100983587475396791493841693)
  ·
    refine ⟨37868845303273796810190635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100983587475396791493841693 37868845303273796810190635)
    ·
      refine ⟨56803267954910695215285953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37868845303273796810190635 56803267954910695215285953)
      ·
        refine ⟨42602450966183021411464465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56803267954910695215285953 42602450966183021411464465)
        ·
          refine ⟨31951838224637266058598349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42602450966183021411464465 31951838224637266058598349)
          ·
            refine ⟨11981939334238974771974381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31951838224637266058598349 11981939334238974771974381)
            ·
              refine ⟨4493227250339615539490393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11981939334238974771974381 4493227250339615539490393)
              ·
                refine ⟨3369920437754711654617795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4493227250339615539490393 3369920437754711654617795)
                ·
                  refine ⟨5054880656632067481926693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3369920437754711654617795 5054880656632067481926693)
                  ·
                    refine ⟨947790123118512652861255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5054880656632067481926693 947790123118512652861255)
                    ·
                      rfl

theorem cell23_5537444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_5537444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537444 prefixEnd_5537444 := by exact prefixLift 5537444
  have htrace : WordTrace (prefixWord ++ tailWord_5537444) baseStart_5537444 baseEnd_5537444 := by
    simpa [prefixWord, tailWord_5537444, baseEnd_5537444] using wordTrace_append hprefix tailTrace_5537444
  have hstable : (prefixWord ++ tailWord_5537444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537444).length < 2 ^ (prefixWord ++ tailWord_5537444).sum := by decide
  have hdescent : baseEnd_5537444 < baseStart_5537444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537470 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_5537470 : Nat := 118140960795 + 5537470 * 2 ^ 59
def prefixEnd_5537470 : Nat := 4983230072969 + 3 ^ 40 * 5537470 * 2
def baseEnd_5537470 : Nat := 947794573284184952286215

theorem tailTrace_5537470 : CollatzResearch.WordTrace tailWord_5537470 prefixEnd_5537470 947794573284184952286215 := by
  unfold tailWord_5537470
  simp only [CollatzResearch.WordTrace]
  refine ⟨25246015406087423678516233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134645415499132926285419909 25246015406087423678516233)
  ·
    refine ⟨18934511554565567758887175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25246015406087423678516233 18934511554565567758887175)
    ·
      refine ⟨28401767331848351638330763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18934511554565567758887175 28401767331848351638330763)
      ·
        refine ⟨42602650997772527457496145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28401767331848351638330763 42602650997772527457496145)
        ·
          refine ⟨31951988248329395593122109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42602650997772527457496145 31951988248329395593122109)
          ·
            refine ⟨11981995593123523347420791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31951988248329395593122109 11981995593123523347420791)
            ·
              refine ⟨17972993389685285021131187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11981995593123523347420791 17972993389685285021131187)
              ·
                refine ⟨26959490084527927531696781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17972993389685285021131187 26959490084527927531696781)
                ·
                  refine ⟨10109808781697972824386293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26959490084527927531696781 10109808781697972824386293)
                  ·
                    refine ⟨947794573284184952286215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10109808781697972824386293 947794573284184952286215)
                    ·
                      rfl

theorem cell23_5537470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_5537470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537470 prefixEnd_5537470 := by exact prefixLift 5537470
  have htrace : WordTrace (prefixWord ++ tailWord_5537470) baseStart_5537470 baseEnd_5537470 := by
    simpa [prefixWord, tailWord_5537470, baseEnd_5537470] using wordTrace_append hprefix tailTrace_5537470
  have hstable : (prefixWord ++ tailWord_5537470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537470).length < 2 ^ (prefixWord ++ tailWord_5537470).sum := by decide
  have hdescent : baseEnd_5537470 < baseStart_5537470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537483 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 6, 4]
def baseStart_5537483 : Nat := 118140960795 + 5537483 * 2 ^ 59
def prefixEnd_5537483 : Nat := 4983230072969 + 3 ^ 40 * 5537483 * 2
def baseEnd_5537483 : Nat := 947796798367021101998695

theorem tailTrace_5537483 : CollatzResearch.WordTrace tailWord_5537483 prefixEnd_5537483 947796798367021101998695 := by
  unfold tailWord_5537483
  simp only [CollatzResearch.WordTrace]
  refine ⟨201968597397652292648353103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134645731598434861765568735 201968597397652292648353103)
  ·
    refine ⟨302952896096478438972529655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201968597397652292648353103 302952896096478438972529655)
    ·
      refine ⟨454429344144717658458794483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302952896096478438972529655 454429344144717658458794483)
      ·
        refine ⟨681644016217076487688191725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454429344144717658458794483 681644016217076487688191725)
        ·
          refine ⟨255616506081403682883071897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 681644016217076487688191725 255616506081403682883071897)
          ·
            refine ⟨191712379561052762162303923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255616506081403682883071897 191712379561052762162303923)
            ·
              refine ⟨287568569341579143243455885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191712379561052762162303923 287568569341579143243455885)
              ·
                refine ⟨107838213503092178716295957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287568569341579143243455885 107838213503092178716295957)
                ·
                  refine ⟨5054916257957445877326373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107838213503092178716295957 5054916257957445877326373)
                  ·
                    refine ⟨947796798367021101998695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5054916257957445877326373 947796798367021101998695)
                    ·
                      rfl

theorem cell23_5537483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 4].length) (baseStart_5537483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537483 prefixEnd_5537483 := by exact prefixLift 5537483
  have htrace : WordTrace (prefixWord ++ tailWord_5537483) baseStart_5537483 baseEnd_5537483 := by
    simpa [prefixWord, tailWord_5537483, baseEnd_5537483] using wordTrace_append hprefix tailTrace_5537483
  have hstable : (prefixWord ++ tailWord_5537483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537483).length < 2 ^ (prefixWord ++ tailWord_5537483).sum := by decide
  have hdescent : baseEnd_5537483 < baseStart_5537483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537503 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 4]
def baseStart_5537503 : Nat := 118140960795 + 5537503 * 2 ^ 59
def prefixEnd_5537503 : Nat := 4983230072969 + 3 ^ 40 * 5537503 * 2
def baseEnd_5537503 : Nat := 2843400664714153227745993

theorem tailTrace_5537503 : CollatzResearch.WordTrace tailWord_5537503 prefixEnd_5537503 2843400664714153227745993 := by
  unfold tailWord_5537503
  simp only [CollatzResearch.WordTrace]
  refine ⟨201969326857579836064081163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134646217905053224042720775 201969326857579836064081163)
  ·
    refine ⟨302953990286369754096121745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201969326857579836064081163 302953990286369754096121745)
    ·
      refine ⟨227215492714777315572091309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302953990286369754096121745 227215492714777315572091309)
      ·
        refine ⟨85205809768041493339534241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227215492714777315572091309 85205809768041493339534241)
        ·
          refine ⟨63904357326031120004650681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85205809768041493339534241 63904357326031120004650681)
          ·
            refine ⟨47928267994523340003488011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63904357326031120004650681 47928267994523340003488011)
            ·
              refine ⟨71892401991785010005232017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47928267994523340003488011 71892401991785010005232017)
              ·
                refine ⟨53919301493838757503924013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71892401991785010005232017 53919301493838757503924013)
                ·
                  refine ⟨20219738060189534063971505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53919301493838757503924013 20219738060189534063971505)
                  ·
                    refine ⟨15164803545142150547978629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20219738060189534063971505 15164803545142150547978629)
                    ·
                      refine ⟨2843400664714153227745993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15164803545142150547978629 2843400664714153227745993)
                      ·
                        rfl

theorem cell23_5537503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_5537503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537503 prefixEnd_5537503 := by exact prefixLift 5537503
  have htrace : WordTrace (prefixWord ++ tailWord_5537503) baseStart_5537503 baseEnd_5537503 := by
    simpa [prefixWord, tailWord_5537503, baseEnd_5537503] using wordTrace_append hprefix tailTrace_5537503
  have hstable : (prefixWord ++ tailWord_5537503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537503).length < 2 ^ (prefixWord ++ tailWord_5537503).sum := by decide
  have hdescent : baseEnd_5537503 < baseStart_5537503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537517 : List Nat := [1, 5, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_5537517 : Nat := 118140960795 + 5537517 * 2 ^ 59
def prefixEnd_5537517 : Nat := 4983230072969 + 3 ^ 40 * 5537517 * 2
def baseEnd_5537517 : Nat := 947802617814438724323643

theorem tailTrace_5537517 : CollatzResearch.WordTrace tailWord_5537517 prefixEnd_5537517 947802617814438724323643 := by
  unfold tailWord_5537517
  simp only [CollatzResearch.WordTrace]
  refine ⟨201969837479529116455090805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134646558319686077636727203 201969837479529116455090805)
  ·
    refine ⟨18934672263705854667664763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201969837479529116455090805 18934672263705854667664763)
    ·
      refine ⟨28402008395558782001497145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18934672263705854667664763 28402008395558782001497145)
      ·
        refine ⟨21301506296669086501122859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28402008395558782001497145 21301506296669086501122859)
        ·
          refine ⟨31952259445003629751684289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21301506296669086501122859 31952259445003629751684289)
          ·
            refine ⟨23964194583752722313763217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31952259445003629751684289 23964194583752722313763217)
            ·
              refine ⟨17973145937814541735322413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23964194583752722313763217 17973145937814541735322413)
              ·
                refine ⟨6739929726680453150745905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17973145937814541735322413 6739929726680453150745905)
                ·
                  refine ⟨5054947295010339863059429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6739929726680453150745905 5054947295010339863059429)
                  ·
                    refine ⟨947802617814438724323643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5054947295010339863059429 947802617814438724323643)
                    ·
                      rfl

theorem cell23_5537517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_5537517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537517 prefixEnd_5537517 := by exact prefixLift 5537517
  have htrace : WordTrace (prefixWord ++ tailWord_5537517) baseStart_5537517 baseEnd_5537517 := by
    simpa [prefixWord, tailWord_5537517, baseEnd_5537517] using wordTrace_append hprefix tailTrace_5537517
  have hstable : (prefixWord ++ tailWord_5537517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537517).length < 2 ^ (prefixWord ++ tailWord_5537517).sum := by decide
  have hdescent : baseEnd_5537517 < baseStart_5537517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537524 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5537524 : Nat := 118140960795 + 5537524 * 2 ^ 59
def prefixEnd_5537524 : Nat := 4983230072969 + 3 ^ 40 * 5537524 * 2
def baseEnd_5537524 : Nat := 2843411447807897645583397

theorem tailTrace_5537524 : CollatzResearch.WordTrace tailWord_5537524 prefixEnd_5537524 2843411447807897645583397 := by
  unfold tailWord_5537524
  simp only [CollatzResearch.WordTrace]
  refine ⟨100985046395251878325297813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134646728527002504433730417 100985046395251878325297813)
  ·
    refine ⟨4733674049777431796498335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100985046395251878325297813 4733674049777431796498335)
    ·
      refine ⟨7100511074666147694747503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4733674049777431796498335 7100511074666147694747503)
      ·
        refine ⟨10650766611999221542121255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7100511074666147694747503 10650766611999221542121255)
        ·
          refine ⟨15976149917998832313181883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10650766611999221542121255 15976149917998832313181883)
          ·
            refine ⟨23964224876998248469772825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15976149917998832313181883 23964224876998248469772825)
            ·
              refine ⟨17973168657748686352329619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23964224876998248469772825 17973168657748686352329619)
              ·
                refine ⟨26959752986623029528494429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17973168657748686352329619 26959752986623029528494429)
                ·
                  refine ⟨10109907369983636073185411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26959752986623029528494429 10109907369983636073185411)
                  ·
                    refine ⟨15164861054975454109778117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10109907369983636073185411 15164861054975454109778117)
                    ·
                      refine ⟨2843411447807897645583397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15164861054975454109778117 2843411447807897645583397)
                      ·
                        rfl

theorem cell23_5537524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5537524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537524 prefixEnd_5537524 := by exact prefixLift 5537524
  have htrace : WordTrace (prefixWord ++ tailWord_5537524) baseStart_5537524 baseEnd_5537524 := by
    simpa [prefixWord, tailWord_5537524, baseEnd_5537524] using wordTrace_append hprefix tailTrace_5537524
  have hstable : (prefixWord ++ tailWord_5537524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537524).length < 2 ^ (prefixWord ++ tailWord_5537524).sum := by decide
  have hdescent : baseEnd_5537524 < baseStart_5537524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537557 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_5537557 : Nat := 118140960795 + 5537557 * 2 ^ 59
def prefixEnd_5537557 : Nat := 4983230072969 + 3 ^ 40 * 5537557 * 2
def baseEnd_5537557 : Nat := 2843428392669496016470745

theorem tailTrace_5537557 : CollatzResearch.WordTrace tailWord_5537557 prefixEnd_5537557 2843428392669496016470745 := by
  unfold tailWord_5537557
  simp only [CollatzResearch.WordTrace]
  refine ⟨201971296399384203286546925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134647530932922802191031283 201971296399384203286546925)
  ·
    refine ⟨75739236149769076232455097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201971296399384203286546925 75739236149769076232455097)
    ·
      refine ⟨56804427112326807174341323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75739236149769076232455097 56804427112326807174341323)
      ·
        refine ⟨85206640668490210761511985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56804427112326807174341323 85206640668490210761511985)
        ·
          refine ⟨63904980501367658071133989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85206640668490210761511985 63904980501367658071133989)
          ·
            refine ⟨11982183844006435888337623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63904980501367658071133989 11982183844006435888337623)
            ·
              refine ⟨17973275766009653832506435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11982183844006435888337623 17973275766009653832506435)
              ·
                refine ⟨26959913649014480748759653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17973275766009653832506435 26959913649014480748759653)
                ·
                  refine ⟨5054983809190215140392435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26959913649014480748759653 5054983809190215140392435)
                  ·
                    refine ⟨7582475713785322710588653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5054983809190215140392435 7582475713785322710588653)
                    ·
                      refine ⟨2843428392669496016470745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7582475713785322710588653 2843428392669496016470745)
                      ·
                        rfl

theorem cell23_5537557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_5537557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537557 prefixEnd_5537557 := by exact prefixLift 5537557
  have htrace : WordTrace (prefixWord ++ tailWord_5537557) baseStart_5537557 baseEnd_5537557 := by
    simpa [prefixWord, tailWord_5537557, baseEnd_5537557] using wordTrace_append hprefix tailTrace_5537557
  have hstable : (prefixWord ++ tailWord_5537557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537557).length < 2 ^ (prefixWord ++ tailWord_5537557).sum := by decide
  have hdescent : baseEnd_5537557 < baseStart_5537557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537583 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 5]
def baseStart_5537583 : Nat := 118140960795 + 5537583 * 2 ^ 59
def prefixEnd_5537583 : Nat := 4983230072969 + 3 ^ 40 * 5537583 * 2
def baseEnd_5537583 : Nat := 2843441743166512914745625

theorem tailTrace_5537583 : CollatzResearch.WordTrace tailWord_5537583 prefixEnd_5537583 2843441743166512914745625 := by
  unfold tailWord_5537583
  simp only [CollatzResearch.WordTrace]
  refine ⟨201972244697290009726993403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134648163131526673151328935 201972244697290009726993403)
  ·
    refine ⟨302958367045935014590490105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201972244697290009726993403 302958367045935014590490105)
    ·
      refine ⟨227218775284451260942867579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302958367045935014590490105 227218775284451260942867579)
      ·
        refine ⟨340828162926676891414301369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227218775284451260942867579 340828162926676891414301369)
        ·
          refine ⟨255621122195007668560726027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340828162926676891414301369 255621122195007668560726027)
          ·
            refine ⟨383431683292511502841089041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255621122195007668560726027 383431683292511502841089041)
            ·
              refine ⟨287573762469383627130816781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383431683292511502841089041 287573762469383627130816781)
              ·
                refine ⟨107840160926018860174056293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287573762469383627130816781 107840160926018860174056293)
                ·
                  refine ⟨20220030173628536282635555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107840160926018860174056293 20220030173628536282635555)
                  ·
                    refine ⟨30330045260442804423953333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20220030173628536282635555 30330045260442804423953333)
                    ·
                      refine ⟨2843441743166512914745625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30330045260442804423953333 2843441743166512914745625)
                      ·
                        rfl

theorem cell23_5537583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_5537583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537583 prefixEnd_5537583 := by exact prefixLift 5537583
  have htrace : WordTrace (prefixWord ++ tailWord_5537583) baseStart_5537583 baseEnd_5537583 := by
    simpa [prefixWord, tailWord_5537583, baseEnd_5537583] using wordTrace_append hprefix tailTrace_5537583
  have hstable : (prefixWord ++ tailWord_5537583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537583).length < 2 ^ (prefixWord ++ tailWord_5537583).sum := by decide
  have hdescent : baseEnd_5537583 < baseStart_5537583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537631 : List Nat := [1, 1, 2, 3, 1, 4, 4, 1, 2, 2, 2]
def baseStart_5537631 : Nat := 118140960795 + 5537631 * 2 ^ 59
def prefixEnd_5537631 : Nat := 4983230072969 + 3 ^ 40 * 5537631 * 2
def baseEnd_5537631 : Nat := 2843466390237928726945405

theorem tailTrace_5537631 : CollatzResearch.WordTrace tailWord_5537631 prefixEnd_5537631 2843466390237928726945405 := by
  unfold tailWord_5537631
  simp only [CollatzResearch.WordTrace]
  refine ⟨201973995401116113924740747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134649330267410742616493831 201973995401116113924740747)
  ·
    refine ⟨302960993101674170887111121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201973995401116113924740747 302960993101674170887111121)
    ·
      refine ⟨227220744826255628165333341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302960993101674170887111121 227220744826255628165333341)
      ·
        refine ⟨85207779309845860562000003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227220744826255628165333341 85207779309845860562000003)
        ·
          refine ⟨127811668964768790843000005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85207779309845860562000003 127811668964768790843000005)
          ·
            refine ⟨23964687930894148283062501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127811668964768790843000005 23964687930894148283062501)
            ·
              refine ⟨4493378987042652803074219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23964687930894148283062501 4493378987042652803074219)
              ·
                refine ⟨6740068480563979204611329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4493378987042652803074219 6740068480563979204611329)
                ·
                  refine ⟨5055051360422984403458497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6740068480563979204611329 5055051360422984403458497)
                  ·
                    refine ⟨3791288520317238302593873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5055051360422984403458497 3791288520317238302593873)
                    ·
                      refine ⟨2843466390237928726945405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3791288520317238302593873 2843466390237928726945405)
                      ·
                        rfl

theorem cell23_5537631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_5537631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537631 prefixEnd_5537631 := by exact prefixLift 5537631
  have htrace : WordTrace (prefixWord ++ tailWord_5537631) baseStart_5537631 baseEnd_5537631 := by
    simpa [prefixWord, tailWord_5537631, baseEnd_5537631] using wordTrace_append hprefix tailTrace_5537631
  have hstable : (prefixWord ++ tailWord_5537631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537631).length < 2 ^ (prefixWord ++ tailWord_5537631).sum := by decide
  have hdescent : baseEnd_5537631 < baseStart_5537631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537643 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 7]
def baseStart_5537643 : Nat := 118140960795 + 5537643 * 2 ^ 59
def prefixEnd_5537643 : Nat := 4983230072969 + 3 ^ 40 * 5537643 * 2
def baseEnd_5537643 : Nat := 2843472552005782679995349

theorem tailTrace_5537643 : CollatzResearch.WordTrace tailWord_5537643 prefixEnd_5537643 2843472552005782679995349 := by
  unfold tailWord_5537643
  simp only [CollatzResearch.WordTrace]
  refine ⟨201974433077072639974177583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134649622051381759982785055 201974433077072639974177583)
  ·
    refine ⟨302961649615608959961266375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201974433077072639974177583 302961649615608959961266375)
    ·
      refine ⟨454442474423413439941899563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302961649615608959961266375 454442474423413439941899563)
      ·
        refine ⟨681663711635120159912849345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454442474423413439941899563 681663711635120159912849345)
        ·
          refine ⟨511247783726340119934637009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 681663711635120159912849345 511247783726340119934637009)
          ·
            refine ⟨383435837794755089950977757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511247783726340119934637009 383435837794755089950977757)
            ·
              refine ⟨143788439173033158731616659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383435837794755089950977757 143788439173033158731616659)
              ·
                refine ⟨215682658759549738097424989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143788439173033158731616659 215682658759549738097424989)
                ·
                  refine ⟨80880997034831151786534371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215682658759549738097424989 80880997034831151786534371)
                  ·
                    refine ⟨121321495552246727679801557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80880997034831151786534371 121321495552246727679801557)
                    ·
                      refine ⟨2843472552005782679995349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121321495552246727679801557 2843472552005782679995349)
                      ·
                        rfl

theorem cell23_5537643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_5537643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537643 prefixEnd_5537643 := by exact prefixLift 5537643
  have htrace : WordTrace (prefixWord ++ tailWord_5537643) baseStart_5537643 baseEnd_5537643 := by
    simpa [prefixWord, tailWord_5537643, baseEnd_5537643] using wordTrace_append hprefix tailTrace_5537643
  have hstable : (prefixWord ++ tailWord_5537643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537643).length < 2 ^ (prefixWord ++ tailWord_5537643).sum := by decide
  have hdescent : baseEnd_5537643 < baseStart_5537643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537671 : List Nat := [1, 1, 4, 2, 4, 2, 2, 2, 5]
def baseStart_5537671 : Nat := 118140960795 + 5537671 * 2 ^ 59
def prefixEnd_5537671 : Nat := 4983230072969 + 3 ^ 40 * 5537671 * 2
def baseEnd_5537671 : Nat := 315942992162678730049469

theorem tailTrace_5537671 : CollatzResearch.WordTrace tailWord_5537671 prefixEnd_5537671 315942992162678730049469 := by
  unfold tailWord_5537671
  simp only [CollatzResearch.WordTrace]
  refine ⟨201975454320971200756196867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134650302880647467170797911 201975454320971200756196867)
  ·
    refine ⟨302963181481456801134295301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201975454320971200756196867 302963181481456801134295301)
    ·
      refine ⟨56805596527773150212680369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302963181481456801134295301 56805596527773150212680369)
      ·
        refine ⟨42604197395829862659510277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56805596527773150212680369 42604197395829862659510277)
        ·
          refine ⟨7988287011718099248658177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42604197395829862659510277 7988287011718099248658177)
          ·
            refine ⟨5991215258788574436493633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7988287011718099248658177 5991215258788574436493633)
            ·
              refine ⟨4493411444091430827370225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5991215258788574436493633 4493411444091430827370225)
              ·
                refine ⟨3370058583068573120527669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4493411444091430827370225 3370058583068573120527669)
                ·
                  refine ⟨315942992162678730049469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3370058583068573120527669 315942992162678730049469)
                  ·
                    rfl

theorem cell23_5537671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 5].length) (baseStart_5537671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537671 prefixEnd_5537671 := by exact prefixLift 5537671
  have htrace : WordTrace (prefixWord ++ tailWord_5537671) baseStart_5537671 baseEnd_5537671 := by
    simpa [prefixWord, tailWord_5537671, baseEnd_5537671] using wordTrace_append hprefix tailTrace_5537671
  have hstable : (prefixWord ++ tailWord_5537671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537671).length < 2 ^ (prefixWord ++ tailWord_5537671).sum := by decide
  have hdescent : baseEnd_5537671 < baseStart_5537671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537687 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 1, 6, 2]
def baseStart_5537687 : Nat := 118140960795 + 5537687 * 2 ^ 59
def prefixEnd_5537687 : Nat := 4983230072969 + 3 ^ 40 * 5537687 * 2
def baseEnd_5537687 : Nat := 2843495145154580507845147

theorem tailTrace_5537687 : CollatzResearch.WordTrace tailWord_5537687 prefixEnd_5537687 2843495145154580507845147 := by
  unfold tailWord_5537687
  simp only [CollatzResearch.WordTrace]
  refine ⟨201976037888913235488779315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134650691925942156992519543 201976037888913235488779315)
  ·
    refine ⟨302964056833369853233168973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201976037888913235488779315 302964056833369853233168973)
    ·
      refine ⟨113611521312513694962438365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302964056833369853233168973 113611521312513694962438365)
      ·
        refine ⟨42604320492192635610914387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113611521312513694962438365 42604320492192635610914387)
        ·
          refine ⟨63906480738288953416371581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42604320492192635610914387 63906480738288953416371581)
          ·
            refine ⟨23964930276858357531139343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63906480738288953416371581 23964930276858357531139343)
            ·
              refine ⟨35947395415287536296709015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23964930276858357531139343 35947395415287536296709015)
              ·
                refine ⟨53921093122931304445063523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35947395415287536296709015 53921093122931304445063523)
                ·
                  refine ⟨80881639684396956667595285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53921093122931304445063523 80881639684396956667595285)
                  ·
                    refine ⟨3791326860206107343793529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80881639684396956667595285 3791326860206107343793529)
                    ·
                      refine ⟨2843495145154580507845147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3791326860206107343793529 2843495145154580507845147)
                      ·
                        rfl

theorem cell23_5537687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_5537687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537687 prefixEnd_5537687 := by exact prefixLift 5537687
  have htrace : WordTrace (prefixWord ++ tailWord_5537687) baseStart_5537687 baseEnd_5537687 := by
    simpa [prefixWord, tailWord_5537687, baseEnd_5537687] using wordTrace_append hprefix tailTrace_5537687
  have hstable : (prefixWord ++ tailWord_5537687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537687).length < 2 ^ (prefixWord ++ tailWord_5537687).sum := by decide
  have hdescent : baseEnd_5537687 < baseStart_5537687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537737 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 7, 1, 3]
def baseStart_5537737 : Nat := 118140960795 + 5537737 * 2 ^ 59
def prefixEnd_5537737 : Nat := 4983230072969 + 3 ^ 40 * 5537737 * 2
def baseEnd_5537737 : Nat := 2843520819187305312219917

theorem tailTrace_5537737 : CollatzResearch.WordTrace tailWord_5537737 prefixEnd_5537737 2843520819187305312219917 := by
  unfold tailWord_5537737
  simp only [CollatzResearch.WordTrace]
  refine ⟨201977861538732094028099465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134651907692488062685399643 201977861538732094028099465)
  ·
    refine ⟨151483396154049070521074599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201977861538732094028099465 151483396154049070521074599)
    ·
      refine ⟨227225094231073605781611899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151483396154049070521074599 227225094231073605781611899)
      ·
        refine ⟨340837641346610408672417849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227225094231073605781611899 340837641346610408672417849)
        ·
          refine ⟨255628231009957806504313387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340837641346610408672417849 255628231009957806504313387)
          ·
            refine ⟨383442346514936709756470081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255628231009957806504313387 383442346514936709756470081)
            ·
              refine ⟨287581759886202532317352561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383442346514936709756470081 287581759886202532317352561)
              ·
                refine ⟨215686319914651899238014421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287581759886202532317352561 215686319914651899238014421)
                ·
                  refine ⟨5055148122999653888390963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 215686319914651899238014421 5055148122999653888390963)
                  ·
                    refine ⟨7582722184499480832586445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5055148122999653888390963 7582722184499480832586445)
                    ·
                      refine ⟨2843520819187305312219917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7582722184499480832586445 2843520819187305312219917)
                      ·
                        rfl

theorem cell23_5537737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 1, 3].length) (baseStart_5537737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537737 prefixEnd_5537737 := by exact prefixLift 5537737
  have htrace : WordTrace (prefixWord ++ tailWord_5537737) baseStart_5537737 baseEnd_5537737 := by
    simpa [prefixWord, tailWord_5537737, baseEnd_5537737] using wordTrace_append hprefix tailTrace_5537737
  have hstable : (prefixWord ++ tailWord_5537737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537737).length < 2 ^ (prefixWord ++ tailWord_5537737).sum := by decide
  have hdescent : baseEnd_5537737 < baseStart_5537737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537760 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 4]
def baseStart_5537760 : Nat := 118140960795 + 5537760 * 2 ^ 59
def prefixEnd_5537760 : Nat := 4983230072969 + 3 ^ 40 * 5537760 * 2
def baseEnd_5537760 : Nat := 2843532629242358722232311

theorem tailTrace_5537760 : CollatzResearch.WordTrace tailWord_5537760 prefixEnd_5537760 2843532629242358722232311 := by
  unfold tailWord_5537760
  simp only [CollatzResearch.WordTrace]
  refine ⟨100989350208824384478093367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134652466945099179304124489 100989350208824384478093367)
  ·
    refine ⟨151484025313236576717140051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100989350208824384478093367 151484025313236576717140051)
    ·
      refine ⟨227226037969854865075710077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151484025313236576717140051 227226037969854865075710077)
      ·
        refine ⟨85209764238695574403391279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227226037969854865075710077 85209764238695574403391279)
        ·
          refine ⟨127814646358043361605086919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85209764238695574403391279 127814646358043361605086919)
          ·
            refine ⟨191721969537065042407630379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127814646358043361605086919 191721969537065042407630379)
            ·
              refine ⟨287582954305597563611445569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191721969537065042407630379 287582954305597563611445569)
              ·
                refine ⟨215687215729198172708584177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287582954305597563611445569 215687215729198172708584177)
                ·
                  refine ⟨161765411796898629531438133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215687215729198172708584177 161765411796898629531438133)
                  ·
                    refine ⟨15165507355959246518572325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 161765411796898629531438133 15165507355959246518572325)
                    ·
                      refine ⟨2843532629242358722232311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15165507355959246518572325 2843532629242358722232311)
                      ·
                        rfl

theorem cell23_5537760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_5537760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537760 prefixEnd_5537760 := by exact prefixLift 5537760
  have htrace : WordTrace (prefixWord ++ tailWord_5537760) baseStart_5537760 baseEnd_5537760 := by
    simpa [prefixWord, tailWord_5537760, baseEnd_5537760] using wordTrace_append hprefix tailTrace_5537760
  have hstable : (prefixWord ++ tailWord_5537760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537760).length < 2 ^ (prefixWord ++ tailWord_5537760).sum := by decide
  have hdescent : baseEnd_5537760 < baseStart_5537760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537764 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 2, 3, 2]
def baseStart_5537764 : Nat := 118140960795 + 5537764 * 2 ^ 59
def prefixEnd_5537764 : Nat := 4983230072969 + 3 ^ 40 * 5537764 * 2
def baseEnd_5537764 : Nat := 2843534683164976706582293

theorem tailTrace_5537764 : CollatzResearch.WordTrace tailWord_5537764 prefixEnd_5537764 2843534683164976706582293 := by
  unfold tailWord_5537764
  simp only [CollatzResearch.WordTrace]
  refine ⟨100989423154817138819666173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134652564206422851759554897 100989423154817138819666173)
  ·
    refine ⟨37871033683056427057374815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100989423154817138819666173 37871033683056427057374815)
    ·
      refine ⟨56806550524584640586062223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37871033683056427057374815 56806550524584640586062223)
      ·
        refine ⟨85209825786876960879093335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56806550524584640586062223 85209825786876960879093335)
        ·
          refine ⟨127814738680315441318640003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85209825786876960879093335 127814738680315441318640003)
          ·
            refine ⟨191722108020473161977960005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127814738680315441318640003 191722108020473161977960005)
            ·
              refine ⟨35947895253838717870867501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191722108020473161977960005 35947895253838717870867501)
              ·
                refine ⟨13480460720189519201575313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35947895253838717870867501 13480460720189519201575313)
                ·
                  refine ⟨10110345540142139401181485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13480460720189519201575313 10110345540142139401181485)
                  ·
                    refine ⟨3791379577553302275443057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10110345540142139401181485 3791379577553302275443057)
                    ·
                      refine ⟨2843534683164976706582293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3791379577553302275443057 2843534683164976706582293)
                      ·
                        rfl

theorem cell23_5537764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_5537764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537764 prefixEnd_5537764 := by exact prefixLift 5537764
  have htrace : WordTrace (prefixWord ++ tailWord_5537764) baseStart_5537764 baseEnd_5537764 := by
    simpa [prefixWord, tailWord_5537764, baseEnd_5537764] using wordTrace_append hprefix tailTrace_5537764
  have hstable : (prefixWord ++ tailWord_5537764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537764).length < 2 ^ (prefixWord ++ tailWord_5537764).sum := by decide
  have hdescent : baseEnd_5537764 < baseStart_5537764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537774 : List Nat := [4, 1, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_5537774 : Nat := 118140960795 + 5537774 * 2 ^ 59
def prefixEnd_5537774 : Nat := 4983230072969 + 3 ^ 40 * 5537774 * 2
def baseEnd_5537774 : Nat := 947846605990507222485749

theorem tailTrace_5537774 : CollatzResearch.WordTrace tailWord_5537774 prefixEnd_5537774 947846605990507222485749 := by
  unfold tailWord_5537774
  simp only [CollatzResearch.WordTrace]
  refine ⟨25247401379949756168399547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134652807359732032898130917 25247401379949756168399547)
  ·
    refine ⟨37871102069924634252599321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25247401379949756168399547 37871102069924634252599321)
    ·
      refine ⟨28403326552443475689449491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37871102069924634252599321 28403326552443475689449491)
      ·
        refine ⟨42604989828665213534174237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28403326552443475689449491 42604989828665213534174237)
        ·
          refine ⟨15976871185749455075315339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42604989828665213534174237 15976871185749455075315339)
          ·
            refine ⟨23965306778624182612973009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15976871185749455075315339 23965306778624182612973009)
            ·
              refine ⟨17973980083968136959729757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23965306778624182612973009 17973980083968136959729757)
              ·
                refine ⟨6740242531488051359898659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17973980083968136959729757 6740242531488051359898659)
                ·
                  refine ⟨10110363797232077039847989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6740242531488051359898659 10110363797232077039847989)
                  ·
                    refine ⟨947846605990507222485749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10110363797232077039847989 947846605990507222485749)
                    ·
                      rfl

theorem cell23_5537774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_5537774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537774 prefixEnd_5537774 := by exact prefixLift 5537774
  have htrace : WordTrace (prefixWord ++ tailWord_5537774) baseStart_5537774 baseEnd_5537774 := by
    simpa [prefixWord, tailWord_5537774, baseEnd_5537774] using wordTrace_append hprefix tailTrace_5537774
  have hstable : (prefixWord ++ tailWord_5537774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537774).length < 2 ^ (prefixWord ++ tailWord_5537774).sum := by decide
  have hdescent : baseEnd_5537774 < baseStart_5537774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537787 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 4, 4]
def baseStart_5537787 : Nat := 118140960795 + 5537787 * 2 ^ 59
def prefixEnd_5537787 : Nat := 4983230072969 + 3 ^ 40 * 5537787 * 2
def baseEnd_5537787 : Nat := 947848831073343372198229

theorem tailTrace_5537787 : CollatzResearch.WordTrace tailWord_5537787 prefixEnd_5537787 947848831073343372198229 := by
  unfold tailWord_5537787
  simp only [CollatzResearch.WordTrace]
  refine ⟨201979685188550952567419615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134653123459033968378279743 201979685188550952567419615)
  ·
    refine ⟨302969527782826428851129423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201979685188550952567419615 302969527782826428851129423)
    ·
      refine ⟨454454291674239643276694135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302969527782826428851129423 454454291674239643276694135)
      ·
        refine ⟨681681437511359464915041203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454454291674239643276694135 681681437511359464915041203)
        ·
          refine ⟨1022522156267039197372561805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681681437511359464915041203 1022522156267039197372561805)
          ·
            refine ⟨383445808600139699014710677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1022522156267039197372561805 383445808600139699014710677)
            ·
              refine ⟨17974022278131548391314563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 383445808600139699014710677 17974022278131548391314563)
              ·
                refine ⟨26961033417197322586971845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17974022278131548391314563 26961033417197322586971845)
                ·
                  refine ⟨5055193765724497985057221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26961033417197322586971845 5055193765724497985057221)
                  ·
                    refine ⟨947848831073343372198229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5055193765724497985057221 947848831073343372198229)
                    ·
                      rfl

theorem cell23_5537787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 4].length) (baseStart_5537787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537787 prefixEnd_5537787 := by exact prefixLift 5537787
  have htrace : WordTrace (prefixWord ++ tailWord_5537787) baseStart_5537787 baseEnd_5537787 := by
    simpa [prefixWord, tailWord_5537787, baseEnd_5537787] using wordTrace_append hprefix tailTrace_5537787
  have hstable : (prefixWord ++ tailWord_5537787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537787).length < 2 ^ (prefixWord ++ tailWord_5537787).sum := by decide
  have hdescent : baseEnd_5537787 < baseStart_5537787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537788 : List Nat := [2, 2, 2, 1, 2, 2, 5, 2, 1, 1, 3]
def baseStart_5537788 : Nat := 118140960795 + 5537788 * 2 ^ 59
def prefixEnd_5537788 : Nat := 4983230072969 + 3 ^ 40 * 5537788 * 2
def baseEnd_5537788 : Nat := 2843547006700684612682183

theorem tailTrace_5537788 : CollatzResearch.WordTrace tailWord_5537788 prefixEnd_5537788 2843547006700684612682183 := by
  unfold tailWord_5537788
  simp only [CollatzResearch.WordTrace]
  refine ⟨100989860830773664869103009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134653147774364886492137345 100989860830773664869103009)
  ·
    refine ⟨75742395623080248651827257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100989860830773664869103009 75742395623080248651827257)
    ·
      refine ⟨56806796717310186488870443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75742395623080248651827257 56806796717310186488870443)
      ·
        refine ⟨85210195075965279733305665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56806796717310186488870443 85210195075965279733305665)
        ·
          refine ⟨63907646306973959799979249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85210195075965279733305665 63907646306973959799979249)
          ·
            refine ⟨47930734730230469849984437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63907646306973959799979249 47930734730230469849984437)
            ·
              refine ⟨4493506380959106548436041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47930734730230469849984437 4493506380959106548436041)
              ·
                refine ⟨3370129785719329911327031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4493506380959106548436041 3370129785719329911327031)
                ·
                  refine ⟨5055194678578994866990547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3370129785719329911327031 5055194678578994866990547)
                  ·
                    refine ⟨7582792017868492300485821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5055194678578994866990547 7582792017868492300485821)
                    ·
                      refine ⟨2843547006700684612682183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7582792017868492300485821 2843547006700684612682183)
                      ·
                        rfl

theorem cell23_5537788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_5537788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537788 prefixEnd_5537788 := by exact prefixLift 5537788
  have htrace : WordTrace (prefixWord ++ tailWord_5537788) baseStart_5537788 baseEnd_5537788 := by
    simpa [prefixWord, tailWord_5537788, baseEnd_5537788] using wordTrace_append hprefix tailTrace_5537788
  have hstable : (prefixWord ++ tailWord_5537788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537788).length < 2 ^ (prefixWord ++ tailWord_5537788).sum := by decide
  have hdescent : baseEnd_5537788 < baseStart_5537788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537797 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_5537797 : Nat := 118140960795 + 5537797 * 2 ^ 59
def prefixEnd_5537797 : Nat := 4983230072969 + 3 ^ 40 * 5537797 * 2
def baseEnd_5537797 : Nat := 2843551628026575077469641

theorem tailTrace_5537797 : CollatzResearch.WordTrace tailWord_5537797 prefixEnd_5537797 2843551628026575077469641 := by
  unfold tailWord_5537797
  simp only [CollatzResearch.WordTrace]
  refine ⟨201980049918514724275283645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134653366612343149516855763 201980049918514724275283645)
  ·
    refine ⟨75742518719443021603231367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201980049918514724275283645 75742518719443021603231367)
    ·
      refine ⟨113613778079164532404847051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75742518719443021603231367 113613778079164532404847051)
      ·
        refine ⟨170420667118746798607270577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113613778079164532404847051 170420667118746798607270577)
        ·
          refine ⟨127815500339060098955452933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170420667118746798607270577 127815500339060098955452933)
          ·
            refine ⟨23965406313573768554147425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127815500339060098955452933 23965406313573768554147425)
            ·
              refine ⟨17974054735180326415610569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23965406313573768554147425 17974054735180326415610569)
              ·
                refine ⟨13480541051385244811707927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17974054735180326415610569 13480541051385244811707927)
                ·
                  refine ⟨20220811577077867217561891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13480541051385244811707927 20220811577077867217561891)
                  ·
                    refine ⟨30331217365616800826342837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20220811577077867217561891 30331217365616800826342837)
                    ·
                      refine ⟨2843551628026575077469641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30331217365616800826342837 2843551628026575077469641)
                      ·
                        rfl

theorem cell23_5537797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_5537797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537797 prefixEnd_5537797 := by exact prefixLift 5537797
  have htrace : WordTrace (prefixWord ++ tailWord_5537797) baseStart_5537797 baseEnd_5537797 := by
    simpa [prefixWord, tailWord_5537797, baseEnd_5537797] using wordTrace_append hprefix tailTrace_5537797
  have hstable : (prefixWord ++ tailWord_5537797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537797).length < 2 ^ (prefixWord ++ tailWord_5537797).sum := by decide
  have hdescent : baseEnd_5537797 < baseStart_5537797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537804 : List Nat := [2, 2, 1, 2, 3, 1, 3, 3, 2, 4]
def baseStart_5537804 : Nat := 118140960795 + 5537804 * 2 ^ 59
def prefixEnd_5537804 : Nat := 4983230072969 + 3 ^ 40 * 5537804 * 2
def baseEnd_5537804 : Nat := 947851740797052183360703

theorem tailTrace_5537804 : CollatzResearch.WordTrace tailWord_5537804 prefixEnd_5537804 947851740797052183360703 := by
  unfold tailWord_5537804
  simp only [CollatzResearch.WordTrace]
  refine ⟨100990152614744682235394233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134653536819659576313858977 100990152614744682235394233)
  ·
    refine ⟨75742614461058511676545675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100990152614744682235394233 75742614461058511676545675)
    ·
      refine ⟨113613921691587767514818513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75742614461058511676545675 113613921691587767514818513)
      ·
        refine ⟨85210441268690825636113885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113613921691587767514818513 85210441268690825636113885)
        ·
          refine ⟨31953915475759059613542707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85210441268690825636113885 31953915475759059613542707)
          ·
            refine ⟨47930873213638589420314061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31953915475759059613542707 47930873213638589420314061)
            ·
              refine ⟨17974077455114471032617773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47930873213638589420314061 17974077455114471032617773)
              ·
                refine ⟨6740279045667926637231665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17974077455114471032617773 6740279045667926637231665)
                ·
                  refine ⟨5055209284250944977923749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6740279045667926637231665 5055209284250944977923749)
                  ·
                    refine ⟨947851740797052183360703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5055209284250944977923749 947851740797052183360703)
                    ·
                      rfl

theorem cell23_5537804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_5537804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537804 prefixEnd_5537804 := by exact prefixLift 5537804
  have htrace : WordTrace (prefixWord ++ tailWord_5537804) baseStart_5537804 baseEnd_5537804 := by
    simpa [prefixWord, tailWord_5537804, baseEnd_5537804] using wordTrace_append hprefix tailTrace_5537804
  have hstable : (prefixWord ++ tailWord_5537804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537804).length < 2 ^ (prefixWord ++ tailWord_5537804).sum := by decide
  have hdescent : baseEnd_5537804 < baseStart_5537804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537828 : List Nat := [2, 3, 1, 4, 2, 1, 3, 1, 1, 1, 4]
def baseStart_5537828 : Nat := 118140960795 + 5537828 * 2 ^ 59
def prefixEnd_5537828 : Nat := 4983230072969 + 3 ^ 40 * 5537828 * 2
def baseEnd_5537828 : Nat := 2843567545926864456181999

theorem tailTrace_5537828 : CollatzResearch.WordTrace tailWord_5537828 prefixEnd_5537828 2843567545926864456181999 := by
  unfold tailWord_5537828
  simp only [CollatzResearch.WordTrace]
  refine ⟨100990590290701208284831069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134654120387601611046441425 100990590290701208284831069)
  ·
    refine ⟨37871471359012953106811651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100990590290701208284831069 37871471359012953106811651)
    ·
      refine ⟨56807207038519429660217477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37871471359012953106811651 56807207038519429660217477)
      ·
        refine ⟨10651351319722393061290777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56807207038519429660217477 10651351319722393061290777)
        ·
          refine ⟨7988513489791794795968083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10651351319722393061290777 7988513489791794795968083)
          ·
            refine ⟨11982770234687692193952125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7988513489791794795968083 11982770234687692193952125)
            ·
              refine ⟨4493538838007884572732047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11982770234687692193952125 4493538838007884572732047)
              ·
                refine ⟨6740308257011826859098071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4493538838007884572732047 6740308257011826859098071)
                ·
                  refine ⟨10110462385517740288647107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6740308257011826859098071 10110462385517740288647107)
                  ·
                    refine ⟨15165693578276610432970661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10110462385517740288647107 15165693578276610432970661)
                    ·
                      refine ⟨2843567545926864456181999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15165693578276610432970661 2843567545926864456181999)
                      ·
                        rfl

theorem cell23_5537828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_5537828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537828 prefixEnd_5537828 := by exact prefixLift 5537828
  have htrace : WordTrace (prefixWord ++ tailWord_5537828) baseStart_5537828 baseEnd_5537828 := by
    simpa [prefixWord, tailWord_5537828, baseEnd_5537828] using wordTrace_append hprefix tailTrace_5537828
  have hstable : (prefixWord ++ tailWord_5537828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537828).length < 2 ^ (prefixWord ++ tailWord_5537828).sum := by decide
  have hdescent : baseEnd_5537828 < baseStart_5537828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537845 : List Nat := [1, 3, 3, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_5537845 : Nat := 118140960795 + 5537845 * 2 ^ 59
def prefixEnd_5537845 : Nat := 4983230072969 + 3 ^ 40 * 5537845 * 2
def baseEnd_5537845 : Nat := 2843576275097990889669421

theorem tailTrace_5537845 : CollatzResearch.WordTrace tailWord_5537845 prefixEnd_5537845 2843576275097990889669421 := by
  unfold tailWord_5537845
  simp only [CollatzResearch.WordTrace]
  refine ⟨201981800622340828473030989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134654533748227218982020659 201981800622340828473030989)
  ·
    refine ⟨75743175233377810677386621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201981800622340828473030989 75743175233377810677386621)
    ·
      refine ⟨28403690712516679004019983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75743175233377810677386621 28403690712516679004019983)
      ·
        refine ⟨42605536068775018506029975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28403690712516679004019983 42605536068775018506029975)
        ·
          refine ⟨63908304103162527759044963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42605536068775018506029975 63908304103162527759044963)
          ·
            refine ⟨95862456154743791638567445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63908304103162527759044963 95862456154743791638567445)
            ·
              refine ⟨4493552632253615233057849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95862456154743791638567445 4493552632253615233057849)
              ·
                refine ⟨3370164474190211424793387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4493552632253615233057849 3370164474190211424793387)
                ·
                  refine ⟨5055246711285317137190081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3370164474190211424793387 5055246711285317137190081)
                  ·
                    refine ⟨3791435033463987852892561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5055246711285317137190081 3791435033463987852892561)
                    ·
                      refine ⟨2843576275097990889669421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3791435033463987852892561 2843576275097990889669421)
                      ·
                        rfl

theorem cell23_5537845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_5537845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537845 prefixEnd_5537845 := by exact prefixLift 5537845
  have htrace : WordTrace (prefixWord ++ tailWord_5537845) baseStart_5537845 baseEnd_5537845 := by
    simpa [prefixWord, tailWord_5537845, baseEnd_5537845] using wordTrace_append hprefix tailTrace_5537845
  have hstable : (prefixWord ++ tailWord_5537845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537845).length < 2 ^ (prefixWord ++ tailWord_5537845).sum := by decide
  have hdescent : baseEnd_5537845 < baseStart_5537845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537878 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_5537878 : Nat := 118140960795 + 5537878 * 2 ^ 59
def prefixEnd_5537878 : Nat := 4983230072969 + 3 ^ 40 * 5537878 * 2
def baseEnd_5537878 : Nat := 2843593219959589260556769

theorem tailTrace_5537878 : CollatzResearch.WordTrace tailWord_5537878 prefixEnd_5537878 2843593219959589260556769 := by
  unfold tailWord_5537878
  simp only [CollatzResearch.WordTrace]
  refine ⟨12623937764451329694311393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134655336154147516739321525 12623937764451329694311393)
  ·
    refine ⟨9467953323338497270733545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12623937764451329694311393 9467953323338497270733545)
    ·
      refine ⟨7100964992503872953050159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9467953323338497270733545 7100964992503872953050159)
      ·
        refine ⟨10651447488755809429575239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7100964992503872953050159 10651447488755809429575239)
        ·
          refine ⟨15977171233133714144362859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10651447488755809429575239 15977171233133714144362859)
          ·
            refine ⟨23965756849700571216544289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15977171233133714144362859 23965756849700571216544289)
            ·
              refine ⟨17974317637275428412408217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23965756849700571216544289 17974317637275428412408217)
              ·
                refine ⟨13480738227956571309306163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17974317637275428412408217 13480738227956571309306163)
                ·
                  refine ⟨20221107341934856963959245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13480738227956571309306163 20221107341934856963959245)
                  ·
                    refine ⟨7582915253225571361484717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20221107341934856963959245 7582915253225571361484717)
                    ·
                      refine ⟨2843593219959589260556769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7582915253225571361484717 2843593219959589260556769)
                      ·
                        rfl

theorem cell23_5537878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_5537878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537878 prefixEnd_5537878 := by exact prefixLift 5537878
  have htrace : WordTrace (prefixWord ++ tailWord_5537878) baseStart_5537878 baseEnd_5537878 := by
    simpa [prefixWord, tailWord_5537878, baseEnd_5537878] using wordTrace_append hprefix tailTrace_5537878
  have hstable : (prefixWord ++ tailWord_5537878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537878).length < 2 ^ (prefixWord ++ tailWord_5537878).sum := by decide
  have hdescent : baseEnd_5537878 < baseStart_5537878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537887 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 3]
def baseStart_5537887 : Nat := 118140960795 + 5537887 * 2 ^ 59
def prefixEnd_5537887 : Nat := 4983230072969 + 3 ^ 40 * 5537887 * 2
def baseEnd_5537887 : Nat := 2843597841285479725344227

theorem tailTrace_5537887 : CollatzResearch.WordTrace tailWord_5537887 prefixEnd_5537887 2843597841285479725344227 := by
  unfold tailWord_5537887
  simp only [CollatzResearch.WordTrace]
  refine ⟨201983332488188669646059915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134655554992125779764039943 201983332488188669646059915)
  ·
    refine ⟨302974998732283004469089873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201983332488188669646059915 302974998732283004469089873)
    ·
      refine ⟨227231249049212253351817405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302974998732283004469089873 227231249049212253351817405)
      ·
        refine ⟨85211718393454595006931527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227231249049212253351817405 85211718393454595006931527)
        ·
          refine ⟨127817577590181892510397291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85211718393454595006931527 127817577590181892510397291)
          ·
            refine ⟨191726366385272838765595937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127817577590181892510397291 191726366385272838765595937)
            ·
              refine ⟨143794774788954629074196953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191726366385272838765595937 143794774788954629074196953)
              ·
                refine ⟨107846081091715971805647715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143794774788954629074196953 107846081091715971805647715)
                ·
                  refine ⟨161769121637573957708471573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107846081091715971805647715 161769121637573957708471573)
                  ·
                    refine ⟨7582927576761279267584605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 161769121637573957708471573 7582927576761279267584605)
                    ·
                      refine ⟨2843597841285479725344227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7582927576761279267584605 2843597841285479725344227)
                      ·
                        rfl

theorem cell23_5537887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_5537887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537887 prefixEnd_5537887 := by exact prefixLift 5537887
  have htrace : WordTrace (prefixWord ++ tailWord_5537887) baseStart_5537887 baseEnd_5537887 := by
    simpa [prefixWord, tailWord_5537887, baseEnd_5537887] using wordTrace_append hprefix tailTrace_5537887
  have hstable : (prefixWord ++ tailWord_5537887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537887).length < 2 ^ (prefixWord ++ tailWord_5537887).sum := by decide
  have hdescent : baseEnd_5537887 < baseStart_5537887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537888 : List Nat := [2, 1, 1, 3, 2, 3, 4, 1, 1, 3, 2]
def baseStart_5537888 : Nat := 118140960795 + 5537888 * 2 ^ 59
def prefixEnd_5537888 : Nat := 4983230072969 + 3 ^ 40 * 5537888 * 2
def baseEnd_5537888 : Nat := 2843598354766134221431723

theorem tailTrace_5537888 : CollatzResearch.WordTrace tailWord_5537888 prefixEnd_5537888 2843598354766134221431723 := by
  unfold tailWord_5537888
  simp only [CollatzResearch.WordTrace]
  refine ⟨100991684480592523408423159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134655579307456697877897545 100991684480592523408423159)
  ·
    refine ⟨151487526720888785112634739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100991684480592523408423159 151487526720888785112634739)
    ·
      refine ⟨227231290081333177668952109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151487526720888785112634739 227231290081333177668952109)
      ·
        refine ⟨85211733780499941625857041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227231290081333177668952109 85211733780499941625857041)
        ·
          refine ⟨63908800335374956219392781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85211733780499941625857041 63908800335374956219392781)
          ·
            refine ⟨23965800125765608582272293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63908800335374956219392781 23965800125765608582272293)
            ·
              refine ⟨4493587523581051609176055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23965800125765608582272293 4493587523581051609176055)
              ·
                refine ⟨6740381285371577413764083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4493587523581051609176055 6740381285371577413764083)
                ·
                  refine ⟨10110571928057366120646125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6740381285371577413764083 10110571928057366120646125)
                  ·
                    refine ⟨3791464473021512295242297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10110571928057366120646125 3791464473021512295242297)
                    ·
                      refine ⟨2843598354766134221431723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3791464473021512295242297 2843598354766134221431723)
                      ·
                        rfl

theorem cell23_5537888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_5537888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537888 prefixEnd_5537888 := by exact prefixLift 5537888
  have htrace : WordTrace (prefixWord ++ tailWord_5537888) baseStart_5537888 baseEnd_5537888 := by
    simpa [prefixWord, tailWord_5537888, baseEnd_5537888] using wordTrace_append hprefix tailTrace_5537888
  have hstable : (prefixWord ++ tailWord_5537888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537888).length < 2 ^ (prefixWord ++ tailWord_5537888).sum := by decide
  have hdescent : baseEnd_5537888 < baseStart_5537888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537897 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 4, 2, 4]
def baseStart_5537897 : Nat := 118140960795 + 5537897 * 2 ^ 59
def prefixEnd_5537897 : Nat := 4983230072969 + 3 ^ 40 * 5537897 * 2
def baseEnd_5537897 : Nat := 2843602976092024686219181

theorem tailTrace_5537897 : CollatzResearch.WordTrace tailWord_5537897 prefixEnd_5537897 2843602976092024686219181 := by
  unfold tailWord_5537897
  simp only [CollatzResearch.WordTrace]
  refine ⟨201983697218152441353923945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134655798145434960902615963 201983697218152441353923945)
  ·
    refine ⟨151487772913614331015442959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201983697218152441353923945 151487772913614331015442959)
    ·
      refine ⟨227231659370421496523164439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151487772913614331015442959 227231659370421496523164439)
      ·
        refine ⟨340847489055632244784746659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227231659370421496523164439 340847489055632244784746659)
        ·
          refine ⟨511271233583448367177119989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340847489055632244784746659 511271233583448367177119989)
          ·
            refine ⟨47931678148448284422854999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 511271233583448367177119989 47931678148448284422854999)
            ·
              refine ⟨71897517222672426634282499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47931678148448284422854999 71897517222672426634282499)
              ·
                refine ⟨107846275834008639951423749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71897517222672426634282499 107846275834008639951423749)
                ·
                  refine ⟨20221176718876619990891953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107846275834008639951423749 20221176718876619990891953)
                  ·
                    refine ⟨15165882539157464993168965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20221176718876619990891953 15165882539157464993168965)
                    ·
                      refine ⟨2843602976092024686219181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15165882539157464993168965 2843602976092024686219181)
                      ·
                        rfl

theorem cell23_5537897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_5537897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537897 prefixEnd_5537897 := by exact prefixLift 5537897
  have htrace : WordTrace (prefixWord ++ tailWord_5537897) baseStart_5537897 baseEnd_5537897 := by
    simpa [prefixWord, tailWord_5537897, baseEnd_5537897] using wordTrace_append hprefix tailTrace_5537897
  have hstable : (prefixWord ++ tailWord_5537897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537897).length < 2 ^ (prefixWord ++ tailWord_5537897).sum := by decide
  have hdescent : baseEnd_5537897 < baseStart_5537897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537937 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 8, 5]
def baseStart_5537937 : Nat := 118140960795 + 5537937 * 2 ^ 59
def prefixEnd_5537937 : Nat := 4983230072969 + 3 ^ 40 * 5537937 * 2
def baseEnd_5537937 : Nat := 947874505106068176572999

theorem tailTrace_5537937 : CollatzResearch.WordTrace tailWord_5537937 prefixEnd_5537937 947874505106068176572999 := by
  unfold tailWord_5537937
  simp only [CollatzResearch.WordTrace]
  refine ⟨201985156138007528185380065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134656770758671685456920043 201985156138007528185380065)
  ·
    refine ⟨151488867103505646139035049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201985156138007528185380065 151488867103505646139035049)
    ·
      refine ⟨113616650327629234604276287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151488867103505646139035049 113616650327629234604276287)
      ·
        refine ⟨170424975491443851906414431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113616650327629234604276287 170424975491443851906414431)
        ·
          refine ⟨255637463237165777859621647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170424975491443851906414431 255637463237165777859621647)
          ·
            refine ⟨383456194855748666789432471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255637463237165777859621647 383456194855748666789432471)
            ·
              refine ⟨575184292283623000184148707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383456194855748666789432471 575184292283623000184148707)
              ·
                refine ⟨862776438425434500276223061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575184292283623000184148707 862776438425434500276223061)
                ·
                  refine ⟨10110661387798060550111989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 862776438425434500276223061 10110661387798060550111989)
                  ·
                    refine ⟨947874505106068176572999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10110661387798060550111989 947874505106068176572999)
                    ·
                      rfl

theorem cell23_5537937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_5537937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537937 prefixEnd_5537937 := by exact prefixLift 5537937
  have htrace : WordTrace (prefixWord ++ tailWord_5537937) baseStart_5537937 baseEnd_5537937 := by
    simpa [prefixWord, tailWord_5537937, baseEnd_5537937] using wordTrace_append hprefix tailTrace_5537937
  have hstable : (prefixWord ++ tailWord_5537937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537937).length < 2 ^ (prefixWord ++ tailWord_5537937).sum := by decide
  have hdescent : baseEnd_5537937 < baseStart_5537937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5537969 : List Nat := [1, 2, 2, 5, 3, 1, 2, 1, 2, 2, 2]
def baseStart_5537969 : Nat := 118140960795 + 5537969 * 2 ^ 59
def prefixEnd_5537969 : Nat := 4983230072969 + 3 ^ 40 * 5537969 * 2
def baseEnd_5537969 : Nat := 2843639946699148404518851

theorem tailTrace_5537969 : CollatzResearch.WordTrace tailWord_5537969 prefixEnd_5537969 2843639946699148404518851 := by
  unfold tailWord_5537969
  simp only [CollatzResearch.WordTrace]
  refine ⟨201986323273891597650544961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134657548849261065100363307 201986323273891597650544961)
  ·
    refine ⟨151489742455418698237908721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201986323273891597650544961 151489742455418698237908721)
    ·
      refine ⟨113617306841564023678431541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151489742455418698237908721 113617306841564023678431541)
      ·
        refine ⟨10651622516396627219852957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113617306841564023678431541 10651622516396627219852957)
        ·
          refine ⟨3994358443648735207444859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10651622516396627219852957 3994358443648735207444859)
          ·
            refine ⟨5991537665473102811167289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3994358443648735207444859 5991537665473102811167289)
            ·
              refine ⟨4493653249104827108375467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5991537665473102811167289 4493653249104827108375467)
              ·
                refine ⟨6740479873657240662563201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4493653249104827108375467 6740479873657240662563201)
                ·
                  refine ⟨5055359905242930496922401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6740479873657240662563201 5055359905242930496922401)
                  ·
                    refine ⟨3791519928932197872691801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5055359905242930496922401 3791519928932197872691801)
                    ·
                      refine ⟨2843639946699148404518851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3791519928932197872691801 2843639946699148404518851)
                      ·
                        rfl

theorem cell23_5537969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_5537969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5537969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5537969 prefixEnd_5537969 := by exact prefixLift 5537969
  have htrace : WordTrace (prefixWord ++ tailWord_5537969) baseStart_5537969 baseEnd_5537969 := by
    simpa [prefixWord, tailWord_5537969, baseEnd_5537969] using wordTrace_append hprefix tailTrace_5537969
  have hstable : (prefixWord ++ tailWord_5537969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5537969).length < 2 ^ (prefixWord ++ tailWord_5537969).sum := by decide
  have hdescent : baseEnd_5537969 < baseStart_5537969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5537969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538051 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 1, 5, 2]
def baseStart_5538051 : Nat := 118140960795 + 5538051 * 2 ^ 59
def prefixEnd_5538051 : Nat := 4983230072969 + 3 ^ 40 * 5538051 * 2
def baseEnd_5538051 : Nat := 2843682052112817083693473

theorem tailTrace_5538051 : CollatzResearch.WordTrace tailWord_5538051 prefixEnd_5538051 2843682052112817083693473 := by
  unfold tailWord_5538051
  simp only [CollatzResearch.WordTrace]
  refine ⟨201989314059594525655030007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134659542706396350436686671 201989314059594525655030007)
  ·
    refine ⟨302983971089391788482545011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201989314059594525655030007 302983971089391788482545011)
    ·
      refine ⟨454475956634087682723817517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302983971089391788482545011 454475956634087682723817517)
      ·
        refine ⟨170428483737782881021431569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 454475956634087682723817517 170428483737782881021431569)
        ·
          refine ⟨127821362803337160766073677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170428483737782881021431569 127821362803337160766073677)
          ·
            refine ⟨47933011051251435287277629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127821362803337160766073677 47933011051251435287277629)
            ·
              refine ⟨17974879144219288232729111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47933011051251435287277629 17974879144219288232729111)
              ·
                refine ⟨26962318716328932349093667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17974879144219288232729111 26962318716328932349093667)
                ·
                  refine ⟨40443478074493398523640501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26962318716328932349093667 40443478074493398523640501)
                  ·
                    refine ⟨3791576069483756111591297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40443478074493398523640501 3791576069483756111591297)
                    ·
                      refine ⟨2843682052112817083693473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3791576069483756111591297 2843682052112817083693473)
                      ·
                        rfl

theorem cell23_5538051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 5, 2].length) (baseStart_5538051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538051 prefixEnd_5538051 := by exact prefixLift 5538051
  have htrace : WordTrace (prefixWord ++ tailWord_5538051) baseStart_5538051 baseEnd_5538051 := by
    simpa [prefixWord, tailWord_5538051, baseEnd_5538051] using wordTrace_append hprefix tailTrace_5538051
  have hstable : (prefixWord ++ tailWord_5538051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538051).length < 2 ^ (prefixWord ++ tailWord_5538051).sum := by decide
  have hdescent : baseEnd_5538051 < baseStart_5538051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538132 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_5538132 : Nat := 118140960795 + 5538132 * 2 ^ 59
def prefixEnd_5538132 : Nat := 4983230072969 + 3 ^ 40 * 5538132 * 2
def baseEnd_5538132 : Nat := 2843723644045831266780601

theorem tailTrace_5538132 : CollatzResearch.WordTrace tailWord_5538132 prefixEnd_5538132 2843723644045831266780601 := by
  unfold tailWord_5538132
  simp only [CollatzResearch.WordTrace]
  refine ⟨100996134186150538244364325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134661512248200717659152433 100996134186150538244364325)
  ·
    refine ⟨18936775159903225920818311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100996134186150538244364325 18936775159903225920818311)
    ·
      refine ⟨28405162739854838881227467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18936775159903225920818311 28405162739854838881227467)
      ·
        refine ⟨42607744109782258321841201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28405162739854838881227467 42607744109782258321841201)
        ·
          refine ⟨31955808082336693741380901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42607744109782258321841201 31955808082336693741380901)
          ·
            refine ⟨5991714015438130076508919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31955808082336693741380901 5991714015438130076508919)
            ·
              refine ⟨8987571023157195114763379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5991714015438130076508919 8987571023157195114763379)
              ·
                refine ⟨13481356534735792672145069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8987571023157195114763379 13481356534735792672145069)
                ·
                  refine ⟨5055508700525922252054401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13481356534735792672145069 5055508700525922252054401)
                  ·
                    refine ⟨3791631525394441689040801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5055508700525922252054401 3791631525394441689040801)
                    ·
                      refine ⟨2843723644045831266780601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3791631525394441689040801 2843723644045831266780601)
                      ·
                        rfl

theorem cell23_5538132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_5538132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538132 prefixEnd_5538132 := by exact prefixLift 5538132
  have htrace : WordTrace (prefixWord ++ tailWord_5538132) baseStart_5538132 baseEnd_5538132 := by
    simpa [prefixWord, tailWord_5538132, baseEnd_5538132] using wordTrace_append hprefix tailTrace_5538132
  have hstable : (prefixWord ++ tailWord_5538132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538132).length < 2 ^ (prefixWord ++ tailWord_5538132).sum := by decide
  have hdescent : baseEnd_5538132 < baseStart_5538132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538201 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 2, 2, 4]
def baseStart_5538201 : Nat := 118140960795 + 5538201 * 2 ^ 59
def prefixEnd_5538201 : Nat := 4983230072969 + 3 ^ 40 * 5538201 * 2
def baseEnd_5538201 : Nat := 2843759074210991496817783

theorem tailTrace_5538201 : CollatzResearch.WordTrace tailWord_5538201 prefixEnd_5538201 2843759074210991496817783 := by
  unfold tailWord_5538201
  simp only [CollatzResearch.WordTrace]
  refine ⟨201994785009051101272990457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134663190006034067515326971 201994785009051101272990457)
  ·
    refine ⟨151496088756788325954742843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201994785009051101272990457 151496088756788325954742843)
    ·
      refine ⟨227244133135182488932114265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151496088756788325954742843 227244133135182488932114265)
      ·
        refine ⟨170433099851386866699085699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227244133135182488932114265 170433099851386866699085699)
        ·
          refine ⟨255649649777080300048628549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170433099851386866699085699 255649649777080300048628549)
          ·
            refine ⟨47934309333202556259117853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255649649777080300048628549 47934309333202556259117853)
            ·
              refine ⟨17975365999950958597169195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47934309333202556259117853 17975365999950958597169195)
              ·
                refine ⟨26963048999926437895753793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17975365999950958597169195 26963048999926437895753793)
                ·
                  refine ⟨20222286749944828421815345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26963048999926437895753793 20222286749944828421815345)
                  ·
                    refine ⟨15166715062458621316361509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20222286749944828421815345 15166715062458621316361509)
                    ·
                      refine ⟨2843759074210991496817783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15166715062458621316361509 2843759074210991496817783)
                      ·
                        rfl

theorem cell23_5538201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_5538201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538201 prefixEnd_5538201 := by exact prefixLift 5538201
  have htrace : WordTrace (prefixWord ++ tailWord_5538201) baseStart_5538201 baseEnd_5538201 := by
    simpa [prefixWord, tailWord_5538201, baseEnd_5538201] using wordTrace_append hprefix tailTrace_5538201
  have hstable : (prefixWord ++ tailWord_5538201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538201).length < 2 ^ (prefixWord ++ tailWord_5538201).sum := by decide
  have hdescent : baseEnd_5538201 < baseStart_5538201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538211 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 7]
def baseStart_5538211 : Nat := 118140960795 + 5538211 * 2 ^ 59
def prefixEnd_5538211 : Nat := 4983230072969 + 3 ^ 40 * 5538211 * 2
def baseEnd_5538211 : Nat := 315973801001948495299193

theorem tailTrace_5538211 : CollatzResearch.WordTrace tailWord_5538211 prefixEnd_5538211 315973801001948495299193 := by
  unfold tailWord_5538211
  simp only [CollatzResearch.WordTrace]
  refine ⟨201995149739014872980854487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134663433159343248653902991 201995149739014872980854487)
  ·
    refine ⟨302992724608522309471281731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201995149739014872980854487 302992724608522309471281731)
    ·
      refine ⟨454489086912783464206922597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302992724608522309471281731 454489086912783464206922597)
      ·
        refine ⟨85216703796146899538797987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 454489086912783464206922597 85216703796146899538797987)
        ·
          refine ⟨127825055694220349308196981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85216703796146899538797987 127825055694220349308196981)
          ·
            refine ⟨11983598971333157747643467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127825055694220349308196981 11983598971333157747643467)
            ·
              refine ⟨17975398456999736621465201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11983598971333157747643467 17975398456999736621465201)
              ·
                refine ⟨13481548842749802466098901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17975398456999736621465201 13481548842749802466098901)
                ·
                  refine ⟨315973801001948495299193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13481548842749802466098901 315973801001948495299193)
                  ·
                    rfl

theorem cell23_5538211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 7].length) (baseStart_5538211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538211 prefixEnd_5538211 := by exact prefixLift 5538211
  have htrace : WordTrace (prefixWord ++ tailWord_5538211) baseStart_5538211 baseEnd_5538211 := by
    simpa [prefixWord, tailWord_5538211, baseEnd_5538211] using wordTrace_append hprefix tailTrace_5538211
  have hstable : (prefixWord ++ tailWord_5538211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538211).length < 2 ^ (prefixWord ++ tailWord_5538211).sum := by decide
  have hdescent : baseEnd_5538211 < baseStart_5538211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538238 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_5538238 : Nat := 118140960795 + 5538238 * 2 ^ 59
def prefixEnd_5538238 : Nat := 4983230072969 + 3 ^ 40 * 5538238 * 2
def baseEnd_5538238 : Nat := 2843778072995207852055113

theorem tailTrace_5538238 : CollatzResearch.WordTrace tailWord_5538238 prefixEnd_5538238 2843778072995207852055113 := by
  unfold tailWord_5538238
  simp only [CollatzResearch.WordTrace]
  refine ⟨25249516813739632074010921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134664089673278037728058245 25249516813739632074010921)
  ·
    refine ⟨18937137610304724055508191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25249516813739632074010921 18937137610304724055508191)
    ·
      refine ⟨28405706415457086083262287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18937137610304724055508191 28405706415457086083262287)
      ·
        refine ⟨42608559623185629124893431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28405706415457086083262287 42608559623185629124893431)
        ·
          refine ⟨63912839434778443687340147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42608559623185629124893431 63912839434778443687340147)
          ·
            refine ⟨95869259152167665531010221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63912839434778443687340147 95869259152167665531010221)
            ·
              refine ⟨35950972182062874574128833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95869259152167665531010221 35950972182062874574128833)
              ·
                refine ⟨26963229136547155930596625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35950972182062874574128833 26963229136547155930596625)
                ·
                  refine ⟨20222421852410366947947469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26963229136547155930596625 20222421852410366947947469)
                  ·
                    refine ⟨7583408194653887605480301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20222421852410366947947469 7583408194653887605480301)
                    ·
                      refine ⟨2843778072995207852055113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7583408194653887605480301 2843778072995207852055113)
                      ·
                        rfl

theorem cell23_5538238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_5538238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538238 prefixEnd_5538238 := by exact prefixLift 5538238
  have htrace : WordTrace (prefixWord ++ tailWord_5538238) baseStart_5538238 baseEnd_5538238 := by
    simpa [prefixWord, tailWord_5538238, baseEnd_5538238] using wordTrace_append hprefix tailTrace_5538238
  have hstable : (prefixWord ++ tailWord_5538238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538238).length < 2 ^ (prefixWord ++ tailWord_5538238).sum := by decide
  have hdescent : baseEnd_5538238 < baseStart_5538238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538301 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 8]
def baseStart_5538301 : Nat := 118140960795 + 5538301 * 2 ^ 59
def prefixEnd_5538301 : Nat := 4983230072969 + 3 ^ 40 * 5538301 * 2
def baseEnd_5538301 : Nat := 315978935808493456174147

theorem tailTrace_5538301 : CollatzResearch.WordTrace tailWord_5538301 prefixEnd_5538301 315978935808493456174147 := by
  unfold tailWord_5538301
  simp only [CollatzResearch.WordTrace]
  refine ⟨201998432308688818351630757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134665621539125878901087171 201998432308688818351630757)
  ·
    refine ⟨37874706057879153440930767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201998432308688818351630757 37874706057879153440930767)
    ·
      refine ⟨56812059086818730161396151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37874706057879153440930767 56812059086818730161396151)
      ·
        refine ⟨85218088630228095242094227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56812059086818730161396151 85218088630228095242094227)
        ·
          refine ⟨127827132945342142863141341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85218088630228095242094227 127827132945342142863141341)
          ·
            refine ⟨47935174854503303573678003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127827132945342142863141341 47935174854503303573678003)
            ·
              refine ⟨71902762281754955360517005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47935174854503303573678003 71902762281754955360517005)
              ·
                refine ⟨26963535855658108260193877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71902762281754955360517005 26963535855658108260193877)
                ·
                  refine ⟨315978935808493456174147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26963535855658108260193877 315978935808493456174147)
                  ·
                    rfl

theorem cell23_5538301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_5538301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538301 prefixEnd_5538301 := by exact prefixLift 5538301
  have htrace : WordTrace (prefixWord ++ tailWord_5538301) baseStart_5538301 baseEnd_5538301 := by
    simpa [prefixWord, tailWord_5538301, baseEnd_5538301] using wordTrace_append hprefix tailTrace_5538301
  have hstable : (prefixWord ++ tailWord_5538301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538301).length < 2 ^ (prefixWord ++ tailWord_5538301).sum := by decide
  have hdescent : baseEnd_5538301 < baseStart_5538301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538305 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 3, 4]
def baseStart_5538305 : Nat := 118140960795 + 5538305 * 2 ^ 59
def prefixEnd_5538305 : Nat := 4983230072969 + 3 ^ 40 * 5538305 * 2
def baseEnd_5538305 : Nat := 947937492066353029972435

theorem tailTrace_5538305 : CollatzResearch.WordTrace tailWord_5538305 prefixEnd_5538305 947937492066353029972435 := by
  unfold tailWord_5538305
  simp only [CollatzResearch.WordTrace]
  refine ⟨201998578200674327034776369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134665718800449551356517579 201998578200674327034776369)
  ·
    refine ⟨151498933650505745276082277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201998578200674327034776369 151498933650505745276082277)
    ·
      refine ⟨28406050059469827239265427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151498933650505745276082277 28406050059469827239265427)
      ·
        refine ⟨42609075089204740858898141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28406050059469827239265427 42609075089204740858898141)
        ·
          refine ⟨15978403158451777822086803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42609075089204740858898141 15978403158451777822086803)
          ·
            refine ⟨23967604737677666733130205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15978403158451777822086803 23967604737677666733130205)
            ·
              refine ⟨8987851776629125024923827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23967604737677666733130205 8987851776629125024923827)
              ·
                refine ⟨13481777664943687537385741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8987851776629125024923827 13481777664943687537385741)
                ·
                  refine ⟨5055666624353882826519653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13481777664943687537385741 5055666624353882826519653)
                  ·
                    refine ⟨947937492066353029972435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5055666624353882826519653 947937492066353029972435)
                    ·
                      rfl

theorem cell23_5538305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_5538305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538305 prefixEnd_5538305 := by exact prefixLift 5538305
  have htrace : WordTrace (prefixWord ++ tailWord_5538305) baseStart_5538305 baseEnd_5538305 := by
    simpa [prefixWord, tailWord_5538305, baseEnd_5538305] using wordTrace_append hprefix tailTrace_5538305
  have hstable : (prefixWord ++ tailWord_5538305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538305).length < 2 ^ (prefixWord ++ tailWord_5538305).sum := by decide
  have hdescent : baseEnd_5538305 < baseStart_5538305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538348 : List Nat := [2, 2, 1, 1, 1, 2, 1, 7, 1, 5]
def baseStart_5538348 : Nat := 118140960795 + 5538348 * 2 ^ 59
def prefixEnd_5538348 : Nat := 4983230072969 + 3 ^ 40 * 5538348 * 2
def baseEnd_5538348 : Nat := 947944851955734140559869

theorem tailTrace_5538348 : CollatzResearch.WordTrace tailWord_5538348 prefixEnd_5538348 947944851955734140559869 := by
  unfold tailWord_5538348
  simp only [CollatzResearch.WordTrace]
  refine ⟨101000073269759272689295849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134666764359679030252394465 101000073269759272689295849)
  ·
    refine ⟨75750054952319454516971887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101000073269759272689295849 75750054952319454516971887)
    ·
      refine ⟨113625082428479181775457831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75750054952319454516971887 113625082428479181775457831)
      ·
        refine ⟨170437623642718772663186747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113625082428479181775457831 170437623642718772663186747)
        ·
          refine ⟨255656435464078158994780121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170437623642718772663186747 255656435464078158994780121)
          ·
            refine ⟨191742326598058619246085091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255656435464078158994780121 191742326598058619246085091)
            ·
              refine ⟨287613489897087928869127637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191742326598058619246085091 287613489897087928869127637)
              ·
                refine ⟨6740941169462998332870179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 287613489897087928869127637 6740941169462998332870179)
                ·
                  refine ⟨10111411754194497499305269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6740941169462998332870179 10111411754194497499305269)
                  ·
                    refine ⟨947944851955734140559869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10111411754194497499305269 947944851955734140559869)
                    ·
                      rfl

theorem cell23_5538348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_5538348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538348 prefixEnd_5538348 := by exact prefixLift 5538348
  have htrace : WordTrace (prefixWord ++ tailWord_5538348) baseStart_5538348 baseEnd_5538348 := by
    simpa [prefixWord, tailWord_5538348, baseEnd_5538348] using wordTrace_append hprefix tailTrace_5538348
  have hstable : (prefixWord ++ tailWord_5538348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538348).length < 2 ^ (prefixWord ++ tailWord_5538348).sum := by decide
  have hdescent : baseEnd_5538348 < baseStart_5538348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538355 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 2, 3, 2]
def baseStart_5538355 : Nat := 118140960795 + 5538355 * 2 ^ 59
def prefixEnd_5538355 : Nat := 4983230072969 + 3 ^ 40 * 5538355 * 2
def baseEnd_5538355 : Nat := 2843838150231783894292075

theorem tailTrace_5538355 : CollatzResearch.WordTrace tailWord_5538355 prefixEnd_5538355 2843838150231783894292075 := by
  unfold tailWord_5538355
  simp only [CollatzResearch.WordTrace]
  refine ⟨202000401850493185574096519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134666934566995457049397679 202000401850493185574096519)
  ·
    refine ⟨303000602775739778361144779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202000401850493185574096519 303000602775739778361144779)
    ·
      refine ⟨454500904163609667541717169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303000602775739778361144779 454500904163609667541717169)
      ·
        refine ⟨340875678122707250656287877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454500904163609667541717169 340875678122707250656287877)
        ·
          refine ⟨63914189648007609498053977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 340875678122707250656287877 63914189648007609498053977)
          ·
            refine ⟨47935642236005707123540483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63914189648007609498053977 47935642236005707123540483)
            ·
              refine ⟨71903463354008560685310725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47935642236005707123540483 71903463354008560685310725)
              ·
                refine ⟨13481899378876605128495761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71903463354008560685310725 13481899378876605128495761)
                ·
                  refine ⟨10111424534157453846371821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13481899378876605128495761 10111424534157453846371821)
                  ·
                    refine ⟨3791784200309045192389433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10111424534157453846371821 3791784200309045192389433)
                    ·
                      refine ⟨2843838150231783894292075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3791784200309045192389433 2843838150231783894292075)
                      ·
                        rfl

theorem cell23_5538355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 3, 2].length) (baseStart_5538355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538355 prefixEnd_5538355 := by exact prefixLift 5538355
  have htrace : WordTrace (prefixWord ++ tailWord_5538355) baseStart_5538355 baseEnd_5538355 := by
    simpa [prefixWord, tailWord_5538355, baseEnd_5538355] using wordTrace_append hprefix tailTrace_5538355
  have hstable : (prefixWord ++ tailWord_5538355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538355).length < 2 ^ (prefixWord ++ tailWord_5538355).sum := by decide
  have hdescent : baseEnd_5538355 < baseStart_5538355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538356 : List Nat := [2, 5, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_5538356 : Nat := 118140960795 + 5538356 * 2 ^ 59
def prefixEnd_5538356 : Nat := 4983230072969 + 3 ^ 40 * 5538356 * 2
def baseEnd_5538356 : Nat := 947946221237479463459857

theorem tailTrace_5538356 : CollatzResearch.WordTrace tailWord_5538356 prefixEnd_5538356 947946221237479463459857 := by
  unfold tailWord_5538356
  simp only [CollatzResearch.WordTrace]
  refine ⟨101000219161744781372441461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134666958882326375163255281 101000219161744781372441461)
  ·
    refine ⟨9468770546413573253666387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101000219161744781372441461 9468770546413573253666387)
    ·
      refine ⟨14203155819620359880499581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9468770546413573253666387 14203155819620359880499581)
      ·
        refine ⟨5326183432357634955187343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14203155819620359880499581 5326183432357634955187343)
        ·
          refine ⟨7989275148536452432781015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5326183432357634955187343 7989275148536452432781015)
          ·
            refine ⟨11983912722804678649171523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7989275148536452432781015 11983912722804678649171523)
            ·
              refine ⟨17975869084207017973757285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11983912722804678649171523 17975869084207017973757285)
              ·
                refine ⟨3370475453288815870079491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17975869084207017973757285 3370475453288815870079491)
                ·
                  refine ⟨5055713179933223805119237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3370475453288815870079491 5055713179933223805119237)
                  ·
                    refine ⟨947946221237479463459857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5055713179933223805119237 947946221237479463459857)
                    ·
                      rfl

theorem cell23_5538356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_5538356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538356 prefixEnd_5538356 := by exact prefixLift 5538356
  have htrace : WordTrace (prefixWord ++ tailWord_5538356) baseStart_5538356 baseEnd_5538356 := by
    simpa [prefixWord, tailWord_5538356, baseEnd_5538356] using wordTrace_append hprefix tailTrace_5538356
  have hstable : (prefixWord ++ tailWord_5538356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538356).length < 2 ^ (prefixWord ++ tailWord_5538356).sum := by decide
  have hdescent : baseEnd_5538356 < baseStart_5538356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538368 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 4]
def baseStart_5538368 : Nat := 118140960795 + 5538368 * 2 ^ 59
def prefixEnd_5538368 : Nat := 4983230072969 + 3 ^ 40 * 5538368 * 2
def baseEnd_5538368 : Nat := 2843844825480292343429515

theorem tailTrace_5538368 : CollatzResearch.WordTrace tailWord_5538368 prefixEnd_5538368 2843844825480292343429515 := by
  unfold tailWord_5538368
  simp only [CollatzResearch.WordTrace]
  refine ⟨101000437999723044397159879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134667250666297392529546505 101000437999723044397159879)
  ·
    refine ⟨151500656999584566595739819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101000437999723044397159879 151500656999584566595739819)
    ·
      refine ⟨227250985499376849893609729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151500656999584566595739819 227250985499376849893609729)
      ·
        refine ⟨170438239124532637420207297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227250985499376849893609729 170438239124532637420207297)
        ·
          refine ⟨127828679343399478065155473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170438239124532637420207297 127828679343399478065155473)
          ·
            refine ⟨95871509507549608548866605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127828679343399478065155473 95871509507549608548866605)
            ·
              refine ⟨35951816065331103205824977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95871509507549608548866605 35951816065331103205824977)
              ·
                refine ⟨26963862048998327404368733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35951816065331103205824977 26963862048998327404368733)
                ·
                  refine ⟨10111448268374372776638275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26963862048998327404368733 10111448268374372776638275)
                  ·
                    refine ⟨15167172402561559164957413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10111448268374372776638275 15167172402561559164957413)
                    ·
                      refine ⟨2843844825480292343429515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15167172402561559164957413 2843844825480292343429515)
                      ·
                        rfl

theorem cell23_5538368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_5538368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538368 prefixEnd_5538368 := by exact prefixLift 5538368
  have htrace : WordTrace (prefixWord ++ tailWord_5538368) baseStart_5538368 baseEnd_5538368 := by
    simpa [prefixWord, tailWord_5538368, baseEnd_5538368] using wordTrace_append hprefix tailTrace_5538368
  have hstable : (prefixWord ++ tailWord_5538368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538368).length < 2 ^ (prefixWord ++ tailWord_5538368).sum := by decide
  have hdescent : baseEnd_5538368 < baseStart_5538368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538378 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 1, 6]
def baseStart_5538378 : Nat := 118140960795 + 5538378 * 2 ^ 59
def prefixEnd_5538378 : Nat := 4983230072969 + 3 ^ 40 * 5538378 * 2
def baseEnd_5538378 : Nat := 947949986762279101434823

theorem tailTrace_5538378 : CollatzResearch.WordTrace tailWord_5538378 prefixEnd_5538378 947949986762279101434823 := by
  unfold tailWord_5538378
  simp only [CollatzResearch.WordTrace]
  refine ⟨50500310182352465125545947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134667493819606573668122525 50500310182352465125545947)
  ·
    refine ⟨75750465273528697688318921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50500310182352465125545947 75750465273528697688318921)
    ·
      refine ⟨56812848955146523266239191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75750465273528697688318921 56812848955146523266239191)
      ·
        refine ⟨85219273432719784899358787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56812848955146523266239191 85219273432719784899358787)
        ·
          refine ⟨127828910149079677349038181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85219273432719784899358787 127828910149079677349038181)
          ·
            refine ⟨23967920652952439502944659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127828910149079677349038181 23967920652952439502944659)
            ·
              refine ⟨35951880979428659254416989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23967920652952439502944659 35951880979428659254416989)
              ·
                refine ⟨13481955367285747220406371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35951880979428659254416989 13481955367285747220406371)
                ·
                  refine ⟨20222933050928620830609557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13481955367285747220406371 20222933050928620830609557)
                  ·
                    refine ⟨947949986762279101434823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20222933050928620830609557 947949986762279101434823)
                    ·
                      rfl

theorem cell23_5538378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_5538378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538378 prefixEnd_5538378 := by exact prefixLift 5538378
  have htrace : WordTrace (prefixWord ++ tailWord_5538378) baseStart_5538378 baseEnd_5538378 := by
    simpa [prefixWord, tailWord_5538378, baseEnd_5538378] using wordTrace_append hprefix tailTrace_5538378
  have hstable : (prefixWord ++ tailWord_5538378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538378).length < 2 ^ (prefixWord ++ tailWord_5538378).sum := by decide
  have hdescent : baseEnd_5538378 < baseStart_5538378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538396 : List Nat := [2, 2, 4, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_5538396 : Nat := 118140960795 + 5538396 * 2 ^ 59
def prefixEnd_5538396 : Nat := 4983230072969 + 3 ^ 40 * 5538396 * 2
def baseEnd_5538396 : Nat := 2843859202938618233879387

theorem tailTrace_5538396 : CollatzResearch.WordTrace tailWord_5538396 prefixEnd_5538396 2843859202938618233879387 := by
  unfold tailWord_5538396
  simp only [CollatzResearch.WordTrace]
  refine ⟨101000948621672324788169521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134667931495563099717559361 101000948621672324788169521)
  ·
    refine ⟨75750711466254243591127141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101000948621672324788169521 75750711466254243591127141)
    ·
      refine ⟨14203258399922670673336339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75750711466254243591127141 14203258399922670673336339)
      ·
        refine ⟨21304887599884006010004509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14203258399922670673336339 21304887599884006010004509)
        ·
          refine ⟨7989332849956502253751691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21304887599884006010004509 7989332849956502253751691)
          ·
            refine ⟨11983999274934753380627537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7989332849956502253751691 11983999274934753380627537)
            ·
              refine ⟨8987999456201065035470653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11983999274934753380627537 8987999456201065035470653)
              ·
                refine ⟨3370499796075399388301495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8987999456201065035470653 3370499796075399388301495)
                ·
                  refine ⟨5055749694113099082452243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3370499796075399388301495 5055749694113099082452243)
                  ·
                    refine ⟨7583624541169648623678365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5055749694113099082452243 7583624541169648623678365)
                    ·
                      refine ⟨2843859202938618233879387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7583624541169648623678365 2843859202938618233879387)
                      ·
                        rfl

theorem cell23_5538396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_5538396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538396 prefixEnd_5538396 := by exact prefixLift 5538396
  have htrace : WordTrace (prefixWord ++ tailWord_5538396) baseStart_5538396 baseEnd_5538396 := by
    simpa [prefixWord, tailWord_5538396, baseEnd_5538396] using wordTrace_append hprefix tailTrace_5538396
  have hstable : (prefixWord ++ tailWord_5538396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538396).length < 2 ^ (prefixWord ++ tailWord_5538396).sum := by decide
  have hdescent : baseEnd_5538396 < baseStart_5538396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538422 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_5538422 : Nat := 118140960795 + 5538422 * 2 ^ 59
def prefixEnd_5538422 : Nat := 4983230072969 + 3 ^ 40 * 5538422 * 2
def baseEnd_5538422 : Nat := 2843872553435635132154267

theorem tailTrace_5538422 : CollatzResearch.WordTrace tailWord_5538422 prefixEnd_5538422 2843872553435635132154267 := by
  unfold tailWord_5538422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12625177846328153501049095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134668563694166970677857013 12625177846328153501049095)
  ·
    refine ⟨18937766769492230251573643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12625177846328153501049095 18937766769492230251573643)
    ·
      refine ⟨28406650154238345377360465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18937766769492230251573643 28406650154238345377360465)
      ·
        refine ⟨21304987615678759033020349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28406650154238345377360465 21304987615678759033020349)
        ·
          refine ⟨7989370355879534637382631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21304987615678759033020349 7989370355879534637382631)
          ·
            refine ⟨11984055533819301956073947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7989370355879534637382631 11984055533819301956073947)
            ·
              refine ⟨17976083300728952934110921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11984055533819301956073947 17976083300728952934110921)
              ·
                refine ⟨13482062475546714700583191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17976083300728952934110921 13482062475546714700583191)
                ·
                  refine ⟨20223093713320072050874787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13482062475546714700583191 20223093713320072050874787)
                  ·
                    refine ⟨30334640569980108076312181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20223093713320072050874787 30334640569980108076312181)
                    ·
                      refine ⟨2843872553435635132154267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30334640569980108076312181 2843872553435635132154267)
                      ·
                        rfl

theorem cell23_5538422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_5538422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538422 prefixEnd_5538422 := by exact prefixLift 5538422
  have htrace : WordTrace (prefixWord ++ tailWord_5538422) baseStart_5538422 baseEnd_5538422 := by
    simpa [prefixWord, tailWord_5538422, baseEnd_5538422] using wordTrace_append hprefix tailTrace_5538422
  have hstable : (prefixWord ++ tailWord_5538422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538422).length < 2 ^ (prefixWord ++ tailWord_5538422).sum := by decide
  have hdescent : baseEnd_5538422 < baseStart_5538422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538429 : List Nat := [1, 4, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_5538429 : Nat := 118140960795 + 5538429 * 2 ^ 59
def prefixEnd_5538429 : Nat := 4983230072969 + 3 ^ 40 * 5538429 * 2
def baseEnd_5538429 : Nat := 947958715933405534922245

theorem tailTrace_5538429 : CollatzResearch.WordTrace tailWord_5538429 prefixEnd_5538429 947958715933405534922245 := by
  unfold tailWord_5538429
  simp only [CollatzResearch.WordTrace]
  refine ⟨202003100852225096212290341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134668733901483397474860227 202003100852225096212290341)
  ·
    refine ⟨37875581409792205539804439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202003100852225096212290341 37875581409792205539804439)
    ·
      refine ⟨56813372114688308309706659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37875581409792205539804439 56813372114688308309706659)
      ·
        refine ⟨85220058172032462464559989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56813372114688308309706659 85220058172032462464559989)
        ·
          refine ⟨7989380453628043356052499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85220058172032462464559989 7989380453628043356052499)
          ·
            refine ⟨11984070680442065034078749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7989380453628043356052499 11984070680442065034078749)
            ·
              refine ⟨4494026505165774387779531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11984070680442065034078749 4494026505165774387779531)
              ·
                refine ⟨6741039757748661581669297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4494026505165774387779531 6741039757748661581669297)
                ·
                  refine ⟨5055779818311496186251973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6741039757748661581669297 5055779818311496186251973)
                  ·
                    refine ⟨947958715933405534922245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5055779818311496186251973 947958715933405534922245)
                    ·
                      rfl

theorem cell23_5538429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_5538429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538429 prefixEnd_5538429 := by exact prefixLift 5538429
  have htrace : WordTrace (prefixWord ++ tailWord_5538429) baseStart_5538429 baseEnd_5538429 := by
    simpa [prefixWord, tailWord_5538429, baseEnd_5538429] using wordTrace_append hprefix tailTrace_5538429
  have hstable : (prefixWord ++ tailWord_5538429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538429).length < 2 ^ (prefixWord ++ tailWord_5538429).sum := by decide
  have hdescent : baseEnd_5538429 < baseStart_5538429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538435 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 3]
def baseStart_5538435 : Nat := 118140960795 + 5538435 * 2 ^ 59
def prefixEnd_5538435 : Nat := 4983230072969 + 3 ^ 40 * 5538435 * 2
def baseEnd_5538435 : Nat := 2843879228684143581291707

theorem tailTrace_5538435 : CollatzResearch.WordTrace tailWord_5538435 prefixEnd_5538435 2843879228684143581291707 := by
  unfold tailWord_5538435
  simp only [CollatzResearch.WordTrace]
  refine ⟨202003319690203359237008759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134668879793468906158005839 202003319690203359237008759)
  ·
    refine ⟨303004979535305038855513139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202003319690203359237008759 303004979535305038855513139)
    ·
      refine ⟨454507469302957558283269709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303004979535305038855513139 454507469302957558283269709)
      ·
        refine ⟨170440300988609084356226141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 454507469302957558283269709 170440300988609084356226141)
        ·
          refine ⟨63915112870728406633584803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170440300988609084356226141 63915112870728406633584803)
          ·
            refine ⟨95872669306092609950377205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63915112870728406633584803 95872669306092609950377205)
            ·
              refine ⟨8988062747446182182847863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95872669306092609950377205 8988062747446182182847863)
              ·
                refine ⟨13482094121169273274271795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8988062747446182182847863 13482094121169273274271795)
                ·
                  refine ⟨20223141181753909911407693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13482094121169273274271795 20223141181753909911407693)
                  ·
                    refine ⟨7583677943157716216777885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20223141181753909911407693 7583677943157716216777885)
                    ·
                      refine ⟨2843879228684143581291707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7583677943157716216777885 2843879228684143581291707)
                      ·
                        rfl

theorem cell23_5538435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_5538435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538435 prefixEnd_5538435 := by exact prefixLift 5538435
  have htrace : WordTrace (prefixWord ++ tailWord_5538435) baseStart_5538435 baseEnd_5538435 := by
    simpa [prefixWord, tailWord_5538435, baseEnd_5538435] using wordTrace_append hprefix tailTrace_5538435
  have hstable : (prefixWord ++ tailWord_5538435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538435).length < 2 ^ (prefixWord ++ tailWord_5538435).sum := by decide
  have hdescent : baseEnd_5538435 < baseStart_5538435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538442 : List Nat := [3, 1, 2, 3, 3, 2, 2, 7]
def baseStart_5538442 : Nat := 118140960795 + 5538442 * 2 ^ 59
def prefixEnd_5538442 : Nat := 4983230072969 + 3 ^ 40 * 5538442 * 2
def baseEnd_5538442 : Nat := 105328993446249076070525

theorem tailTrace_5538442 : CollatzResearch.WordTrace tailWord_5538442 prefixEnd_5538442 105328993446249076070525 := by
  unfold tailWord_5538442
  simp only [CollatzResearch.WordTrace]
  refine ⟨50500893750294499858128395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134669050000785332955009053 50500893750294499858128395)
  ·
    refine ⟨75751340625441749787192593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50500893750294499858128395 75751340625441749787192593)
    ·
      refine ⟨56813505469081312340394445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75751340625441749787192593 56813505469081312340394445)
      ·
        refine ⟨21305064550905492127647917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56813505469081312340394445 21305064550905492127647917)
        ·
          refine ⟨7989399206589559547867969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21305064550905492127647917 7989399206589559547867969)
          ·
            refine ⟨5992049404942169660900977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7989399206589559547867969 5992049404942169660900977)
            ·
              refine ⟨4494037053706627245675733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5992049404942169660900977 4494037053706627245675733)
              ·
                refine ⟨105328993446249076070525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4494037053706627245675733 105328993446249076070525)
                ·
                  rfl

theorem cell23_5538442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 7].length) (baseStart_5538442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538442 prefixEnd_5538442 := by exact prefixLift 5538442
  have htrace : WordTrace (prefixWord ++ tailWord_5538442) baseStart_5538442 baseEnd_5538442 := by
    simpa [prefixWord, tailWord_5538442, baseEnd_5538442] using wordTrace_append hprefix tailTrace_5538442
  have hstable : (prefixWord ++ tailWord_5538442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538442).length < 2 ^ (prefixWord ++ tailWord_5538442).sum := by decide
  have hdescent : baseEnd_5538442 < baseStart_5538442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538492 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 1, 4, 2]
def baseStart_5538492 : Nat := 118140960795 + 5538492 * 2 ^ 59
def prefixEnd_5538492 : Nat := 4983230072969 + 3 ^ 40 * 5538492 * 2
def baseEnd_5538492 : Nat := 2843908497081449858278945

theorem tailTrace_5538492 : CollatzResearch.WordTrace tailWord_5538492 prefixEnd_5538492 2843908497081449858278945 := by
  unfold tailWord_5538492
  simp only [CollatzResearch.WordTrace]
  refine ⟨101002699325498428985916865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134670265767331238647889153 101002699325498428985916865)
  ·
    refine ⟨75752024494123821739437649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101002699325498428985916865 75752024494123821739437649)
    ·
      refine ⟨56814018370592866304578237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75752024494123821739437649 56814018370592866304578237)
      ·
        refine ⟨21305256888972324864216839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56814018370592866304578237 21305256888972324864216839)
        ·
          refine ⟨31957885333458487296325259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21305256888972324864216839 31957885333458487296325259)
          ·
            refine ⟨47936828000187730944487889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31957885333458487296325259 47936828000187730944487889)
            ·
              refine ⟨35952621000140798208365917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47936828000187730944487889 35952621000140798208365917)
              ·
                refine ⟨13482232875052799328137219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35952621000140798208365917 13482232875052799328137219)
                ·
                  refine ⟨20223349312579198992205829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13482232875052799328137219 20223349312579198992205829)
                  ·
                    refine ⟨3791877996108599811038593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20223349312579198992205829 3791877996108599811038593)
                    ·
                      refine ⟨2843908497081449858278945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3791877996108599811038593 2843908497081449858278945)
                      ·
                        rfl

theorem cell23_5538492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_5538492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538492 prefixEnd_5538492 := by exact prefixLift 5538492
  have htrace : WordTrace (prefixWord ++ tailWord_5538492) baseStart_5538492 baseEnd_5538492 := by
    simpa [prefixWord, tailWord_5538492, baseEnd_5538492] using wordTrace_append hprefix tailTrace_5538492
  have hstable : (prefixWord ++ tailWord_5538492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538492).length < 2 ^ (prefixWord ++ tailWord_5538492).sum := by decide
  have hdescent : baseEnd_5538492 < baseStart_5538492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538528 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 3, 7]
def baseStart_5538528 : Nat := 118140960795 + 5538528 * 2 ^ 59
def prefixEnd_5538528 : Nat := 4983230072969 + 3 ^ 40 * 5538528 * 2
def baseEnd_5538528 : Nat := 947975660795003905809593

theorem tailTrace_5538528 : CollatzResearch.WordTrace tailWord_5538528 prefixEnd_5538528 947975660795003905809593 := by
  unfold tailWord_5538528
  simp only [CollatzResearch.WordTrace]
  refine ⟨101003355839433218060072119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134671141119244290746762825 101003355839433218060072119)
  ·
    refine ⟨151505033759149827090108179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101003355839433218060072119 151505033759149827090108179)
    ·
      refine ⟨227257550638724740635162269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151505033759149827090108179 227257550638724740635162269)
      ·
        refine ⟨85221581489521777738185851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227257550638724740635162269 85221581489521777738185851)
        ·
          refine ⟨127832372234282666607278777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85221581489521777738185851 127832372234282666607278777)
          ·
            refine ⟨95874279175711999955459083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127832372234282666607278777 95874279175711999955459083)
            ·
              refine ⟨143811418763567999933188625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95874279175711999955459083 143811418763567999933188625)
              ·
                refine ⟨107858564072675999949891469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143811418763567999933188625 107858564072675999949891469)
                ·
                  refine ⟨40446961527253499981209301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107858564072675999949891469 40446961527253499981209301)
                  ·
                    refine ⟨947975660795003905809593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40446961527253499981209301 947975660795003905809593)
                    ·
                      rfl

theorem cell23_5538528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_5538528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538528 prefixEnd_5538528 := by exact prefixLift 5538528
  have htrace : WordTrace (prefixWord ++ tailWord_5538528) baseStart_5538528 baseEnd_5538528 := by
    simpa [prefixWord, tailWord_5538528, baseEnd_5538528] using wordTrace_append hprefix tailTrace_5538528
  have hstable : (prefixWord ++ tailWord_5538528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538528).length < 2 ^ (prefixWord ++ tailWord_5538528).sum := by decide
  have hdescent : baseEnd_5538528 < baseStart_5538528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538532 : List Nat := [2, 3, 1, 1, 1, 5, 1, 4, 5]
def baseStart_5538532 : Nat := 118140960795 + 5538532 * 2 ^ 59
def prefixEnd_5538532 : Nat := 4983230072969 + 3 ^ 40 * 5538532 * 2
def baseEnd_5538532 : Nat := 315992115145292189086529

theorem tailTrace_5538532 : CollatzResearch.WordTrace tailWord_5538532 prefixEnd_5538532 315992115145292189086529 := by
  unfold tailWord_5538532
  simp only [CollatzResearch.WordTrace]
  refine ⟨101003428785425972401644925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134671238380567963202193233 101003428785425972401644925)
  ·
    refine ⟨37876285794534739650616847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101003428785425972401644925 37876285794534739650616847)
    ·
      refine ⟨56814428691802109475925271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37876285794534739650616847 56814428691802109475925271)
      ·
        refine ⟨85221643037703164213887907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56814428691802109475925271 85221643037703164213887907)
        ·
          refine ⟨127832464556554746320831861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85221643037703164213887907 127832464556554746320831861)
          ·
            refine ⟨11984293552177007467577987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127832464556554746320831861 11984293552177007467577987)
            ·
              refine ⟨17976440328265511201366981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11984293552177007467577987 17976440328265511201366981)
              ·
                refine ⟨3370582561549783350256309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17976440328265511201366981 3370582561549783350256309)
                ·
                  refine ⟨315992115145292189086529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3370582561549783350256309 315992115145292189086529)
                  ·
                    rfl

theorem cell23_5538532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_5538532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538532 prefixEnd_5538532 := by exact prefixLift 5538532
  have htrace : WordTrace (prefixWord ++ tailWord_5538532) baseStart_5538532 baseEnd_5538532 := by
    simpa [prefixWord, tailWord_5538532, baseEnd_5538532] using wordTrace_append hprefix tailTrace_5538532
  have hstable : (prefixWord ++ tailWord_5538532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538532).length < 2 ^ (prefixWord ++ tailWord_5538532).sum := by decide
  have hdescent : baseEnd_5538532 < baseStart_5538532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538542 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_5538542 : Nat := 118140960795 + 5538542 * 2 ^ 59
def prefixEnd_5538542 : Nat := 4983230072969 + 3 ^ 40 * 5538542 * 2
def baseEnd_5538542 : Nat := 2843934171114174662653715

theorem tailTrace_5538542 : CollatzResearch.WordTrace tailWord_5538542 prefixEnd_5538542 2843934171114174662653715 := by
  unfold tailWord_5538542
  simp only [CollatzResearch.WordTrace]
  refine ⟨25250902787601964563894235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134671481533877144340769253 25250902787601964563894235)
  ·
    refine ⟨37876354181402946845841353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25250902787601964563894235 37876354181402946845841353)
    ·
      refine ⟨28407265636052210134381015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37876354181402946845841353 28407265636052210134381015)
      ·
        refine ⟨42610898454078315201571523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28407265636052210134381015 42610898454078315201571523)
        ·
          refine ⟨63916347681117472802357285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42610898454078315201571523 63916347681117472802357285)
          ·
            refine ⟨11984315190209526150441991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63916347681117472802357285 11984315190209526150441991)
            ·
              refine ⟨17976472785314289225662987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11984315190209526150441991 17976472785314289225662987)
              ·
                refine ⟨26964709177971433838494481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17976472785314289225662987 26964709177971433838494481)
                ·
                  refine ⟨20223531883478575378870861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26964709177971433838494481 20223531883478575378870861)
                  ·
                    refine ⟨7583824456304465767076573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20223531883478575378870861 7583824456304465767076573)
                    ·
                      refine ⟨2843934171114174662653715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7583824456304465767076573 2843934171114174662653715)
                      ·
                        rfl

theorem cell23_5538542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_5538542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538542 prefixEnd_5538542 := by exact prefixLift 5538542
  have htrace : WordTrace (prefixWord ++ tailWord_5538542) baseStart_5538542 baseEnd_5538542 := by
    simpa [prefixWord, tailWord_5538542, baseEnd_5538542] using wordTrace_append hprefix tailTrace_5538542
  have hstable : (prefixWord ++ tailWord_5538542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538542).length < 2 ^ (prefixWord ++ tailWord_5538542).sum := by decide
  have hdescent : baseEnd_5538542 < baseStart_5538542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538562 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_5538562 : Nat := 118140960795 + 5538562 * 2 ^ 59
def prefixEnd_5538562 : Nat := 4983230072969 + 3 ^ 40 * 5538562 * 2
def baseEnd_5538562 : Nat := 947981480242421528134541

theorem tailTrace_5538562 : CollatzResearch.WordTrace tailWord_5538562 prefixEnd_5538562 947981480242421528134541 := by
  unfold tailWord_5538562
  simp only [CollatzResearch.WordTrace]
  refine ⟨50501987940185814981720485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134671967840495506617921293 50501987940185814981720485)
  ·
    refine ⟨9469122738784840309072591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50501987940185814981720485 9469122738784840309072591)
    ·
      refine ⟨14203684108177260463608887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9469122738784840309072591 14203684108177260463608887)
      ·
        refine ⟨21305526162265890695413331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14203684108177260463608887 21305526162265890695413331)
        ·
          refine ⟨31958289243398836043119997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21305526162265890695413331 31958289243398836043119997)
          ·
            refine ⟨11984358466274563516169999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31958289243398836043119997 11984358466274563516169999)
            ·
              refine ⟨17976537699411845274254999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11984358466274563516169999 17976537699411845274254999)
              ·
                refine ⟨26964806549117767911382499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17976537699411845274254999 26964806549117767911382499)
                ·
                  refine ⟨40447209823676651867073749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26964806549117767911382499 40447209823676651867073749)
                  ·
                    refine ⟨947981480242421528134541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40447209823676651867073749 947981480242421528134541)
                    ·
                      rfl

theorem cell23_5538562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_5538562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538562 prefixEnd_5538562 := by exact prefixLift 5538562
  have htrace : WordTrace (prefixWord ++ tailWord_5538562) baseStart_5538562 baseEnd_5538562 := by
    simpa [prefixWord, tailWord_5538562, baseEnd_5538562] using wordTrace_append hprefix tailTrace_5538562
  have hstable : (prefixWord ++ tailWord_5538562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538562).length < 2 ^ (prefixWord ++ tailWord_5538562).sum := by decide
  have hdescent : baseEnd_5538562 < baseStart_5538562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538575 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 5, 4]
def baseStart_5538575 : Nat := 118140960795 + 5538575 * 2 ^ 59
def prefixEnd_5538575 : Nat := 4983230072969 + 3 ^ 40 * 5538575 * 2
def baseEnd_5538575 : Nat := 947983705325257677847021

theorem tailTrace_5538575 : CollatzResearch.WordTrace tailWord_5538575 prefixEnd_5538575 947983705325257677847021 := by
  unfold tailWord_5538575
  simp only [CollatzResearch.WordTrace]
  refine ⟨202008425909696163147105179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134672283939797442098070119 202008425909696163147105179)
  ·
    refine ⟨303012638864544244720657769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202008425909696163147105179 303012638864544244720657769)
    ·
      refine ⟨227259479148408183540493327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303012638864544244720657769 227259479148408183540493327)
      ·
        refine ⟨340889218722612275310739991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227259479148408183540493327 340889218722612275310739991)
        ·
          refine ⟨511333828083918412966109987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340889218722612275310739991 511333828083918412966109987)
          ·
            refine ⟨767000742125877619449164981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511333828083918412966109987 767000742125877619449164981)
            ·
              refine ⟨71906319574301026823359217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 767000742125877619449164981 71906319574301026823359217)
              ·
                refine ⟨53929739680725770117519413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71906319574301026823359217 53929739680725770117519413)
                ·
                  refine ⟨5055913095068040948517445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53929739680725770117519413 5055913095068040948517445)
                  ·
                    refine ⟨947983705325257677847021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5055913095068040948517445 947983705325257677847021)
                    ·
                      rfl

theorem cell23_5538575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 4].length) (baseStart_5538575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538575 prefixEnd_5538575 := by exact prefixLift 5538575
  have htrace : WordTrace (prefixWord ++ tailWord_5538575) baseStart_5538575 baseEnd_5538575 := by
    simpa [prefixWord, tailWord_5538575, baseEnd_5538575] using wordTrace_append hprefix tailTrace_5538575
  have hstable : (prefixWord ++ tailWord_5538575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538575).length < 2 ^ (prefixWord ++ tailWord_5538575).sum := by decide
  have hdescent : baseEnd_5538575 < baseStart_5538575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538592 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 3, 4]
def baseStart_5538592 : Nat := 118140960795 + 5538592 * 2 ^ 59
def prefixEnd_5538592 : Nat := 4983230072969 + 3 ^ 40 * 5538592 * 2
def baseEnd_5538592 : Nat := 947986615048966489009495

theorem tailTrace_5538592 : CollatzResearch.WordTrace tailWord_5538592 prefixEnd_5538592 947986615048966489009495 := by
  unfold tailWord_5538592
  simp only [CollatzResearch.WordTrace]
  refine ⟨101004522975317287525237015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134672697300423050033649353 101004522975317287525237015)
  ·
    refine ⟨151506784462975931287855523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101004522975317287525237015 151506784462975931287855523)
    ·
      refine ⟨227260176694463896931783285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151506784462975931287855523 227260176694463896931783285)
      ·
        refine ⟨21305641565105990337354683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 227260176694463896931783285 21305641565105990337354683)
        ·
          refine ⟨31958462347658985506032025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21305641565105990337354683 31958462347658985506032025)
          ·
            refine ⟨23968846760744239129524019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31958462347658985506032025 23968846760744239129524019)
            ·
              refine ⟨35953270141116358694286029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23968846760744239129524019 35953270141116358694286029)
              ·
                refine ⟨13482476302918634510357261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35953270141116358694286029 13482476302918634510357261)
                ·
                  refine ⟨5055928613594487941383973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13482476302918634510357261 5055928613594487941383973)
                  ·
                    refine ⟨947986615048966489009495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5055928613594487941383973 947986615048966489009495)
                    ·
                      rfl

theorem cell23_5538592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 3, 4].length) (baseStart_5538592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538592 prefixEnd_5538592 := by exact prefixLift 5538592
  have htrace : WordTrace (prefixWord ++ tailWord_5538592) baseStart_5538592 baseEnd_5538592 := by
    simpa [prefixWord, tailWord_5538592, baseEnd_5538592] using wordTrace_append hprefix tailTrace_5538592
  have hstable : (prefixWord ++ tailWord_5538592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538592).length < 2 ^ (prefixWord ++ tailWord_5538592).sum := by decide
  have hdescent : baseEnd_5538592 < baseStart_5538592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538615 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 3]
def baseStart_5538615 : Nat := 118140960795 + 5538615 * 2 ^ 59
def prefixEnd_5538615 : Nat := 4983230072969 + 3 ^ 40 * 5538615 * 2
def baseEnd_5538615 : Nat := 2843971655201952877040879

theorem tailTrace_5538615 : CollatzResearch.WordTrace tailWord_5538615 prefixEnd_5538615 2843971655201952877040879 := by
  unfold tailWord_5538615
  simp only [CollatzResearch.WordTrace]
  refine ⟨202009884829551249978561299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134673256553034166652374199 202009884829551249978561299)
  ·
    refine ⟨303014827244326874967841949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202009884829551249978561299 303014827244326874967841949)
    ·
      refine ⟨113630560216622578112940731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303014827244326874967841949 113630560216622578112940731)
      ·
        refine ⟨170445840324933867169411097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113630560216622578112940731 170445840324933867169411097)
        ·
          refine ⟨127834380243700400377058323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170445840324933867169411097 127834380243700400377058323)
          ·
            refine ⟨191751570365550600565587485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127834380243700400377058323 191751570365550600565587485)
            ·
              refine ⟨71906838887081475212095307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191751570365550600565587485 71906838887081475212095307)
              ·
                refine ⟨107860258330622212818142961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71906838887081475212095307 107860258330622212818142961)
                ·
                  refine ⟨80895193747966659613607221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107860258330622212818142961 80895193747966659613607221)
                  ·
                    refine ⟨7583924413871874338775677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80895193747966659613607221 7583924413871874338775677)
                    ·
                      refine ⟨2843971655201952877040879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7583924413871874338775677 2843971655201952877040879)
                      ·
                        rfl

theorem cell23_5538615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_5538615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538615 prefixEnd_5538615 := by exact prefixLift 5538615
  have htrace : WordTrace (prefixWord ++ tailWord_5538615) baseStart_5538615 baseEnd_5538615 := by
    simpa [prefixWord, tailWord_5538615, baseEnd_5538615] using wordTrace_append hprefix tailTrace_5538615
  have hstable : (prefixWord ++ tailWord_5538615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538615).length < 2 ^ (prefixWord ++ tailWord_5538615).sum := by decide
  have hdescent : baseEnd_5538615 < baseStart_5538615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538649 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 3, 1, 3]
def baseStart_5538649 : Nat := 118140960795 + 5538649 * 2 ^ 59
def prefixEnd_5538649 : Nat := 4983230072969 + 3 ^ 40 * 5538649 * 2
def baseEnd_5538649 : Nat := 2843989113544205744015723

theorem tailTrace_5538649 : CollatzResearch.WordTrace tailWord_5538649 prefixEnd_5538649 2843989113544205744015723 := by
  unfold tailWord_5538649
  simp only [CollatzResearch.WordTrace]
  refine ⟨202011124911428073785299001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134674083274285382523532667 202011124911428073785299001)
  ·
    refine ⟨151508343683571055338974251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202011124911428073785299001 151508343683571055338974251)
    ·
      refine ⟨227262515525356583008461377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151508343683571055338974251 227262515525356583008461377)
      ·
        refine ⟨170446886644017437256346033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227262515525356583008461377 170446886644017437256346033)
        ·
          refine ⟨127835164983013077942259525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170446886644017437256346033 127835164983013077942259525)
          ·
            refine ⟨23969093434314952114173661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127835164983013077942259525 23969093434314952114173661)
            ·
              refine ⟨8988410037868107042815123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23969093434314952114173661 8988410037868107042815123)
              ·
                refine ⟨13482615056802160564222685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8988410037868107042815123 13482615056802160564222685)
                ·
                  refine ⟨5055980646300810211583507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13482615056802160564222685 5055980646300810211583507)
                  ·
                    refine ⟨7583970969451215317375261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5055980646300810211583507 7583970969451215317375261)
                    ·
                      refine ⟨2843989113544205744015723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7583970969451215317375261 2843989113544205744015723)
                      ·
                        rfl

theorem cell23_5538649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_5538649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538649 prefixEnd_5538649 := by exact prefixLift 5538649
  have htrace : WordTrace (prefixWord ++ tailWord_5538649) baseStart_5538649 baseEnd_5538649 := by
    simpa [prefixWord, tailWord_5538649, baseEnd_5538649] using wordTrace_append hprefix tailTrace_5538649
  have hstable : (prefixWord ++ tailWord_5538649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538649).length < 2 ^ (prefixWord ++ tailWord_5538649).sum := by decide
  have hdescent : baseEnd_5538649 < baseStart_5538649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538672 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 2, 6, 2]
def baseStart_5538672 : Nat := 118140960795 + 5538672 * 2 ^ 59
def prefixEnd_5538672 : Nat := 4983230072969 + 3 ^ 40 * 5538672 * 2
def baseEnd_5538672 : Nat := 2844000923599259154028117

theorem tailTrace_5538672 : CollatzResearch.WordTrace tailWord_5538672 prefixEnd_5538672 2844000923599259154028117 := by
  unfold tailWord_5538672
  simp only [CollatzResearch.WordTrace]
  refine ⟨101005981895172374356693135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134674642526896499142257513 101005981895172374356693135)
  ·
    refine ⟨151508972842758561535039703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101005981895172374356693135 151508972842758561535039703)
    ·
      refine ⟨227263459264137842302559555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151508972842758561535039703 227263459264137842302559555)
      ·
        refine ⟨340895188896206763453839333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227263459264137842302559555 340895188896206763453839333)
        ·
          refine ⟨63917847918038768147594875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 340895188896206763453839333 63917847918038768147594875)
          ·
            refine ⟨95876771877058152221392313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63917847918038768147594875 95876771877058152221392313)
            ·
              refine ⟨71907578907793614166044235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95876771877058152221392313 71907578907793614166044235)
              ·
                refine ⟨107861368361690421249066353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71907578907793614166044235 107861368361690421249066353)
                ·
                  refine ⟨80896026271267815936799765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107861368361690421249066353 80896026271267815936799765)
                  ·
                    refine ⟨3792001231465678872037489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80896026271267815936799765 3792001231465678872037489)
                    ·
                      refine ⟨2844000923599259154028117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792001231465678872037489 2844000923599259154028117)
                      ·
                        rfl

theorem cell23_5538672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 6, 2].length) (baseStart_5538672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538672 prefixEnd_5538672 := by exact prefixLift 5538672
  have htrace : WordTrace (prefixWord ++ tailWord_5538672) baseStart_5538672 baseEnd_5538672 := by
    simpa [prefixWord, tailWord_5538672, baseEnd_5538672] using wordTrace_append hprefix tailTrace_5538672
  have hstable : (prefixWord ++ tailWord_5538672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538672).length < 2 ^ (prefixWord ++ tailWord_5538672).sum := by decide
  have hdescent : baseEnd_5538672 < baseStart_5538672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538675 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 5]
def baseStart_5538675 : Nat := 118140960795 + 5538675 * 2 ^ 59
def prefixEnd_5538675 : Nat := 4983230072969 + 3 ^ 40 * 5538675 * 2
def baseEnd_5538675 : Nat := 2844002464041222642290603

theorem tailTrace_5538675 : CollatzResearch.WordTrace tailWord_5538675 prefixEnd_5538675 2844002464041222642290603 := by
  unfold tailWord_5538675
  simp only [CollatzResearch.WordTrace]
  refine ⟨202012073209333880225745479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134674715472889253483830319 202012073209333880225745479)
  ·
    refine ⟨303018109814000820338618219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202012073209333880225745479 303018109814000820338618219)
    ·
      refine ⟨454527164721001230507927329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303018109814000820338618219 454527164721001230507927329)
      ·
        refine ⟨340895373540750922880945497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454527164721001230507927329 340895373540750922880945497)
        ·
          refine ⟨255671530155563192160709123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340895373540750922880945497 255671530155563192160709123)
          ·
            refine ⟨383507295233344788241063685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255671530155563192160709123 383507295233344788241063685)
            ·
              refine ⟨71907617856252147795199441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 383507295233344788241063685 71907617856252147795199441)
              ·
                refine ⟨53930713392189110846399581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71907617856252147795199441 53930713392189110846399581)
                ·
                  refine ⟨20224017522070916567399843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53930713392189110846399581 20224017522070916567399843)
                  ·
                    refine ⟨30336026283106374851099765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20224017522070916567399843 30336026283106374851099765)
                    ·
                      refine ⟨2844002464041222642290603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30336026283106374851099765 2844002464041222642290603)
                      ·
                        rfl

theorem cell23_5538675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_5538675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538675 prefixEnd_5538675 := by exact prefixLift 5538675
  have htrace : WordTrace (prefixWord ++ tailWord_5538675) baseStart_5538675 baseEnd_5538675 := by
    simpa [prefixWord, tailWord_5538675, baseEnd_5538675] using wordTrace_append hprefix tailTrace_5538675
  have hstable : (prefixWord ++ tailWord_5538675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538675).length < 2 ^ (prefixWord ++ tailWord_5538675).sum := by decide
  have hdescent : baseEnd_5538675 < baseStart_5538675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538695 : List Nat := [1, 1, 4, 2, 3, 12]
def baseStart_5538695 : Nat := 118140960795 + 5538695 * 2 ^ 59
def prefixEnd_5538695 : Nat := 4983230072969 + 3 ^ 40 * 5538695 * 2
def baseEnd_5538695 : Nat := 11703756105573302732677

theorem tailTrace_5538695 : CollatzResearch.WordTrace tailWord_5538695 prefixEnd_5538695 11703756105573302732677 := by
  unfold tailWord_5538695
  simp only [CollatzResearch.WordTrace]
  refine ⟨202012802669261423641473539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134675201779507615760982359 202012802669261423641473539)
  ·
    refine ⟨303019204003892135462210309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202012802669261423641473539 303019204003892135462210309)
    ·
      refine ⟨56816100750729775399164433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303019204003892135462210309 56816100750729775399164433)
      ·
        refine ⟨42612075563047331549373325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56816100750729775399164433 42612075563047331549373325)
        ·
          refine ⟨15979528336142749331014997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42612075563047331549373325 15979528336142749331014997)
          ·
            refine ⟨11703756105573302732677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15979528336142749331014997 11703756105573302732677)
            ·
              rfl

theorem cell23_5538695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 12].length) (baseStart_5538695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538695 prefixEnd_5538695 := by exact prefixLift 5538695
  have htrace : WordTrace (prefixWord ++ tailWord_5538695) baseStart_5538695 baseEnd_5538695 := by
    simpa [prefixWord, tailWord_5538695, baseEnd_5538695] using wordTrace_append hprefix tailTrace_5538695
  have hstable : (prefixWord ++ tailWord_5538695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538695).length < 2 ^ (prefixWord ++ tailWord_5538695).sum := by decide
  have hdescent : baseEnd_5538695 < baseStart_5538695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538719 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 4]
def baseStart_5538719 : Nat := 118140960795 + 5538719 * 2 ^ 59
def prefixEnd_5538719 : Nat := 4983230072969 + 3 ^ 40 * 5538719 * 2
def baseEnd_5538719 : Nat := 2844025057190020470140401

theorem tailTrace_5538719 : CollatzResearch.WordTrace tailWord_5538719 prefixEnd_5538719 2844025057190020470140401 := by
  unfold tailWord_5538719
  simp only [CollatzResearch.WordTrace]
  refine ⟨202013678021174475740347211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134675785347449650493564807 202013678021174475740347211)
  ·
    refine ⟨303020517031761713610520817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202013678021174475740347211 303020517031761713610520817)
    ·
      refine ⟨227265387773821285207890613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303020517031761713610520817 227265387773821285207890613)
      ·
        refine ⟨21306130103795745488239745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 227265387773821285207890613 21306130103795745488239745)
        ·
          refine ⟨15979597577846809116179809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21306130103795745488239745 15979597577846809116179809)
          ·
            refine ⟨11984698183385106837134857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15979597577846809116179809 11984698183385106837134857)
            ·
              refine ⟨8988523637538830127851143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11984698183385106837134857 8988523637538830127851143)
              ·
                refine ⟨13482785456308245191776715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8988523637538830127851143 13482785456308245191776715)
                ·
                  refine ⟨20224178184462367787665073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13482785456308245191776715 20224178184462367787665073)
                  ·
                    refine ⟨15168133638346775840748805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20224178184462367787665073 15168133638346775840748805)
                    ·
                      refine ⟨2844025057190020470140401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15168133638346775840748805 2844025057190020470140401)
                      ·
                        rfl

theorem cell23_5538719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_5538719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538719 prefixEnd_5538719 := by exact prefixLift 5538719
  have htrace : WordTrace (prefixWord ++ tailWord_5538719) baseStart_5538719 baseEnd_5538719 := by
    simpa [prefixWord, tailWord_5538719, baseEnd_5538719] using wordTrace_append hprefix tailTrace_5538719
  have hstable : (prefixWord ++ tailWord_5538719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538719).length < 2 ^ (prefixWord ++ tailWord_5538719).sum := by decide
  have hdescent : baseEnd_5538719 < baseStart_5538719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538740 : List Nat := [2, 5, 2, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_5538740 : Nat := 118140960795 + 5538740 * 2 ^ 59
def prefixEnd_5538740 : Nat := 4983230072969 + 3 ^ 40 * 5538740 * 2
def baseEnd_5538740 : Nat := 2844035840283764887977805

theorem tailTrace_5538740 : CollatzResearch.WordTrace tailWord_5538740 prefixEnd_5538740 2844035840283764887977805 := by
  unfold tailWord_5538740
  simp only [CollatzResearch.WordTrace]
  refine ⟨101007221977049198163430837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134676295969398930884574449 101007221977049198163430837)
  ·
    refine ⟨9469427060348362327821641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101007221977049198163430837 9469427060348362327821641)
    ·
      refine ⟨7102070295261271745866231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9469427060348362327821641 7102070295261271745866231)
      ·
        refine ⟨10653105442891907618799347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7102070295261271745866231 10653105442891907618799347)
        ·
          refine ⟨15979658164337861428199021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10653105442891907618799347 15979658164337861428199021)
          ·
            refine ⟨5992371811626698035574633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15979658164337861428199021 5992371811626698035574633)
            ·
              refine ⟨4494278858720023526680975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5992371811626698035574633 4494278858720023526680975)
              ·
                refine ⟨6741418288080035290021463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4494278858720023526680975 6741418288080035290021463)
                ·
                  refine ⟨10112127432120052935032195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6741418288080035290021463 10112127432120052935032195)
                  ·
                    refine ⟨15168191148180079402548293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10112127432120052935032195 15168191148180079402548293)
                    ·
                      refine ⟨2844035840283764887977805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15168191148180079402548293 2844035840283764887977805)
                      ·
                        rfl

theorem cell23_5538740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_5538740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538740 prefixEnd_5538740 := by exact prefixLift 5538740
  have htrace : WordTrace (prefixWord ++ tailWord_5538740) baseStart_5538740 baseEnd_5538740 := by
    simpa [prefixWord, tailWord_5538740, baseEnd_5538740] using wordTrace_append hprefix tailTrace_5538740
  have hstable : (prefixWord ++ tailWord_5538740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538740).length < 2 ^ (prefixWord ++ tailWord_5538740).sum := by decide
  have hdescent : baseEnd_5538740 < baseStart_5538740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538755 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 3, 8]
def baseStart_5538755 : Nat := 118140960795 + 5538755 * 2 ^ 59
def prefixEnd_5538755 : Nat := 4983230072969 + 3 ^ 40 * 5538755 * 2
def baseEnd_5538755 : Nat := 948014514164527443096745

theorem tailTrace_5538755 : CollatzResearch.WordTrace tailWord_5538755 prefixEnd_5538755 948014514164527443096745 := by
  unfold tailWord_5538755
  simp only [CollatzResearch.WordTrace]
  refine ⟨202014991049044053888657719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134676660699362702592438479 202014991049044053888657719)
  ·
    refine ⟨303022486573566080832986579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202014991049044053888657719 303022486573566080832986579)
    ·
      refine ⟨454533729860349121249479869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303022486573566080832986579 454533729860349121249479869)
      ·
        refine ⟨170450148697630920468554951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 454533729860349121249479869 170450148697630920468554951)
        ·
          refine ⟨255675223046446380702832427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170450148697630920468554951 255675223046446380702832427)
          ·
            refine ⟨383512834569669571054248641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255675223046446380702832427 383512834569669571054248641)
            ·
              refine ⟨287634625927252178290686481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383512834569669571054248641 287634625927252178290686481)
              ·
                refine ⟨215725969445439133718014861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287634625927252178290686481 215725969445439133718014861)
                ·
                  refine ⟨80897238542039675144255573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215725969445439133718014861 80897238542039675144255573)
                  ·
                    refine ⟨948014514164527443096745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80897238542039675144255573 948014514164527443096745)
                    ·
                      rfl

theorem cell23_5538755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 8].length) (baseStart_5538755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538755 prefixEnd_5538755 := by exact prefixLift 5538755
  have htrace : WordTrace (prefixWord ++ tailWord_5538755) baseStart_5538755 baseEnd_5538755 := by
    simpa [prefixWord, tailWord_5538755, baseEnd_5538755] using wordTrace_append hprefix tailTrace_5538755
  have hstable : (prefixWord ++ tailWord_5538755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538755).length < 2 ^ (prefixWord ++ tailWord_5538755).sum := by decide
  have hdescent : baseEnd_5538755 < baseStart_5538755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538773 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 1, 3, 3]
def baseStart_5538773 : Nat := 118140960795 + 5538773 * 2 ^ 59
def prefixEnd_5538773 : Nat := 4983230072969 + 3 ^ 40 * 5538773 * 2
def baseEnd_5538773 : Nat := 2844052785145363258865153

theorem tailTrace_5538773 : CollatzResearch.WordTrace tailWord_5538773 prefixEnd_5538773 2844052785145363258865153 := by
  unfold tailWord_5538773
  simp only [CollatzResearch.WordTrace]
  refine ⟨202015647562978842962812973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134677098375319228641875315 202015647562978842962812973)
  ·
    refine ⟨75755867836117066111054865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202015647562978842962812973 75755867836117066111054865)
    ·
      refine ⟨56816900877087799583291149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75755867836117066111054865 56816900877087799583291149)
      ·
        refine ⟨21306337828907924843734181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56816900877087799583291149 21306337828907924843734181)
        ·
          refine ⟨3994938342920235908200159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21306337828907924843734181 3994938342920235908200159)
          ·
            refine ⟨5992407514380353862300239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3994938342920235908200159 5992407514380353862300239)
            ·
              refine ⟨8988611271570530793450359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5992407514380353862300239 8988611271570530793450359)
              ·
                refine ⟨13482916907355796190175539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8988611271570530793450359 13482916907355796190175539)
                ·
                  refine ⟨20224375361033694285263309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13482916907355796190175539 20224375361033694285263309)
                  ·
                    refine ⟨7584140760387635356973741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20224375361033694285263309 7584140760387635356973741)
                    ·
                      refine ⟨2844052785145363258865153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7584140760387635356973741 2844052785145363258865153)
                      ·
                        rfl

theorem cell23_5538773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_5538773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538773 prefixEnd_5538773 := by exact prefixLift 5538773
  have htrace : WordTrace (prefixWord ++ tailWord_5538773) baseStart_5538773 baseEnd_5538773 := by
    simpa [prefixWord, tailWord_5538773, baseEnd_5538773] using wordTrace_append hprefix tailTrace_5538773
  have hstable : (prefixWord ++ tailWord_5538773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538773).length < 2 ^ (prefixWord ++ tailWord_5538773).sum := by decide
  have hdescent : baseEnd_5538773 < baseStart_5538773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538783 : List Nat := [1, 1, 2, 3, 5, 1, 2, 2, 1, 3, 2]
def baseStart_5538783 : Nat := 118140960795 + 5538783 * 2 ^ 59
def prefixEnd_5538783 : Nat := 4983230072969 + 3 ^ 40 * 5538783 * 2
def baseEnd_5538783 : Nat := 2844057919951908219740107

theorem tailTrace_5538783 : CollatzResearch.WordTrace tailWord_5538783 prefixEnd_5538783 2844057919951908219740107 := by
  unfold tailWord_5538783
  simp only [CollatzResearch.WordTrace]
  refine ⟨202016012292942614670677003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134677341528628409780451335 202016012292942614670677003)
  ·
    refine ⟨303024018439413922006015505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202016012292942614670677003 303024018439413922006015505)
    ·
      refine ⟨227268013829560441504511629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303024018439413922006015505 227268013829560441504511629)
      ·
        refine ⟨85225505186085165564191861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227268013829560441504511629 85225505186085165564191861)
        ·
          refine ⟨7989891111195484271642987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85225505186085165564191861 7989891111195484271642987)
          ·
            refine ⟨11984836666793226407464481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7989891111195484271642987 11984836666793226407464481)
            ·
              refine ⟨8988627500094919805598361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11984836666793226407464481 8988627500094919805598361)
              ·
                refine ⟨6741470625071189854198771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8988627500094919805598361 6741470625071189854198771)
                ·
                  refine ⟨10112205937606784781298157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6741470625071189854198771 10112205937606784781298157)
                  ·
                    refine ⟨3792077226602544292986809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10112205937606784781298157 3792077226602544292986809)
                    ·
                      refine ⟨2844057919951908219740107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792077226602544292986809 2844057919951908219740107)
                      ·
                        rfl

theorem cell23_5538783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_5538783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538783 prefixEnd_5538783 := by exact prefixLift 5538783
  have htrace : WordTrace (prefixWord ++ tailWord_5538783) baseStart_5538783 baseEnd_5538783 := by
    simpa [prefixWord, tailWord_5538783, baseEnd_5538783] using wordTrace_append hprefix tailTrace_5538783
  have hstable : (prefixWord ++ tailWord_5538783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538783).length < 2 ^ (prefixWord ++ tailWord_5538783).sum := by decide
  have hdescent : baseEnd_5538783 < baseStart_5538783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538792 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_5538792 : Nat := 118140960795 + 5538792 * 2 ^ 59
def prefixEnd_5538792 : Nat := 4983230072969 + 3 ^ 40 * 5538792 * 2
def baseEnd_5538792 : Nat := 2844062541277798684527565

theorem tailTrace_5538792 : CollatzResearch.WordTrace tailWord_5538792 prefixEnd_5538792 2844062541277798684527565 := by
  unfold tailWord_5538792
  simp only [CollatzResearch.WordTrace]
  refine ⟨101008170274955004603877315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134677560366606672805169753 101008170274955004603877315)
  ·
    refine ⟨151512255412432506905815973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101008170274955004603877315 151512255412432506905815973)
    ·
      refine ⟨28408547889831095044840495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151512255412432506905815973 28408547889831095044840495)
      ·
        refine ⟨42612821834746642567260743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28408547889831095044840495 42612821834746642567260743)
        ·
          refine ⟨63919232752119963850891115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42612821834746642567260743 63919232752119963850891115)
          ·
            refine ⟨95878849128179945776336673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63919232752119963850891115 95878849128179945776336673)
            ·
              refine ⟨71909136846134959332252505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95878849128179945776336673 71909136846134959332252505)
              ·
                refine ⟨53931852634601219499189379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71909136846134959332252505 53931852634601219499189379)
                ·
                  refine ⟨80897778951901829248784069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53931852634601219499189379 80897778951901829248784069)
                  ·
                    refine ⟨15168333553481592984147013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80897778951901829248784069 15168333553481592984147013)
                    ·
                      refine ⟨2844062541277798684527565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15168333553481592984147013 2844062541277798684527565)
                      ·
                        rfl

theorem cell23_5538792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_5538792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538792 prefixEnd_5538792 := by exact prefixLift 5538792
  have htrace : WordTrace (prefixWord ++ tailWord_5538792) baseStart_5538792 baseEnd_5538792 := by
    simpa [prefixWord, tailWord_5538792, baseEnd_5538792] using wordTrace_append hprefix tailTrace_5538792
  have hstable : (prefixWord ++ tailWord_5538792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538792).length < 2 ^ (prefixWord ++ tailWord_5538792).sum := by decide
  have hdescent : baseEnd_5538792 < baseStart_5538792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538830 : List Nat := [4, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2]
def baseStart_5538830 : Nat := 118140960795 + 5538830 * 2 ^ 59
def prefixEnd_5538830 : Nat := 4983230072969 + 3 ^ 40 * 5538830 * 2
def baseEnd_5538830 : Nat := 2844082053542669535852391

theorem tailTrace_5538830 : CollatzResearch.WordTrace tailWord_5538830 prefixEnd_5538830 2844082053542669535852391 := by
  unfold tailWord_5538830
  simp only [CollatzResearch.WordTrace]
  refine ⟨25252215815471542712204743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134678484349181561131758629 25252215815471542712204743)
  ·
    refine ⟨37878323723207314068307115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25252215815471542712204743 37878323723207314068307115)
    ·
      refine ⟨56817485584810971102460673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37878323723207314068307115 56817485584810971102460673)
      ·
        refine ⟨42613114188608228326845505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56817485584810971102460673 42613114188608228326845505)
        ·
          refine ⟨31959835641456171245134129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42613114188608228326845505 31959835641456171245134129)
          ·
            refine ⟨23969876731092128433850597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31959835641456171245134129 23969876731092128433850597)
            ·
              refine ⟨4494351887079774081346987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23969876731092128433850597 4494351887079774081346987)
              ·
                refine ⟨6741527830619661122020481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4494351887079774081346987 6741527830619661122020481)
                ·
                  refine ⟨5056145872964745841515361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6741527830619661122020481 5056145872964745841515361)
                  ·
                    refine ⟨3792109404723559381136521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5056145872964745841515361 3792109404723559381136521)
                    ·
                      refine ⟨2844082053542669535852391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792109404723559381136521 2844082053542669535852391)
                      ·
                        rfl

theorem cell23_5538830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_5538830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538830 prefixEnd_5538830 := by exact prefixLift 5538830
  have htrace : WordTrace (prefixWord ++ tailWord_5538830) baseStart_5538830 baseEnd_5538830 := by
    simpa [prefixWord, tailWord_5538830, baseEnd_5538830] using wordTrace_append hprefix tailTrace_5538830
  have hstable : (prefixWord ++ tailWord_5538830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538830).length < 2 ^ (prefixWord ++ tailWord_5538830).sum := by decide
  have hdescent : baseEnd_5538830 < baseStart_5538830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538834 : List Nat := [3, 2, 5, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_5538834 : Nat := 118140960795 + 5538834 * 2 ^ 59
def prefixEnd_5538834 : Nat := 4983230072969 + 3 ^ 40 * 5538834 * 2
def baseEnd_5538834 : Nat := 2844084107465287520202373

theorem tailTrace_5538834 : CollatzResearch.WordTrace tailWord_5538834 prefixEnd_5538834 2844084107465287520202373 := by
  unfold tailWord_5538834
  simp only [CollatzResearch.WordTrace]
  refine ⟨50504468103939462595195889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134678581610505233587189037 50504468103939462595195889)
  ·
    refine ⟨37878351077954596946396917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50504468103939462595195889 37878351077954596946396917)
    ·
      refine ⟨3551095413558243463724711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37878351077954596946396917 3551095413558243463724711)
      ·
        refine ⟨5326643120337365195587067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3551095413558243463724711 5326643120337365195587067)
        ·
          refine ⟨7989964680506047793380601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5326643120337365195587067 7989964680506047793380601)
          ·
            refine ⟨5992473510379535845035451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7989964680506047793380601 5992473510379535845035451)
            ·
              refine ⟨8988710265569303767553177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5992473510379535845035451 8988710265569303767553177)
              ·
                refine ⟨6741532699176977825664883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8988710265569303767553177 6741532699176977825664883)
                ·
                  refine ⟨10112299048765466738497325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6741532699176977825664883 10112299048765466738497325)
                  ·
                    refine ⟨3792112143287050026936497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10112299048765466738497325 3792112143287050026936497)
                    ·
                      refine ⟨2844084107465287520202373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792112143287050026936497 2844084107465287520202373)
                      ·
                        rfl

theorem cell23_5538834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_5538834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538834 prefixEnd_5538834 := by exact prefixLift 5538834
  have htrace : WordTrace (prefixWord ++ tailWord_5538834) baseStart_5538834 baseEnd_5538834 := by
    simpa [prefixWord, tailWord_5538834, baseEnd_5538834] using wordTrace_append hprefix tailTrace_5538834
  have hstable : (prefixWord ++ tailWord_5538834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538834).length < 2 ^ (prefixWord ++ tailWord_5538834).sum := by decide
  have hdescent : baseEnd_5538834 < baseStart_5538834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538842 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_5538842 : Nat := 118140960795 + 5538842 * 2 ^ 59
def prefixEnd_5538842 : Nat := 4983230072969 + 3 ^ 40 * 5538842 * 2
def baseEnd_5538842 : Nat := 2844088215310523488902335

theorem tailTrace_5538842 : CollatzResearch.WordTrace tailWord_5538842 prefixEnd_5538842 2844088215310523488902335 := by
  unfold tailWord_5538842
  simp only [CollatzResearch.WordTrace]
  refine ⟨50504541049932216936768695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134678776133152578498049853 50504541049932216936768695)
  ·
    refine ⟨75756811574898325405153043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50504541049932216936768695 75756811574898325405153043)
    ·
      refine ⟨113635217362347488107729565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75756811574898325405153043 113635217362347488107729565)
      ·
        refine ⟨42613206510880308040398587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113635217362347488107729565 42613206510880308040398587)
        ·
          refine ⟨63919809766320462060597881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42613206510880308040398587 63919809766320462060597881)
          ·
            refine ⟨47939857324740346545448411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63919809766320462060597881 47939857324740346545448411)
            ·
              refine ⟨71909785987110519818172617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47939857324740346545448411 71909785987110519818172617)
              ·
                refine ⟨53932339490332889863629463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71909785987110519818172617 53932339490332889863629463)
                ·
                  refine ⟨80898509235499334795444195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53932339490332889863629463 80898509235499334795444195)
                  ·
                    refine ⟨121347763853249002193166293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80898509235499334795444195 121347763853249002193166293)
                    ·
                      refine ⟨2844088215310523488902335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121347763853249002193166293 2844088215310523488902335)
                      ·
                        rfl

theorem cell23_5538842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_5538842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538842 prefixEnd_5538842 := by exact prefixLift 5538842
  have htrace : WordTrace (prefixWord ++ tailWord_5538842) baseStart_5538842 baseEnd_5538842 := by
    simpa [prefixWord, tailWord_5538842, baseEnd_5538842] using wordTrace_append hprefix tailTrace_5538842
  have hstable : (prefixWord ++ tailWord_5538842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538842).length < 2 ^ (prefixWord ++ tailWord_5538842).sum := by decide
  have hdescent : baseEnd_5538842 < baseStart_5538842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538849 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 2, 5]
def baseStart_5538849 : Nat := 118140960795 + 5538849 * 2 ^ 59
def prefixEnd_5538849 : Nat := 4983230072969 + 3 ^ 40 * 5538849 * 2
def baseEnd_5538849 : Nat := 948030603225034987171601

theorem tailTrace_5538849 : CollatzResearch.WordTrace tailWord_5538849 prefixEnd_5538849 948030603225034987171601 := by
  unfold tailWord_5538849
  simp only [CollatzResearch.WordTrace]
  refine ⟨202018419510703507942579601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134678946340469005295053067 202018419510703507942579601)
  ·
    refine ⟨151513814633027630956934701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202018419510703507942579601 151513814633027630956934701)
    ·
      refine ⟨56817680487385361608850513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151513814633027630956934701 56817680487385361608850513)
      ·
        refine ⟨42613260365539021206637885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56817680487385361608850513 42613260365539021206637885)
        ·
          refine ⟨15979972637077132952489207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42613260365539021206637885 15979972637077132952489207)
          ·
            refine ⟨23969958955615699428733811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15979972637077132952489207 23969958955615699428733811)
            ·
              refine ⟨35954938433423549143100717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23969958955615699428733811 35954938433423549143100717)
              ·
                refine ⟨13483101912533830928662769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35954938433423549143100717 13483101912533830928662769)
                ·
                  refine ⟨10112326434400373196497077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13483101912533830928662769 10112326434400373196497077)
                  ·
                    refine ⟨948030603225034987171601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10112326434400373196497077 948030603225034987171601)
                    ·
                      rfl

theorem cell23_5538849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_5538849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538849 prefixEnd_5538849 := by exact prefixLift 5538849
  have htrace : WordTrace (prefixWord ++ tailWord_5538849) baseStart_5538849 baseEnd_5538849 := by
    simpa [prefixWord, tailWord_5538849, baseEnd_5538849] using wordTrace_append hprefix tailTrace_5538849
  have hstable : (prefixWord ++ tailWord_5538849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538849).length < 2 ^ (prefixWord ++ tailWord_5538849).sum := by decide
  have hdescent : baseEnd_5538849 < baseStart_5538849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538870 : List Nat := [5, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_5538870 : Nat := 118140960795 + 5538870 * 2 ^ 59
def prefixEnd_5538870 : Nat := 4983230072969 + 3 ^ 40 * 5538870 * 2
def baseEnd_5538870 : Nat := 316011399196538819928023

theorem tailTrace_5538870 : CollatzResearch.WordTrace tailWord_5538870 prefixEnd_5538870 316011399196538819928023 := by
  unfold tailWord_5538870
  simp only [CollatzResearch.WordTrace]
  refine ⟨12626199090226714283068379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134679456962418285686062709 12626199090226714283068379)
  ·
    refine ⟨18939298635340071424602569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12626199090226714283068379 18939298635340071424602569)
    ·
      refine ⟨14204473976505053568451927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18939298635340071424602569 14204473976505053568451927)
      ·
        refine ⟨21306710964757580352677891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14204473976505053568451927 21306710964757580352677891)
        ·
          refine ⟨31960066447136370529016837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21306710964757580352677891 31960066447136370529016837)
          ·
            refine ⟨5992512458838069474190657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31960066447136370529016837 5992512458838069474190657)
            ·
              refine ⟨4494384344128552105642993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5992512458838069474190657 4494384344128552105642993)
              ·
                refine ⟨3370788258096414079232245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4494384344128552105642993 3370788258096414079232245)
                ·
                  refine ⟨316011399196538819928023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3370788258096414079232245 316011399196538819928023)
                  ·
                    rfl

theorem cell23_5538870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_5538870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538870 prefixEnd_5538870 := by exact prefixLift 5538870
  have htrace : WordTrace (prefixWord ++ tailWord_5538870) baseStart_5538870 baseEnd_5538870 := by
    simpa [prefixWord, tailWord_5538870, baseEnd_5538870] using wordTrace_append hprefix tailTrace_5538870
  have hstable : (prefixWord ++ tailWord_5538870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538870).length < 2 ^ (prefixWord ++ tailWord_5538870).sum := by decide
  have hdescent : baseEnd_5538870 < baseStart_5538870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538879 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 3, 4]
def baseStart_5538879 : Nat := 118140960795 + 5538879 * 2 ^ 59
def prefixEnd_5538879 : Nat := 4983230072969 + 3 ^ 40 * 5538879 * 2
def baseEnd_5538879 : Nat := 948035738031579948046555

theorem tailTrace_5538879 : CollatzResearch.WordTrace tailWord_5538879 prefixEnd_5538879 948035738031579948046555 := by
  unfold tailWord_5538879
  simp only [CollatzResearch.WordTrace]
  refine ⟨202019513700594823066171691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134679675800396548710781127 202019513700594823066171691)
  ·
    refine ⟨303029270550892234599257537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202019513700594823066171691 303029270550892234599257537)
    ·
      refine ⟨227271952913169175949443153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303029270550892234599257537 227271952913169175949443153)
      ·
        refine ⟨170453964684876881962082365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227271952913169175949443153 170453964684876881962082365)
        ·
          refine ⟨63920236756828830735780887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170453964684876881962082365 63920236756828830735780887)
          ·
            refine ⟨95880355135243246103671331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63920236756828830735780887 95880355135243246103671331)
            ·
              refine ⟨143820532702864869155506997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95880355135243246103671331 143820532702864869155506997)
              ·
                refine ⟨13483174940893581483328781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143820532702864869155506997 13483174940893581483328781)
                ·
                  refine ⟨5056190602835093056248293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13483174940893581483328781 5056190602835093056248293)
                  ·
                    refine ⟨948035738031579948046555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5056190602835093056248293 948035738031579948046555)
                    ·
                      rfl

theorem cell23_5538879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 4].length) (baseStart_5538879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538879 prefixEnd_5538879 := by exact prefixLift 5538879
  have htrace : WordTrace (prefixWord ++ tailWord_5538879) baseStart_5538879 baseEnd_5538879 := by
    simpa [prefixWord, tailWord_5538879, baseEnd_5538879] using wordTrace_append hprefix tailTrace_5538879
  have hstable : (prefixWord ++ tailWord_5538879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538879).length < 2 ^ (prefixWord ++ tailWord_5538879).sum := by decide
  have hdescent : baseEnd_5538879 < baseStart_5538879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538892 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 10]
def baseStart_5538892 : Nat := 118140960795 + 5538892 * 2 ^ 59
def prefixEnd_5538892 : Nat := 4983230072969 + 3 ^ 40 * 5538892 * 2
def baseEnd_5538892 : Nat := 316012654371472032586345

theorem tailTrace_5538892 : CollatzResearch.WordTrace tailWord_5538892 prefixEnd_5538892 316012654371472032586345 := by
  unfold tailWord_5538892
  simp only [CollatzResearch.WordTrace]
  refine ⟨101009993924773863143197465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134679991899698484190929953 101009993924773863143197465)
  ·
    refine ⟨75757495443580397357398099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101009993924773863143197465 75757495443580397357398099)
    ·
      refine ⟨113636243165370596036097149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75757495443580397357398099 113636243165370596036097149)
      ·
        refine ⟨42613591187013973513536431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113636243165370596036097149 42613591187013973513536431)
        ·
          refine ⟨63920386780520960270304647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42613591187013973513536431 63920386780520960270304647)
          ·
            refine ⟨95880580170781440405456971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63920386780520960270304647 95880580170781440405456971)
            ·
              refine ⟨143820870256172160608185457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95880580170781440405456971 143820870256172160608185457)
              ·
                refine ⟨107865652692129120456139093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143820870256172160608185457 107865652692129120456139093)
                ·
                  refine ⟨316012654371472032586345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 107865652692129120456139093 316012654371472032586345)
                  ·
                    rfl

theorem cell23_5538892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_5538892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538892 prefixEnd_5538892 := by exact prefixLift 5538892
  have htrace : WordTrace (prefixWord ++ tailWord_5538892) baseStart_5538892 baseEnd_5538892 := by
    simpa [prefixWord, tailWord_5538892, baseEnd_5538892] using wordTrace_append hprefix tailTrace_5538892
  have hstable : (prefixWord ++ tailWord_5538892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538892).length < 2 ^ (prefixWord ++ tailWord_5538892).sum := by decide
  have hdescent : baseEnd_5538892 < baseStart_5538892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538926 : List Nat := [4, 1, 2, 2, 1, 2, 3, 2, 6]
def baseStart_5538926 : Nat := 118140960795 + 5538926 * 2 ^ 59
def prefixEnd_5538926 : Nat := 4983230072969 + 3 ^ 40 * 5538926 * 2
def baseEnd_5538926 : Nat := 316014594187277906694661

theorem tailTrace_5538926 : CollatzResearch.WordTrace tailWord_5538926 prefixEnd_5538926 316014594187277906694661 := by
  unfold tailWord_5538926
  simp only [CollatzResearch.WordTrace]
  refine ⟨25252653491428068761641579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134680818620949700062088421 25252653491428068761641579)
  ·
    refine ⟨37878980237142103142462369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25252653491428068761641579 37878980237142103142462369)
    ·
      refine ⟨28409235177856577356846777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37878980237142103142462369 28409235177856577356846777)
      ·
        refine ⟨21306926383392433017635083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28409235177856577356846777 21306926383392433017635083)
        ·
          refine ⟨31960389575088649526452625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21306926383392433017635083 31960389575088649526452625)
          ·
            refine ⟨23970292181316487144839469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31960389575088649526452625 23970292181316487144839469)
            ·
              refine ⟨8988859567993682679314801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23970292181316487144839469 8988859567993682679314801)
              ·
                refine ⟨6741644675995262009486101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8988859567993682679314801 6741644675995262009486101)
                ·
                  refine ⟨316014594187277906694661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6741644675995262009486101 316014594187277906694661)
                  ·
                    rfl

theorem cell23_5538926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_5538926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538926 prefixEnd_5538926 := by exact prefixLift 5538926
  have htrace : WordTrace (prefixWord ++ tailWord_5538926) baseStart_5538926 baseEnd_5538926 := by
    simpa [prefixWord, tailWord_5538926, baseEnd_5538926] using wordTrace_append hprefix tailTrace_5538926
  have hstable : (prefixWord ++ tailWord_5538926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538926).length < 2 ^ (prefixWord ++ tailWord_5538926).sum := by decide
  have hdescent : baseEnd_5538926 < baseStart_5538926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538936 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 3, 1, 3]
def baseStart_5538936 : Nat := 118140960795 + 5538936 * 2 ^ 59
def prefixEnd_5538936 : Nat := 4983230072969 + 3 ^ 40 * 5538936 * 2
def baseEnd_5538936 : Nat := 2844136482492046121126903

theorem tailTrace_5538936 : CollatzResearch.WordTrace tailWord_5538936 prefixEnd_5538936 2844136482492046121126903 := by
  unfold tailWord_5538936
  simp only [CollatzResearch.WordTrace]
  refine ⟨101010796330694160900498331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134681061774258881200664441 101010796330694160900498331)
  ·
    refine ⟨151516194496041241350747497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101010796330694160900498331 151516194496041241350747497)
    ·
      refine ⟨113637145872030931013060623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151516194496041241350747497 113637145872030931013060623)
      ·
        refine ⟨170455718808046396519590935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113637145872030931013060623 170455718808046396519590935)
        ·
          refine ⟨255683578212069594779386403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170455718808046396519590935 255683578212069594779386403)
          ·
            refine ⟨383525367318104392169079605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255683578212069594779386403 383525367318104392169079605)
            ·
              refine ⟨35955503186072286765851213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 383525367318104392169079605 35955503186072286765851213)
              ·
                refine ⟨13483313694777107537194205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35955503186072286765851213 13483313694777107537194205)
                ·
                  refine ⟨5056242635541415326447827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13483313694777107537194205 5056242635541415326447827)
                  ·
                    refine ⟨7584363953312122989671741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5056242635541415326447827 7584363953312122989671741)
                    ·
                      refine ⟨2844136482492046121126903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7584363953312122989671741 2844136482492046121126903)
                      ·
                        rfl

theorem cell23_5538936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_5538936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538936 prefixEnd_5538936 := by exact prefixLift 5538936
  have htrace : WordTrace (prefixWord ++ tailWord_5538936) baseStart_5538936 baseEnd_5538936 := by
    simpa [prefixWord, tailWord_5538936, baseEnd_5538936] using wordTrace_append hprefix tailTrace_5538936
  have hstable : (prefixWord ++ tailWord_5538936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538936).length < 2 ^ (prefixWord ++ tailWord_5538936).sum := by decide
  have hdescent : baseEnd_5538936 < baseStart_5538936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538976 : List Nat := [2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 4]
def baseStart_5538976 : Nat := 118140960795 + 5538976 * 2 ^ 59
def prefixEnd_5538976 : Nat := 4983230072969 + 3 ^ 40 * 5538976 * 2
def baseEnd_5538976 : Nat := 2844157021718225964626719

theorem tailTrace_5538976 : CollatzResearch.WordTrace tailWord_5538976 prefixEnd_5538976 2844157021718225964626719 := by
  unfold tailWord_5538976
  simp only [CollatzResearch.WordTrace]
  refine ⟨101011525790621704316226391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134682034387495605754968521 101011525790621704316226391)
  ·
    refine ⟨151517288685932556474339587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101011525790621704316226391 151517288685932556474339587)
    ·
      refine ⟨227275933028898834711509381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151517288685932556474339587 227275933028898834711509381)
      ·
        refine ⟨42614237442918531508408009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227275933028898834711509381 42614237442918531508408009)
        ·
          refine ⟨31960678082188898631306007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42614237442918531508408009 31960678082188898631306007)
          ·
            refine ⟨47941017123283347946959011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31960678082188898631306007 47941017123283347946959011)
            ·
              refine ⟨71911525684925021920438517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47941017123283347946959011 71911525684925021920438517)
              ·
                refine ⟨6741705532961720805041111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71911525684925021920438517 6741705532961720805041111)
                ·
                  refine ⟨10112558299442581207561667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6741705532961720805041111 10112558299442581207561667)
                  ·
                    refine ⟨15168837449163871811342501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10112558299442581207561667 15168837449163871811342501)
                    ·
                      refine ⟨2844157021718225964626719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15168837449163871811342501 2844157021718225964626719)
                      ·
                        rfl

theorem cell23_5538976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_5538976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538976 prefixEnd_5538976 := by exact prefixLift 5538976
  have htrace : WordTrace (prefixWord ++ tailWord_5538976) baseStart_5538976 baseEnd_5538976 := by
    simpa [prefixWord, tailWord_5538976, baseEnd_5538976] using wordTrace_append hprefix tailTrace_5538976
  have hstable : (prefixWord ++ tailWord_5538976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538976).length < 2 ^ (prefixWord ++ tailWord_5538976).sum := by decide
  have hdescent : baseEnd_5538976 < baseStart_5538976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5538999 : List Nat := [1, 1, 3, 1, 4, 1, 4, 8]
def baseStart_5538999 : Nat := 118140960795 + 5538999 * 2 ^ 59
def prefixEnd_5538999 : Nat := 4983230072969 + 3 ^ 40 * 5538999 * 2
def baseEnd_5538999 : Nat := 105339586361973310171819

theorem tailTrace_5538999 : CollatzResearch.WordTrace tailWord_5538999 prefixEnd_5538999 105339586361973310171819 := by
  unfold tailWord_5538999
  simp only [CollatzResearch.WordTrace]
  refine ⟨202023890460160083560540051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134682593640106722373693367 202023890460160083560540051)
  ·
    refine ⟨303035835690240125340810077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202023890460160083560540051 303035835690240125340810077)
    ·
      refine ⟨113638438383840047002803779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303035835690240125340810077 113638438383840047002803779)
      ·
        refine ⟨170457657575760070504205669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113638438383840047002803779 170457657575760070504205669)
        ·
          refine ⟨31960810795455013219538563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170457657575760070504205669 31960810795455013219538563)
          ·
            refine ⟨47941216193182519829307845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31960810795455013219538563 47941216193182519829307845)
            ·
              refine ⟨8988978036221722467995221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47941216193182519829307845 8988978036221722467995221)
              ·
                refine ⟨105339586361973310171819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8988978036221722467995221 105339586361973310171819)
                ·
                  rfl

theorem cell23_5538999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 8].length) (baseStart_5538999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5538999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5538999 prefixEnd_5538999 := by exact prefixLift 5538999
  have htrace : WordTrace (prefixWord ++ tailWord_5538999) baseStart_5538999 baseEnd_5538999 := by
    simpa [prefixWord, tailWord_5538999, baseEnd_5538999] using wordTrace_append hprefix tailTrace_5538999
  have hstable : (prefixWord ++ tailWord_5538999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5538999).length < 2 ^ (prefixWord ++ tailWord_5538999).sum := by decide
  have hdescent : baseEnd_5538999 < baseStart_5538999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5538999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539006 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_5539006 : Nat := 118140960795 + 5539006 * 2 ^ 59
def prefixEnd_5539006 : Nat := 4983230072969 + 3 ^ 40 * 5539006 * 2
def baseEnd_5539006 : Nat := 2844172426137860847251581

theorem tailTrace_5539006 : CollatzResearch.WordTrace tailWord_5539006 prefixEnd_5539006 2844172426137860847251581 := by
  unfold tailWord_5539006
  simp only [CollatzResearch.WordTrace]
  refine ⟨25253018221391840469505609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134682763847423149170696581 25253018221391840469505609)
  ·
    refine ⟨18939763666043880352129207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25253018221391840469505609 18939763666043880352129207)
    ·
      refine ⟨28409645499065820528193811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18939763666043880352129207 28409645499065820528193811)
      ·
        refine ⟨42614468248598730792290717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28409645499065820528193811 42614468248598730792290717)
        ·
          refine ⟨15980425593224524047109019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42614468248598730792290717 15980425593224524047109019)
          ·
            refine ⟨23970638389836786070663529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15980425593224524047109019 23970638389836786070663529)
            ·
              refine ⟨17977978792377589552997647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23970638389836786070663529 17977978792377589552997647)
              ·
                refine ⟨26966968188566384329496471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17977978792377589552997647 26966968188566384329496471)
                ·
                  refine ⟨40450452282849576494244707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26966968188566384329496471 40450452282849576494244707)
                  ·
                    refine ⟨60675678424274364741367061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40450452282849576494244707 60675678424274364741367061)
                    ·
                      refine ⟨2844172426137860847251581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60675678424274364741367061 2844172426137860847251581)
                      ·
                        rfl

theorem cell23_5539006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_5539006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539006 prefixEnd_5539006 := by exact prefixLift 5539006
  have htrace : WordTrace (prefixWord ++ tailWord_5539006) baseStart_5539006 baseEnd_5539006 := by
    simpa [prefixWord, tailWord_5539006, baseEnd_5539006] using wordTrace_append hprefix tailTrace_5539006
  have hstable : (prefixWord ++ tailWord_5539006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539006).length < 2 ^ (prefixWord ++ tailWord_5539006).sum := by decide
  have hdescent : baseEnd_5539006 < baseStart_5539006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539039 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 5]
def baseStart_5539039 : Nat := 118140960795 + 5539039 * 2 ^ 59
def prefixEnd_5539039 : Nat := 4983230072969 + 3 ^ 40 * 5539039 * 2
def baseEnd_5539039 : Nat := 2844189370999459218138929

theorem tailTrace_5539039 : CollatzResearch.WordTrace tailWord_5539039 prefixEnd_5539039 2844189370999459218138929 := by
  unfold tailWord_5539039
  simp only [CollatzResearch.WordTrace]
  refine ⟨202025349380015170391996171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134683566253343446927997447 202025349380015170391996171)
  ·
    refine ⟨303038024070022755587994257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202025349380015170391996171 303038024070022755587994257)
    ·
      refine ⟨227278518052517066690995693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303038024070022755587994257 227278518052517066690995693)
      ·
        refine ⟨85229444269693900009123385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227278518052517066690995693 85229444269693900009123385)
        ·
          refine ⟨63922083202270425006842539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85229444269693900009123385 63922083202270425006842539)
          ·
            refine ⟨95883124803405637510263809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63922083202270425006842539 95883124803405637510263809)
            ·
              refine ⟨71912343602554228132697857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95883124803405637510263809 71912343602554228132697857)
              ·
                refine ⟨53934257701915671099523393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71912343602554228132697857 53934257701915671099523393)
                ·
                  refine ⟨40450693276436753324642545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53934257701915671099523393 40450693276436753324642545)
                  ·
                    refine ⟨30338019957327564993481909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40450693276436753324642545 30338019957327564993481909)
                    ·
                      refine ⟨2844189370999459218138929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30338019957327564993481909 2844189370999459218138929)
                      ·
                        rfl

theorem cell23_5539039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_5539039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539039 prefixEnd_5539039 := by exact prefixLift 5539039
  have htrace : WordTrace (prefixWord ++ tailWord_5539039) baseStart_5539039 baseEnd_5539039 := by
    simpa [prefixWord, tailWord_5539039, baseEnd_5539039] using wordTrace_append hprefix tailTrace_5539039
  have hstable : (prefixWord ++ tailWord_5539039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539039).length < 2 ^ (prefixWord ++ tailWord_5539039).sum := by decide
  have hdescent : baseEnd_5539039 < baseStart_5539039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539059 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 1, 8]
def baseStart_5539059 : Nat := 118140960795 + 5539059 * 2 ^ 59
def prefixEnd_5539059 : Nat := 4983230072969 + 3 ^ 40 * 5539059 * 2
def baseEnd_5539059 : Nat := 948066546870849713296279

theorem tailTrace_5539059 : CollatzResearch.WordTrace tailWord_5539059 prefixEnd_5539059 948066546870849713296279 := by
  unfold tailWord_5539059
  simp only [CollatzResearch.WordTrace]
  refine ⟨202026078839942713807724231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134684052559961809205149487 202026078839942713807724231)
  ·
    refine ⟨303039118259914070711586347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202026078839942713807724231 303039118259914070711586347)
    ·
      refine ⟨454558677389871106067379521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303039118259914070711586347 454558677389871106067379521)
      ·
        refine ⟨340919008042403329550534641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454558677389871106067379521 340919008042403329550534641)
        ·
          refine ⟨255689256031802497162900981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340919008042403329550534641 255689256031802497162900981)
          ·
            refine ⟨23970867752981484109021967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 255689256031802497162900981 23970867752981484109021967)
            ·
              refine ⟨35956301629472226163532951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23970867752981484109021967 35956301629472226163532951)
              ·
                refine ⟨53934452444208339245299427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35956301629472226163532951 53934452444208339245299427)
                ·
                  refine ⟨80901678666312508867949141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53934452444208339245299427 80901678666312508867949141)
                  ·
                    refine ⟨948066546870849713296279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80901678666312508867949141 948066546870849713296279)
                    ·
                      rfl

theorem cell23_5539059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 8].length) (baseStart_5539059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539059 prefixEnd_5539059 := by exact prefixLift 5539059
  have htrace : WordTrace (prefixWord ++ tailWord_5539059) baseStart_5539059 baseEnd_5539059 := by
    simpa [prefixWord, tailWord_5539059, baseEnd_5539059] using wordTrace_append hprefix tailTrace_5539059
  have hstable : (prefixWord ++ tailWord_5539059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539059).length < 2 ^ (prefixWord ++ tailWord_5539059).sum := by decide
  have hdescent : baseEnd_5539059 < baseStart_5539059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539070 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_5539070 : Nat := 118140960795 + 5539070 * 2 ^ 59
def prefixEnd_5539070 : Nat := 4983230072969 + 3 ^ 40 * 5539070 * 2
def baseEnd_5539070 : Nat := 2844205288899748596851287

theorem tailTrace_5539070 : CollatzResearch.WordTrace tailWord_5539070 prefixEnd_5539070 2844205288899748596851287 := by
  unfold tailWord_5539070
  simp only [CollatzResearch.WordTrace]
  refine ⟨25253310005362857835796833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134684320028601908457583109 25253310005362857835796833)
  ·
    refine ⟨18939982504022143376847625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25253310005362857835796833 18939982504022143376847625)
    ·
      refine ⟨14204986878016607532635719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18939982504022143376847625 14204986878016607532635719)
      ·
        refine ⟨21307480317024911298953579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14204986878016607532635719 21307480317024911298953579)
        ·
          refine ⟨31961220475537366948430369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21307480317024911298953579 31961220475537366948430369)
          ·
            refine ⟨23970915356653025211322777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31961220475537366948430369 23970915356653025211322777)
            ·
              refine ⟨17978186517489768908492083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23970915356653025211322777 17978186517489768908492083)
              ·
                refine ⟨26967279776234653362738125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17978186517489768908492083 26967279776234653362738125)
                ·
                  refine ⟨10112729916087995011026797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26967279776234653362738125 10112729916087995011026797)
                  ·
                    refine ⟨3792273718532998129135049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10112729916087995011026797 3792273718532998129135049)
                    ·
                      refine ⟨2844205288899748596851287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792273718532998129135049 2844205288899748596851287)
                      ·
                        rfl

theorem cell23_5539070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_5539070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539070 prefixEnd_5539070 := by exact prefixLift 5539070
  have htrace : WordTrace (prefixWord ++ tailWord_5539070) baseStart_5539070 baseEnd_5539070 := by
    simpa [prefixWord, tailWord_5539070, baseEnd_5539070] using wordTrace_append hprefix tailTrace_5539070
  have hstable : (prefixWord ++ tailWord_5539070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539070).length < 2 ^ (prefixWord ++ tailWord_5539070).sum := by decide
  have hdescent : baseEnd_5539070 < baseStart_5539070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539083 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 1, 4, 2]
def baseStart_5539083 : Nat := 118140960795 + 5539083 * 2 ^ 59
def prefixEnd_5539083 : Nat := 4983230072969 + 3 ^ 40 * 5539083 * 2
def baseEnd_5539083 : Nat := 2844211964148257045988727

theorem tailTrace_5539083 : CollatzResearch.WordTrace tailWord_5539083 prefixEnd_5539083 2844211964148257045988727 := by
  unfold tailWord_5539083
  simp only [CollatzResearch.WordTrace]
  refine ⟨202026954191855765906597903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134684636127903843937731935 202026954191855765906597903)
  ·
    refine ⟨303040431287783648859896855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202026954191855765906597903 303040431287783648859896855)
    ·
      refine ⟨454560646931675473289845283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303040431287783648859896855 454560646931675473289845283)
      ·
        refine ⟨681840970397513209934767925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454560646931675473289845283 681840970397513209934767925)
        ·
          refine ⟨63922590974766863431384493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 681840970397513209934767925 63922590974766863431384493)
          ·
            refine ⟨23970971615537573786769185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63922590974766863431384493 23970971615537573786769185)
            ·
              refine ⟨17978228711653180340076889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23970971615537573786769185 17978228711653180340076889)
              ·
                refine ⟨13483671533739885255057667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17978228711653180340076889 13483671533739885255057667)
                ·
                  refine ⟨20225507300609827882586501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13483671533739885255057667 20225507300609827882586501)
                  ·
                    refine ⟨3792282618864342727984969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20225507300609827882586501 3792282618864342727984969)
                    ·
                      refine ⟨2844211964148257045988727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792282618864342727984969 2844211964148257045988727)
                      ·
                        rfl

theorem cell23_5539083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 4, 2].length) (baseStart_5539083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539083 prefixEnd_5539083 := by exact prefixLift 5539083
  have htrace : WordTrace (prefixWord ++ tailWord_5539083) baseStart_5539083 baseEnd_5539083 := by
    simpa [prefixWord, tailWord_5539083, baseEnd_5539083] using wordTrace_append hprefix tailTrace_5539083
  have hstable : (prefixWord ++ tailWord_5539083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539083).length < 2 ^ (prefixWord ++ tailWord_5539083).sum := by decide
  have hdescent : baseEnd_5539083 < baseStart_5539083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539089 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 9]
def baseStart_5539089 : Nat := 118140960795 + 5539089 * 2 ^ 59
def prefixEnd_5539089 : Nat := 4983230072969 + 3 ^ 40 * 5539089 * 2
def baseEnd_5539089 : Nat := 316023893892464891390411

theorem tailTrace_5539089 : CollatzResearch.WordTrace tailWord_5539089 prefixEnd_5539089 316023893892464891390411 := by
  unfold tailWord_5539089
  simp only [CollatzResearch.WordTrace]
  refine ⟨202027173029834028931316321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134684782019889352620877547 202027173029834028931316321)
  ·
    refine ⟨151520379772375521698487241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202027173029834028931316321 151520379772375521698487241)
    ·
      refine ⟨113640284829281641273865431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151520379772375521698487241 113640284829281641273865431)
      ·
        refine ⟨170460427243922461910798147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113640284829281641273865431 170460427243922461910798147)
        ·
          refine ⟨255690640865883692866197221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170460427243922461910798147 255690640865883692866197221)
          ·
            refine ⟨47941995162353192412411979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255690640865883692866197221 47941995162353192412411979)
            ·
              refine ⟨71912992743529788618617969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47941995162353192412411979 71912992743529788618617969)
              ·
                refine ⟨53934744557647341463963477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71912992743529788618617969 53934744557647341463963477)
                ·
                  refine ⟨316023893892464891390411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53934744557647341463963477 316023893892464891390411)
                  ·
                    rfl

theorem cell23_5539089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 9].length) (baseStart_5539089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539089 prefixEnd_5539089 := by exact prefixLift 5539089
  have htrace : WordTrace (prefixWord ++ tailWord_5539089) baseStart_5539089 baseEnd_5539089 := by
    simpa [prefixWord, tailWord_5539089, baseEnd_5539089] using wordTrace_append hprefix tailTrace_5539089
  have hstable : (prefixWord ++ tailWord_5539089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539089).length < 2 ^ (prefixWord ++ tailWord_5539089).sum := by decide
  have hdescent : baseEnd_5539089 < baseStart_5539089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539096 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_5539096 : Nat := 118140960795 + 5539096 * 2 ^ 59
def prefixEnd_5539096 : Nat := 4983230072969 + 3 ^ 40 * 5539096 * 2
def baseEnd_5539096 : Nat := 2844218639396765495126167

theorem tailTrace_5539096 : CollatzResearch.WordTrace tailWord_5539096 prefixEnd_5539096 2844218639396765495126167 := by
  unfold tailWord_5539096
  simp only [CollatzResearch.WordTrace]
  refine ⟨101013714170404334563410571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134684952227205779417880761 101013714170404334563410571)
  ·
    refine ⟨151520571255606501845115857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101013714170404334563410571 151520571255606501845115857)
    ·
      refine ⟨113640428441704876383836893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151520571255606501845115857 113640428441704876383836893)
      ·
        refine ⟨42615160665639328643938835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113640428441704876383836893 42615160665639328643938835)
        ·
          refine ⟨63922740998458992965908253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42615160665639328643938835 63922740998458992965908253)
          ·
            refine ⟨23971027874422122362215595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63922740998458992965908253 23971027874422122362215595)
            ·
              refine ⟨35956541811633183543323393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23971027874422122362215595 35956541811633183543323393)
              ·
                refine ⟨26967406358724887657492545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35956541811633183543323393 26967406358724887657492545)
                ·
                  refine ⟨20225554769043665743119409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26967406358724887657492545 20225554769043665743119409)
                  ·
                    refine ⟨15169166076782749307339557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20225554769043665743119409 15169166076782749307339557)
                    ·
                      refine ⟨2844218639396765495126167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15169166076782749307339557 2844218639396765495126167)
                      ·
                        rfl

theorem cell23_5539096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_5539096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539096 prefixEnd_5539096 := by exact prefixLift 5539096
  have htrace : WordTrace (prefixWord ++ tailWord_5539096) baseStart_5539096 baseEnd_5539096 := by
    simpa [prefixWord, tailWord_5539096, baseEnd_5539096] using wordTrace_append hprefix tailTrace_5539096
  have hstable : (prefixWord ++ tailWord_5539096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539096).length < 2 ^ (prefixWord ++ tailWord_5539096).sum := by decide
  have hdescent : baseEnd_5539096 < baseStart_5539096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539117 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_5539117 : Nat := 118140960795 + 5539117 * 2 ^ 59
def prefixEnd_5539117 : Nat := 4983230072969 + 3 ^ 40 * 5539117 * 2
def baseEnd_5539117 : Nat := 2844229422490509912963571

theorem tailTrace_5539117 : CollatzResearch.WordTrace tailWord_5539117 prefixEnd_5539117 2844229422490509912963571 := by
  unfold tailWord_5539117
  simp only [CollatzResearch.WordTrace]
  refine ⟨202028194273732589713335605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134685462849155059808890403 202028194273732589713335605)
  ·
    refine ⟨18940143213162430285625213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202028194273732589713335605 18940143213162430285625213)
    ·
      refine ⟨7102553704935911357109455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18940143213162430285625213 7102553704935911357109455)
      ·
        refine ⟨10653830557403867035664183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7102553704935911357109455 10653830557403867035664183)
        ·
          refine ⟨15980745836105800553496275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10653830557403867035664183 15980745836105800553496275)
          ·
            refine ⟨23971118754158700830244413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15980745836105800553496275 23971118754158700830244413)
            ·
              refine ⟨8989169532809512811341655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23971118754158700830244413 8989169532809512811341655)
              ·
                refine ⟨13483754299214269217012483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8989169532809512811341655 13483754299214269217012483)
                ·
                  refine ⟨20225631448821403825518725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13483754299214269217012483 20225631448821403825518725)
                  ·
                    refine ⟨3792305896654013217284761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20225631448821403825518725 3792305896654013217284761)
                    ·
                      refine ⟨2844229422490509912963571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792305896654013217284761 2844229422490509912963571)
                      ·
                        rfl

theorem cell23_5539117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_5539117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539117 prefixEnd_5539117 := by exact prefixLift 5539117
  have htrace : WordTrace (prefixWord ++ tailWord_5539117) baseStart_5539117 baseEnd_5539117 := by
    simpa [prefixWord, tailWord_5539117, baseEnd_5539117] using wordTrace_append hprefix tailTrace_5539117
  have hstable : (prefixWord ++ tailWord_5539117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539117).length < 2 ^ (prefixWord ++ tailWord_5539117).sum := by decide
  have hdescent : baseEnd_5539117 < baseStart_5539117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539136 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 2, 5]
def baseStart_5539136 : Nat := 118140960795 + 5539136 * 2 ^ 59
def prefixEnd_5539136 : Nat := 4983230072969 + 3 ^ 40 * 5539136 * 2
def baseEnd_5539136 : Nat := 948079726207648446208661

theorem tailTrace_5539136 : CollatzResearch.WordTrace tailWord_5539136 prefixEnd_5539136 948079726207648446208661 := by
  unfold tailWord_5539136
  simp only [CollatzResearch.WordTrace]
  refine ⟨101014443630331877979138631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134685924840442503972184841 101014443630331877979138631)
  ·
    refine ⟨151521665445497816968707947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101014443630331877979138631 151521665445497816968707947)
    ·
      refine ⟨227282498168246725453061921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151521665445497816968707947 227282498168246725453061921)
      ·
        refine ⟨170461873626185044089796441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227282498168246725453061921 170461873626185044089796441)
        ·
          refine ⟨127846405219638783067347331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170461873626185044089796441 127846405219638783067347331)
          ·
            refine ⟨191769607829458174601020997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127846405219638783067347331 191769607829458174601020997)
            ·
              refine ⟨35956801468023407737691437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191769607829458174601020997 35956801468023407737691437)
              ·
                refine ⟨13483800550508777901634289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35956801468023407737691437 13483800550508777901634289)
                ·
                  refine ⟨10112850412881583426225717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13483800550508777901634289 10112850412881583426225717)
                  ·
                    refine ⟨948079726207648446208661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10112850412881583426225717 948079726207648446208661)
                    ·
                      rfl

theorem cell23_5539136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2, 5].length) (baseStart_5539136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539136 prefixEnd_5539136 := by exact prefixLift 5539136
  have htrace : WordTrace (prefixWord ++ tailWord_5539136) baseStart_5539136 baseEnd_5539136 := by
    simpa [prefixWord, tailWord_5539136, baseEnd_5539136] using wordTrace_append hprefix tailTrace_5539136
  have hstable : (prefixWord ++ tailWord_5539136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539136).length < 2 ^ (prefixWord ++ tailWord_5539136).sum := by decide
  have hdescent : baseEnd_5539136 < baseStart_5539136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539173 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 1, 6, 2]
def baseStart_5539173 : Nat := 118140960795 + 5539173 * 2 ^ 59
def prefixEnd_5539173 : Nat := 4983230072969 + 3 ^ 40 * 5539173 * 2
def baseEnd_5539173 : Nat := 2844258177407161693863313

theorem tailTrace_5539173 : CollatzResearch.WordTrace tailWord_5539173 prefixEnd_5539173 2844258177407161693863313 := by
  unfold tailWord_5539173
  simp only [CollatzResearch.WordTrace]
  refine ⟨202030236761529711277374173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134686824507686474184916115 202030236761529711277374173)
  ·
    refine ⟨75761338785573641729015315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202030236761529711277374173 75761338785573641729015315)
    ·
      refine ⟨113642008178360462593522973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75761338785573641729015315 113642008178360462593522973)
      ·
        refine ⟨42615753066885173472571115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113642008178360462593522973 42615753066885173472571115)
        ·
          refine ⟨63923629600327760208856673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42615753066885173472571115 63923629600327760208856673)
          ·
            refine ⟨47942722200245820156642505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63923629600327760208856673 47942722200245820156642505)
            ·
              refine ⟨35957041650184365117481879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47942722200245820156642505 35957041650184365117481879)
              ·
                refine ⟨53935562475276547676222819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35957041650184365117481879 53935562475276547676222819)
                ·
                  refine ⟨80903343712914821514334229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53935562475276547676222819 80903343712914821514334229)
                  ·
                    refine ⟨3792344236542882258484417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80903343712914821514334229 3792344236542882258484417)
                    ·
                      refine ⟨2844258177407161693863313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792344236542882258484417 2844258177407161693863313)
                      ·
                        rfl

theorem cell23_5539173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_5539173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539173 prefixEnd_5539173 := by exact prefixLift 5539173
  have htrace : WordTrace (prefixWord ++ tailWord_5539173) baseStart_5539173 baseEnd_5539173 := by
    simpa [prefixWord, tailWord_5539173, baseEnd_5539173] using wordTrace_append hprefix tailTrace_5539173
  have hstable : (prefixWord ++ tailWord_5539173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539173).length < 2 ^ (prefixWord ++ tailWord_5539173).sum := by decide
  have hdescent : baseEnd_5539173 < baseStart_5539173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539193 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 2, 2, 3]
def baseStart_5539193 : Nat := 118140960795 + 5539193 * 2 ^ 59
def prefixEnd_5539193 : Nat := 4983230072969 + 3 ^ 40 * 5539193 * 2
def baseEnd_5539193 : Nat := 2844268447020251615613221

theorem tailTrace_5539193 : CollatzResearch.WordTrace tailWord_5539193 prefixEnd_5539193 2844268447020251615613221 := by
  unfold tailWord_5539193
  simp only [CollatzResearch.WordTrace]
  refine ⟨202030966221457254693102233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134687310814304836462068155 202030966221457254693102233)
  ·
    refine ⟨151523224666092941019826675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202030966221457254693102233 151523224666092941019826675)
    ·
      refine ⟨227284836999139411529740013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151523224666092941019826675 227284836999139411529740013)
      ·
        refine ⟨85231813874677279323652505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227284836999139411529740013 85231813874677279323652505)
        ·
          refine ⟨63923860406007959492739379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85231813874677279323652505 63923860406007959492739379)
          ·
            refine ⟨95885790609011939239109069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63923860406007959492739379 95885790609011939239109069)
            ·
              refine ⟨35957171478379477214665901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95885790609011939239109069 35957171478379477214665901)
              ·
                refine ⟨13483939304392303955499713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35957171478379477214665901 13483939304392303955499713)
                ·
                  refine ⟨10112954478294227966624785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13483939304392303955499713 10112954478294227966624785)
                  ·
                    refine ⟨7584715858720670974968589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10112954478294227966624785 7584715858720670974968589)
                    ·
                      refine ⟨2844268447020251615613221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7584715858720670974968589 2844268447020251615613221)
                      ·
                        rfl

theorem cell23_5539193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_5539193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539193 prefixEnd_5539193 := by exact prefixLift 5539193
  have htrace : WordTrace (prefixWord ++ tailWord_5539193) baseStart_5539193 baseEnd_5539193 := by
    simpa [prefixWord, tailWord_5539193, baseEnd_5539193] using wordTrace_append hprefix tailTrace_5539193
  have hstable : (prefixWord ++ tailWord_5539193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539193).length < 2 ^ (prefixWord ++ tailWord_5539193).sum := by decide
  have hdescent : baseEnd_5539193 < baseStart_5539193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539236 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_5539236 : Nat := 118140960795 + 5539236 * 2 ^ 59
def prefixEnd_5539236 : Nat := 4983230072969 + 3 ^ 40 * 5539236 * 2
def baseEnd_5539236 : Nat := 2844290526688394947375523

theorem tailTrace_5539236 : CollatzResearch.WordTrace tailWord_5539236 prefixEnd_5539236 2844290526688394947375523 := by
  unfold tailWord_5539236
  simp only [CollatzResearch.WordTrace]
  refine ⟨101016267280150736518458781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134688356373534315357945041 101016267280150736518458781)
  ·
    refine ⟨37881100230056526194422043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101016267280150736518458781 37881100230056526194422043)
    ·
      refine ⟨56821650345084789291633065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37881100230056526194422043 56821650345084789291633065)
      ·
        refine ⟨42616237758813591968724799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56821650345084789291633065 42616237758813591968724799)
        ·
          refine ⟨63924356638220387953087199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42616237758813591968724799 63924356638220387953087199)
          ·
            refine ⟨95886534957330581929630799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63924356638220387953087199 95886534957330581929630799)
            ·
              refine ⟨143829802435995872894446199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95886534957330581929630799 143829802435995872894446199)
              ·
                refine ⟨215744703653993809341669299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143829802435995872894446199 215744703653993809341669299)
                ·
                  refine ⟨323617055480990714012503949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215744703653993809341669299 323617055480990714012503949)
                  ·
                    refine ⟨121356395805371517754688981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 323617055480990714012503949 121356395805371517754688981)
                    ·
                      refine ⟨2844290526688394947375523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121356395805371517754688981 2844290526688394947375523)
                      ·
                        rfl

theorem cell23_5539236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_5539236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539236 prefixEnd_5539236 := by exact prefixLift 5539236
  have htrace : WordTrace (prefixWord ++ tailWord_5539236) baseStart_5539236 baseEnd_5539236 := by
    simpa [prefixWord, tailWord_5539236, baseEnd_5539236] using wordTrace_append hprefix tailTrace_5539236
  have hstable : (prefixWord ++ tailWord_5539236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539236).length < 2 ^ (prefixWord ++ tailWord_5539236).sum := by decide
  have hdescent : baseEnd_5539236 < baseStart_5539236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539250 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2]
def baseStart_5539250 : Nat := 118140960795 + 5539250 * 2 ^ 59
def prefixEnd_5539250 : Nat := 4983230072969 + 3 ^ 40 * 5539250 * 2
def baseEnd_5539250 : Nat := 2844297715417557892600459

theorem tailTrace_5539250 : CollatzResearch.WordTrace tailWord_5539250 prefixEnd_5539250 2844297715417557892600459 := by
  unfold tailWord_5539250
  simp only [CollatzResearch.WordTrace]
  refine ⟨50508261295562688356981801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134688696788167168951951469 50508261295562688356981801)
  ·
    refine ⟨37881195971672016267736351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50508261295562688356981801 37881195971672016267736351)
    ·
      refine ⟨56821793957508024401604527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37881195971672016267736351 56821793957508024401604527)
      ·
        refine ⟨85232690936262036602406791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56821793957508024401604527 85232690936262036602406791)
        ·
          refine ⟨127849036404393054903610187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85232690936262036602406791 127849036404393054903610187)
          ·
            refine ⟨191773554606589582355415281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127849036404393054903610187 191773554606589582355415281)
            ·
              refine ⟨143830165954942186766561461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191773554606589582355415281 143830165954942186766561461)
              ·
                refine ⟨13484078058275830009365137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143830165954942186766561461 13484078058275830009365137)
                ·
                  refine ⟨10113058543706872507023853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13484078058275830009365137 10113058543706872507023853)
                  ·
                    refine ⟨3792396953890077190133945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10113058543706872507023853 3792396953890077190133945)
                    ·
                      refine ⟨2844297715417557892600459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792396953890077190133945 2844297715417557892600459)
                      ·
                        rfl

theorem cell23_5539250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_5539250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539250 prefixEnd_5539250 := by exact prefixLift 5539250
  have htrace : WordTrace (prefixWord ++ tailWord_5539250) baseStart_5539250 baseEnd_5539250 := by
    simpa [prefixWord, tailWord_5539250, baseEnd_5539250] using wordTrace_append hprefix tailTrace_5539250
  have hstable : (prefixWord ++ tailWord_5539250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539250).length < 2 ^ (prefixWord ++ tailWord_5539250).sum := by decide
  have hdescent : baseEnd_5539250 < baseStart_5539250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539263 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 1, 8, 2]
def baseStart_5539263 : Nat := 118140960795 + 5539263 * 2 ^ 59
def prefixEnd_5539263 : Nat := 4983230072969 + 3 ^ 40 * 5539263 * 2
def baseEnd_5539263 : Nat := 2844304390666066341737899

theorem tailTrace_5539263 : CollatzResearch.WordTrace tailWord_5539263 prefixEnd_5539263 2844304390666066341737899 := by
  unfold tailWord_5539263
  simp only [CollatzResearch.WordTrace]
  refine ⟨202033519331203656648150443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134689012887469104432100295 202033519331203656648150443)
  ·
    refine ⟨303050278996805484972225665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202033519331203656648150443 303050278996805484972225665)
    ·
      refine ⟨227287709247604113729169249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303050278996805484972225665 227287709247604113729169249)
      ·
        refine ⟨170465781935703085296876937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227287709247604113729169249 170465781935703085296876937)
        ·
          refine ⟨127849336451777313972657703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170465781935703085296876937 127849336451777313972657703)
          ·
            refine ⟨191774004677665970958986555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127849336451777313972657703 191774004677665970958986555)
            ·
              refine ⟨287661007016498956438479833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191774004677665970958986555 287661007016498956438479833)
              ·
                refine ⟨215745755262374217328859875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287661007016498956438479833 215745755262374217328859875)
                ·
                  refine ⟨323618632893561325993289813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215745755262374217328859875 323618632893561325993289813)
                  ·
                    refine ⟨3792405854221421788983865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 323618632893561325993289813 3792405854221421788983865)
                    ·
                      refine ⟨2844304390666066341737899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792405854221421788983865 2844304390666066341737899)
                      ·
                        rfl

theorem cell23_5539263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 8, 2].length) (baseStart_5539263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539263 prefixEnd_5539263 := by exact prefixLift 5539263
  have htrace : WordTrace (prefixWord ++ tailWord_5539263) baseStart_5539263 baseEnd_5539263 := by
    simpa [prefixWord, tailWord_5539263, baseEnd_5539263] using wordTrace_append hprefix tailTrace_5539263
  have hstable : (prefixWord ++ tailWord_5539263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539263).length < 2 ^ (prefixWord ++ tailWord_5539263).sum := by decide
  have hdescent : baseEnd_5539263 < baseStart_5539263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539280 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 7, 2, 2]
def baseStart_5539280 : Nat := 118140960795 + 5539280 * 2 ^ 59
def prefixEnd_5539280 : Nat := 4983230072969 + 3 ^ 40 * 5539280 * 2
def baseEnd_5539280 : Nat := 2844313119837192775225321

theorem tailTrace_5539280 : CollatzResearch.WordTrace tailWord_5539280 prefixEnd_5539280 2844313119837192775225321 := by
  unfold tailWord_5539280
  simp only [CollatzResearch.WordTrace]
  refine ⟨101017069686071034275759647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134689426248094712367679529 101017069686071034275759647)
  ·
    refine ⟨151525604529106551413639471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101017069686071034275759647 151525604529106551413639471)
    ·
      refine ⟨227288406793659827120459207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151525604529106551413639471 227288406793659827120459207)
      ·
        refine ⟨340932610190489740680688811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227288406793659827120459207 340932610190489740680688811)
        ·
          refine ⟨511398915285734611021033217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340932610190489740680688811 511398915285734611021033217)
          ·
            refine ⟨383549186464300958265774913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511398915285734611021033217 383549186464300958265774913)
            ·
              refine ⟨287661889848225718699331185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383549186464300958265774913 287661889848225718699331185)
              ·
                refine ⟨215746417386169289024498389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287661889848225718699331185 215746417386169289024498389)
                ·
                  refine ⟨5056556657488342711511681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 215746417386169289024498389 5056556657488342711511681)
                  ·
                    refine ⟨3792417493116257033633761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5056556657488342711511681 3792417493116257033633761)
                    ·
                      refine ⟨2844313119837192775225321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792417493116257033633761 2844313119837192775225321)
                      ·
                        rfl

theorem cell23_5539280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 7, 2, 2].length) (baseStart_5539280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539280 prefixEnd_5539280 := by exact prefixLift 5539280
  have htrace : WordTrace (prefixWord ++ tailWord_5539280) baseStart_5539280 baseEnd_5539280 := by
    simpa [prefixWord, tailWord_5539280, baseEnd_5539280] using wordTrace_append hprefix tailTrace_5539280
  have hstable : (prefixWord ++ tailWord_5539280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539280).length < 2 ^ (prefixWord ++ tailWord_5539280).sum := by decide
  have hdescent : baseEnd_5539280 < baseStart_5539280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539290 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 1, 6]
def baseStart_5539290 : Nat := 118140960795 + 5539290 * 2 ^ 59
def prefixEnd_5539290 : Nat := 4983230072969 + 3 ^ 40 * 5539290 * 2
def baseEnd_5539290 : Nat := 948106084881245912033425

theorem tailTrace_5539290 : CollatzResearch.WordTrace tailWord_5539290 prefixEnd_5539290 948106084881245912033425 := by
  unfold tailWord_5539290
  simp only [CollatzResearch.WordTrace]
  refine ⟨50508626025526460064845831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134689669401403893506255549 50508626025526460064845831)
  ·
    refine ⟨75762939038289690097268747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50508626025526460064845831 75762939038289690097268747)
    ·
      refine ⟨113644408557434535145903121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75762939038289690097268747 113644408557434535145903121)
      ·
        refine ⟨85233306418075901359427341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113644408557434535145903121 85233306418075901359427341)
        ·
          refine ⟨31962489906778463009785253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85233306418075901359427341 31962489906778463009785253)
          ·
            refine ⟨5992966857520961814334735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31962489906778463009785253 5992966857520961814334735)
            ·
              refine ⟨8989450286281442721502103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5992966857520961814334735 8989450286281442721502103)
              ·
                refine ⟨13484175429422164082253155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8989450286281442721502103 13484175429422164082253155)
                ·
                  refine ⟨20226263144133246123379733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13484175429422164082253155 20226263144133246123379733)
                  ·
                    refine ⟨948106084881245912033425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20226263144133246123379733 948106084881245912033425)
                    ·
                      rfl

theorem cell23_5539290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_5539290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539290 prefixEnd_5539290 := by exact prefixLift 5539290
  have htrace : WordTrace (prefixWord ++ tailWord_5539290) baseStart_5539290 baseEnd_5539290 := by
    simpa [prefixWord, tailWord_5539290, baseEnd_5539290] using wordTrace_append hprefix tailTrace_5539290
  have hstable : (prefixWord ++ tailWord_5539290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539290).length < 2 ^ (prefixWord ++ tailWord_5539290).sum := by decide
  have hdescent : baseEnd_5539290 < baseStart_5539290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539297 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 3, 2, 2]
def baseStart_5539297 : Nat := 118140960795 + 5539297 * 2 ^ 59
def prefixEnd_5539297 : Nat := 4983230072969 + 3 ^ 40 * 5539297 * 2
def baseEnd_5539297 : Nat := 2844321849008319208712743

theorem tailTrace_5539297 : CollatzResearch.WordTrace tailWord_5539297 prefixEnd_5539297 2844321849008319208712743 := by
  unfold tailWord_5539297
  simp only [CollatzResearch.WordTrace]
  refine ⟨202034759413080480454888145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134689839608720320303258763 202034759413080480454888145)
  ·
    refine ⟨151526069559810360341166109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202034759413080480454888145 151526069559810360341166109)
    ·
      refine ⟨56822276084928885127937291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151526069559810360341166109 56822276084928885127937291)
      ·
        refine ⟨85233414127393327691905937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56822276084928885127937291 85233414127393327691905937)
        ·
          refine ⟨63925060595544995768929453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85233414127393327691905937 63925060595544995768929453)
          ·
            refine ⟨23971897723329373413348545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63925060595544995768929453 23971897723329373413348545)
            ·
              refine ⟨17978923292497030060011409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23971897723329373413348545 17978923292497030060011409)
              ·
                refine ⟨13484192469372772545008557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17978923292497030060011409 13484192469372772545008557)
                ·
                  refine ⟨5056572176014789704378209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13484192469372772545008557 5056572176014789704378209)
                  ·
                    refine ⟨3792429132011092278283657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5056572176014789704378209 3792429132011092278283657)
                    ·
                      refine ⟨2844321849008319208712743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792429132011092278283657 2844321849008319208712743)
                      ·
                        rfl

theorem cell23_5539297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_5539297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539297 prefixEnd_5539297 := by exact prefixLift 5539297
  have htrace : WordTrace (prefixWord ++ tailWord_5539297) baseStart_5539297 baseEnd_5539297 := by
    simpa [prefixWord, tailWord_5539297, baseEnd_5539297] using wordTrace_append hprefix tailTrace_5539297
  have hstable : (prefixWord ++ tailWord_5539297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539297).length < 2 ^ (prefixWord ++ tailWord_5539297).sum := by decide
  have hdescent : baseEnd_5539297 < baseStart_5539297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539303 : List Nat := [1, 1, 5, 2, 1, 3, 1, 9]
def baseStart_5539303 : Nat := 118140960795 + 5539303 * 2 ^ 59
def prefixEnd_5539303 : Nat := 4983230072969 + 3 ^ 40 * 5539303 * 2
def baseEnd_5539303 : Nat := 105345367773786895749545

theorem tailTrace_5539303 : CollatzResearch.WordTrace tailWord_5539303 prefixEnd_5539303 105345367773786895749545 := by
  unfold tailWord_5539303
  simp only [CollatzResearch.WordTrace]
  refine ⟨202034978251058743479606563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134689985500705828986404375 202034978251058743479606563)
  ·
    refine ⟨303052467376588115219409845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202034978251058743479606563 303052467376588115219409845)
    ·
      refine ⟨28411168816555135801819673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 303052467376588115219409845 28411168816555135801819673)
      ·
        refine ⟨21308376612416351851364755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28411168816555135801819673 21308376612416351851364755)
        ·
          refine ⟨31962564918624527777047133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21308376612416351851364755 31962564918624527777047133)
          ·
            refine ⟨11985961844484197916392675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31962564918624527777047133 11985961844484197916392675)
            ·
              refine ⟨17978942766726296874589013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11985961844484197916392675 17978942766726296874589013)
              ·
                refine ⟨105345367773786895749545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17978942766726296874589013 105345367773786895749545)
                ·
                  rfl

theorem cell23_5539303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 9].length) (baseStart_5539303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539303 prefixEnd_5539303 := by exact prefixLift 5539303
  have htrace : WordTrace (prefixWord ++ tailWord_5539303) baseStart_5539303 baseEnd_5539303 := by
    simpa [prefixWord, tailWord_5539303, baseEnd_5539303] using wordTrace_append hprefix tailTrace_5539303
  have hstable : (prefixWord ++ tailWord_5539303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539303).length < 2 ^ (prefixWord ++ tailWord_5539303).sum := by decide
  have hdescent : baseEnd_5539303 < baseStart_5539303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539317 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_5539317 : Nat := 118140960795 + 5539317 * 2 ^ 59
def prefixEnd_5539317 : Nat := 4983230072969 + 3 ^ 40 * 5539317 * 2
def baseEnd_5539317 : Nat := 2844332118621409130462651

theorem tailTrace_5539317 : CollatzResearch.WordTrace tailWord_5539317 prefixEnd_5539317 2844332118621409130462651 := by
  unfold tailWord_5539317
  simp only [CollatzResearch.WordTrace]
  refine ⟨202035488873008023870616205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134690325915338682580410803 202035488873008023870616205)
  ·
    refine ⟨75763308327378008951481077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202035488873008023870616205 75763308327378008951481077)
    ·
      refine ⟨7102810155691688339201351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75763308327378008951481077 7102810155691688339201351)
      ·
        refine ⟨10654215233537532508802027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7102810155691688339201351 10654215233537532508802027)
        ·
          refine ⟨15981322850306298763203041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10654215233537532508802027 15981322850306298763203041)
          ·
            refine ⟨11985992137729724072402281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15981322850306298763203041 11985992137729724072402281)
            ·
              refine ⟨8989494103297293054301711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11985992137729724072402281 8989494103297293054301711)
              ·
                refine ⟨13484241154945939581452567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8989494103297293054301711 13484241154945939581452567)
                ·
                  refine ⟨20226361732418909372178851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13484241154945939581452567 20226361732418909372178851)
                  ·
                    refine ⟨30339542598628364058268277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20226361732418909372178851 30339542598628364058268277)
                    ·
                      refine ⟨2844332118621409130462651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30339542598628364058268277 2844332118621409130462651)
                      ·
                        rfl

theorem cell23_5539317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_5539317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539317 prefixEnd_5539317 := by exact prefixLift 5539317
  have htrace : WordTrace (prefixWord ++ tailWord_5539317) baseStart_5539317 baseEnd_5539317 := by
    simpa [prefixWord, tailWord_5539317, baseEnd_5539317] using wordTrace_append hprefix tailTrace_5539317
  have hstable : (prefixWord ++ tailWord_5539317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539317).length < 2 ^ (prefixWord ++ tailWord_5539317).sum := by decide
  have hdescent : baseEnd_5539317 < baseStart_5539317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539341 : List Nat := [1, 7, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_5539341 : Nat := 118140960795 + 5539341 * 2 ^ 59
def prefixEnd_5539341 : Nat := 4983230072969 + 3 ^ 40 * 5539341 * 2
def baseEnd_5539341 : Nat := 948114814052372345520847

theorem tailTrace_5539341 : CollatzResearch.WordTrace tailWord_5539341 prefixEnd_5539341 948114814052372345520847 := by
  unfold tailWord_5539341
  simp only [CollatzResearch.WordTrace]
  refine ⟨202036364224921075969489877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134690909483280717312993251 202036364224921075969489877)
  ·
    refine ⟨4735227286521587718034919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 202036364224921075969489877 4735227286521587718034919)
    ·
      refine ⟨7102840929782381577052379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4735227286521587718034919 7102840929782381577052379)
      ·
        refine ⟨10654261394673572365578569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7102840929782381577052379 10654261394673572365578569)
        ·
          refine ⟨7990696046005179274183927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10654261394673572365578569 7990696046005179274183927)
          ·
            refine ⟨11986044069007768911275891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7990696046005179274183927 11986044069007768911275891)
            ·
              refine ⟨17979066103511653366913837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11986044069007768911275891 17979066103511653366913837)
              ·
                refine ⟨6742149788816870012592689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17979066103511653366913837 6742149788816870012592689)
                ·
                  refine ⟨5056612341612652509444517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6742149788816870012592689 5056612341612652509444517)
                  ·
                    refine ⟨948114814052372345520847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5056612341612652509444517 948114814052372345520847)
                    ·
                      rfl

theorem cell23_5539341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_5539341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539341 prefixEnd_5539341 := by exact prefixLift 5539341
  have htrace : WordTrace (prefixWord ++ tailWord_5539341) baseStart_5539341 baseEnd_5539341 := by
    simpa [prefixWord, tailWord_5539341, baseEnd_5539341] using wordTrace_append hprefix tailTrace_5539341
  have hstable : (prefixWord ++ tailWord_5539341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539341).length < 2 ^ (prefixWord ++ tailWord_5539341).sum := by decide
  have hdescent : baseEnd_5539341 < baseStart_5539341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539347 : List Nat := [1, 1, 1, 2, 1, 7, 1, 3, 2, 1, 3]
def baseStart_5539347 : Nat := 118140960795 + 5539347 * 2 ^ 59
def prefixEnd_5539347 : Nat := 4983230072969 + 3 ^ 40 * 5539347 * 2
def baseEnd_5539347 : Nat := 2844347523041044013087513

theorem tailTrace_5539347 : CollatzResearch.WordTrace tailWord_5539347 prefixEnd_5539347 2844347523041044013087513 := by
  unfold tailWord_5539347
  simp only [CollatzResearch.WordTrace]
  refine ⟨202036583062899338994208295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134691055375266225996138863 202036583062899338994208295)
  ·
    refine ⟨303054874594349008491312443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202036583062899338994208295 303054874594349008491312443)
    ·
      refine ⟨454582311891523512736968665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303054874594349008491312443 454582311891523512736968665)
      ·
        refine ⟨340936733918642634552726499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454582311891523512736968665 340936733918642634552726499)
        ·
          refine ⟨511405100877963951829089749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340936733918642634552726499 511405100877963951829089749)
          ·
            refine ⟨11986057051827280120994291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 511405100877963951829089749 11986057051827280120994291)
            ·
              refine ⟨17979085577740920181491437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11986057051827280120994291 17979085577740920181491437)
              ·
                refine ⟨6742157091652845068059289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17979085577740920181491437 6742157091652845068059289)
                ·
                  refine ⟨5056617818739633801044467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6742157091652845068059289 5056617818739633801044467)
                  ·
                    refine ⟨7584926728109450701566701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5056617818739633801044467 7584926728109450701566701)
                    ·
                      refine ⟨2844347523041044013087513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7584926728109450701566701 2844347523041044013087513)
                      ·
                        rfl

theorem cell23_5539347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 1, 3].length) (baseStart_5539347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539347 prefixEnd_5539347 := by exact prefixLift 5539347
  have htrace : WordTrace (prefixWord ++ tailWord_5539347) baseStart_5539347 baseEnd_5539347 := by
    simpa [prefixWord, tailWord_5539347, baseEnd_5539347] using wordTrace_append hprefix tailTrace_5539347
  have hstable : (prefixWord ++ tailWord_5539347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539347).length < 2 ^ (prefixWord ++ tailWord_5539347).sum := by decide
  have hdescent : baseEnd_5539347 < baseStart_5539347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539357 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_5539357 : Nat := 118140960795 + 5539357 * 2 ^ 59
def prefixEnd_5539357 : Nat := 4983230072969 + 3 ^ 40 * 5539357 * 2
def baseEnd_5539357 : Nat := 2844352657847588973962467

theorem tailTrace_5539357 : CollatzResearch.WordTrace tailWord_5539357 prefixEnd_5539357 2844352657847588973962467 := by
  unfold tailWord_5539357
  simp only [CollatzResearch.WordTrace]
  refine ⟨202036947792863110702072325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134691298528575407134714883 202036947792863110702072325)
  ·
    refine ⟨37881927711161833256638561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202036947792863110702072325 37881927711161833256638561)
    ·
      refine ⟨28411445783371374942478921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37881927711161833256638561 28411445783371374942478921)
      ·
        refine ⟨21308584337528531206859191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28411445783371374942478921 21308584337528531206859191)
        ·
          refine ⟨31962876506292796810288787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21308584337528531206859191 31962876506292796810288787)
          ·
            refine ⟨47944314759439195215433181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31962876506292796810288787 47944314759439195215433181)
            ·
              refine ⟨17979118034789698205787443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47944314759439195215433181 17979118034789698205787443)
              ·
                refine ⟨26968677052184547308681165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17979118034789698205787443 26968677052184547308681165)
                ·
                  refine ⟨10113253894569205240755437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26968677052184547308681165 10113253894569205240755437)
                  ·
                    refine ⟨3792470210463451965283289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10113253894569205240755437 3792470210463451965283289)
                    ·
                      refine ⟨2844352657847588973962467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792470210463451965283289 2844352657847588973962467)
                      ·
                        rfl

theorem cell23_5539357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_5539357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539357 prefixEnd_5539357 := by exact prefixLift 5539357
  have htrace : WordTrace (prefixWord ++ tailWord_5539357) baseStart_5539357 baseEnd_5539357 := by
    simpa [prefixWord, tailWord_5539357, baseEnd_5539357] using wordTrace_append hprefix tailTrace_5539357
  have hstable : (prefixWord ++ tailWord_5539357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539357).length < 2 ^ (prefixWord ++ tailWord_5539357).sum := by decide
  have hdescent : baseEnd_5539357 < baseStart_5539357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539382 : List Nat := [5, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_5539382 : Nat := 118140960795 + 5539382 * 2 ^ 59
def prefixEnd_5539382 : Nat := 4983230072969 + 3 ^ 40 * 5539382 * 2
def baseEnd_5539382 : Nat := 2844365494863951376149853

theorem tailTrace_5539382 : CollatzResearch.WordTrace tailWord_5539382 prefixEnd_5539382 2844365494863951376149853 := by
  unfold tailWord_5539382
  simp only [CollatzResearch.WordTrace]
  refine ⟨12627366226110783748233275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134691906411848359981154933 12627366226110783748233275)
  ·
    refine ⟨18941049339166175622349913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12627366226110783748233275 18941049339166175622349913)
    ·
      refine ⟨14205787004374631716762435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18941049339166175622349913 14205787004374631716762435)
      ·
        refine ⟨21308680506561947575143653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14205787004374631716762435 21308680506561947575143653)
        ·
          refine ⟨3995377594980365170339435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21308680506561947575143653 3995377594980365170339435)
          ·
            refine ⟨5993066392470547755509153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3995377594980365170339435 5993066392470547755509153)
            ·
              refine ⟨4494799794352910816631865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5993066392470547755509153 4494799794352910816631865)
              ·
                refine ⟨3371099845764683112473899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4494799794352910816631865 3371099845764683112473899)
                ·
                  refine ⟨5056649768647024668710849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371099845764683112473899 5056649768647024668710849)
                  ·
                    refine ⟨3792487326485268501533137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5056649768647024668710849 3792487326485268501533137)
                    ·
                      refine ⟨2844365494863951376149853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792487326485268501533137 2844365494863951376149853)
                      ·
                        rfl

theorem cell23_5539382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_5539382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539382 prefixEnd_5539382 := by exact prefixLift 5539382
  have htrace : WordTrace (prefixWord ++ tailWord_5539382) baseStart_5539382 baseEnd_5539382 := by
    simpa [prefixWord, tailWord_5539382, baseEnd_5539382] using wordTrace_append hprefix tailTrace_5539382
  have hstable : (prefixWord ++ tailWord_5539382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539382).length < 2 ^ (prefixWord ++ tailWord_5539382).sum := by decide
  have hdescent : baseEnd_5539382 < baseStart_5539382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
