import V185TrunkScan23Chunk0999

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5921744 : List Nat := [2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 3]
def baseStart_5921744 : Nat := 118140960795 + 5921744 * 2 ^ 59
def prefixEnd_5921744 : Nat := 4983230072969 + 3 ^ 40 * 5921744 * 2
def baseEnd_5921744 : Nat := 3040700984878384383066401

theorem tailTrace_5921744 : CollatzResearch.WordTrace tailWord_5921744 prefixEnd_5921744 3040700984878384383066401 := by
  unfold tailWord_5921744
  simp only [CollatzResearch.WordTrace]
  refine ⟨107991873729270158101178143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143989164972360210801570857 107991873729270158101178143)
  ·
    refine ⟨161987810593905237151767215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107991873729270158101178143 161987810593905237151767215)
    ·
      refine ⟨242981715890857855727650823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161987810593905237151767215 242981715890857855727650823)
      ·
        refine ⟨364472573836286783591476235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242981715890857855727650823 364472573836286783591476235)
        ·
          refine ⟨546708860754430175387214353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364472573836286783591476235 546708860754430175387214353)
          ·
            refine ⟨410031645565822631540410765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546708860754430175387214353 410031645565822631540410765)
            ·
              refine ⟨153761867087183486827654037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 410031645565822631540410765 153761867087183486827654037)
              ·
                refine ⟨7207587519711725945046283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153761867087183486827654037 7207587519711725945046283)
                ·
                  refine ⟨10811381279567588917569425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7207587519711725945046283 10811381279567588917569425)
                  ·
                    refine ⟨8108535959675691688177069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10811381279567588917569425 8108535959675691688177069)
                    ·
                      refine ⟨3040700984878384383066401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8108535959675691688177069 3040700984878384383066401)
                      ·
                        rfl

theorem cell23_5921744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 3].length) (baseStart_5921744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921744 prefixEnd_5921744 := by exact prefixLift 5921744
  have htrace : WordTrace (prefixWord ++ tailWord_5921744) baseStart_5921744 baseEnd_5921744 := by
    simpa [prefixWord, tailWord_5921744, baseEnd_5921744] using wordTrace_append hprefix tailTrace_5921744
  have hstable : (prefixWord ++ tailWord_5921744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921744).length < 2 ^ (prefixWord ++ tailWord_5921744).sum := by decide
  have hdescent : baseEnd_5921744 < baseStart_5921744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921754 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_5921754 : Nat := 118140960795 + 5921754 * 2 ^ 59
def prefixEnd_5921754 : Nat := 4983230072969 + 3 ^ 40 * 5921754 * 2
def baseEnd_5921754 : Nat := 3040706119684929343941355

theorem tailTrace_5921754 : CollatzResearch.WordTrace tailWord_5921754 prefixEnd_5921754 3040706119684929343941355 := by
  unfold tailWord_5921754
  simp only [CollatzResearch.WordTrace]
  refine ⟨53996028047126021977555079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143989408125669391940146877 53996028047126021977555079)
  ·
    refine ⟨80994042070689032966332619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53996028047126021977555079 80994042070689032966332619)
    ·
      refine ⟨121491063106033549449498929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80994042070689032966332619 121491063106033549449498929)
      ·
        refine ⟨91118297329525162087124197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121491063106033549449498929 91118297329525162087124197)
        ·
          refine ⟨17084680749285967891335787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91118297329525162087124197 17084680749285967891335787)
          ·
            refine ⟨25627021123928951837003681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17084680749285967891335787 25627021123928951837003681)
            ·
              refine ⟨19220265842946713877752761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25627021123928951837003681 19220265842946713877752761)
              ·
                refine ⟨14415199382210035408314571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19220265842946713877752761 14415199382210035408314571)
                ·
                  refine ⟨21622799073315053112471857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14415199382210035408314571 21622799073315053112471857)
                  ·
                    refine ⟨16217099304986289834353893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21622799073315053112471857 16217099304986289834353893)
                    ·
                      refine ⟨3040706119684929343941355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16217099304986289834353893 3040706119684929343941355)
                      ·
                        rfl

theorem cell23_5921754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_5921754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921754 prefixEnd_5921754 := by exact prefixLift 5921754
  have htrace : WordTrace (prefixWord ++ tailWord_5921754) baseStart_5921754 baseEnd_5921754 := by
    simpa [prefixWord, tailWord_5921754, baseEnd_5921754] using wordTrace_append hprefix tailTrace_5921754
  have hstable : (prefixWord ++ tailWord_5921754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921754).length < 2 ^ (prefixWord ++ tailWord_5921754).sum := by decide
  have hdescent : baseEnd_5921754 < baseStart_5921754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921817 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 5]
def baseStart_5921817 : Nat := 118140960795 + 5921817 * 2 ^ 59
def prefixEnd_5921817 : Nat := 4983230072969 + 3 ^ 40 * 5921817 * 2
def baseEnd_5921817 : Nat := 3040738468966162597453565

theorem tailTrace_5921817 : CollatzResearch.WordTrace tailWord_5921817 prefixEnd_5921817 3040738468966162597453565 := by
  unfold tailWord_5921817
  simp only [CollatzResearch.WordTrace]
  refine ⟨215986409987275849669763705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143990939991517233113175803 215986409987275849669763705)
  ·
    refine ⟨161989807490456887252322779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215986409987275849669763705 161989807490456887252322779)
    ·
      refine ⟨242984711235685330878484169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161989807490456887252322779 242984711235685330878484169)
      ·
        refine ⟨182238533426763998158863127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242984711235685330878484169 182238533426763998158863127)
        ·
          refine ⟨273357800140145997238294691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182238533426763998158863127 273357800140145997238294691)
          ·
            refine ⟨410036700210218995857442037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273357800140145997238294691 410036700210218995857442037)
            ·
              refine ⟨38440940644708030861635191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 410036700210218995857442037 38440940644708030861635191)
              ·
                refine ⟨57661410967062046292452787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38440940644708030861635191 57661410967062046292452787)
                ·
                  refine ⟨86492116450593069438679181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57661410967062046292452787 86492116450593069438679181)
                  ·
                    refine ⟨32434543668972401039504693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86492116450593069438679181 32434543668972401039504693)
                    ·
                      refine ⟨3040738468966162597453565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32434543668972401039504693 3040738468966162597453565)
                      ·
                        rfl

theorem cell23_5921817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_5921817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921817 prefixEnd_5921817 := by exact prefixLift 5921817
  have htrace : WordTrace (prefixWord ++ tailWord_5921817) baseStart_5921817 baseEnd_5921817 := by
    simpa [prefixWord, tailWord_5921817, baseEnd_5921817] using wordTrace_append hprefix tailTrace_5921817
  have hstable : (prefixWord ++ tailWord_5921817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921817).length < 2 ^ (prefixWord ++ tailWord_5921817).sum := by decide
  have hdescent : baseEnd_5921817 < baseStart_5921817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921904 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 4]
def baseStart_5921904 : Nat := 118140960795 + 5921904 * 2 ^ 59
def prefixEnd_5921904 : Nat := 4983230072969 + 3 ^ 40 * 5921904 * 2
def baseEnd_5921904 : Nat := 3040783141783103757065665

theorem tailTrace_5921904 : CollatzResearch.WordTrace tailWord_5921904 prefixEnd_5921904 3040783141783103757065665 := by
  unfold tailWord_5921904
  simp only [CollatzResearch.WordTrace]
  refine ⟨107994791568980331764090383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143993055425307109018787177 107994791568980331764090383)
  ·
    refine ⟨161992187353470497646135575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107994791568980331764090383 161992187353470497646135575)
    ·
      refine ⟨242988281030205746469203363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161992187353470497646135575 242988281030205746469203363)
      ·
        refine ⟨364482421545308619703805045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242988281030205746469203363 364482421545308619703805045)
        ·
          refine ⟨34170227019872683097231723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 364482421545308619703805045 34170227019872683097231723)
          ·
            refine ⟨51255340529809024645847585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34170227019872683097231723 51255340529809024645847585)
            ·
              refine ⟨38441505397356768484385689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51255340529809024645847585 38441505397356768484385689)
              ·
                refine ⟨28831129048017576363289267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38441505397356768484385689 28831129048017576363289267)
                ·
                  refine ⟨43246693572026364544933901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28831129048017576363289267 43246693572026364544933901)
                  ·
                    refine ⟨16217510089509886704350213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43246693572026364544933901 16217510089509886704350213)
                    ·
                      refine ⟨3040783141783103757065665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16217510089509886704350213 3040783141783103757065665)
                      ·
                        rfl

theorem cell23_5921904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_5921904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921904 prefixEnd_5921904 := by exact prefixLift 5921904
  have htrace : WordTrace (prefixWord ++ tailWord_5921904) baseStart_5921904 baseEnd_5921904 := by
    simpa [prefixWord, tailWord_5921904, baseEnd_5921904] using wordTrace_append hprefix tailTrace_5921904
  have hstable : (prefixWord ++ tailWord_5921904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921904).length < 2 ^ (prefixWord ++ tailWord_5921904).sum := by decide
  have hdescent : baseEnd_5921904 < baseStart_5921904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921921 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_5921921 : Nat := 118140960795 + 5921921 * 2 ^ 59
def prefixEnd_5921921 : Nat := 4983230072969 + 3 ^ 40 * 5921921 * 2
def baseEnd_5921921 : Nat := 3040791870954230190553087

theorem tailTrace_5921921 : CollatzResearch.WordTrace tailWord_5921921 prefixEnd_5921921 3040791870954230190553087 := by
  unfold tailWord_5921921
  simp only [CollatzResearch.WordTrace]
  refine ⟨215990203178899075431549617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143993468785932716954366411 215990203178899075431549617)
  ·
    refine ⟨161992652384174306573662213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215990203178899075431549617 161992652384174306573662213)
    ·
      refine ⟨30373622322032682482561665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161992652384174306573662213 30373622322032682482561665)
      ·
        refine ⟨22780216741524511861921249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30373622322032682482561665 22780216741524511861921249)
        ·
          refine ⟨17085162556143383896440937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22780216741524511861921249 17085162556143383896440937)
          ·
            refine ⟨12813871917107537922330703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17085162556143383896440937 12813871917107537922330703)
            ·
              refine ⟨19220807875661306883496055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12813871917107537922330703 19220807875661306883496055)
              ·
                refine ⟨28831211813491960325244083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19220807875661306883496055 28831211813491960325244083)
                ·
                  refine ⟨43246817720237940487866125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28831211813491960325244083 43246817720237940487866125)
                  ·
                    refine ⟨16217556645089227682949797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43246817720237940487866125 16217556645089227682949797)
                    ·
                      refine ⟨3040791870954230190553087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16217556645089227682949797 3040791870954230190553087)
                      ·
                        rfl

theorem cell23_5921921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_5921921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921921 prefixEnd_5921921 := by exact prefixLift 5921921
  have htrace : WordTrace (prefixWord ++ tailWord_5921921) baseStart_5921921 baseEnd_5921921 := by
    simpa [prefixWord, tailWord_5921921, baseEnd_5921921] using wordTrace_append hprefix tailTrace_5921921
  have hstable : (prefixWord ++ tailWord_5921921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921921).length < 2 ^ (prefixWord ++ tailWord_5921921).sum := by decide
  have hdescent : baseEnd_5921921 < baseStart_5921921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921938 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_5921938 : Nat := 118140960795 + 5921938 * 2 ^ 59
def prefixEnd_5921938 : Nat := 4983230072969 + 3 ^ 40 * 5921938 * 2
def baseEnd_5921938 : Nat := 3040800600125356624040509

theorem tailTrace_5921938 : CollatzResearch.WordTrace tailWord_5921938 prefixEnd_5921938 3040800600125356624040509 := by
  unfold tailWord_5921938
  simp only [CollatzResearch.WordTrace]
  refine ⟨53997705804959371833729617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143993882146558324889945645 53997705804959371833729617)
  ·
    refine ⟨40498279353719528875297213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53997705804959371833729617 40498279353719528875297213)
    ·
      refine ⟨15186854757644823328236455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40498279353719528875297213 15186854757644823328236455)
      ·
        refine ⟨22780282136467234992354683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15186854757644823328236455 22780282136467234992354683)
        ·
          refine ⟨34170423204700852488532025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22780282136467234992354683 34170423204700852488532025)
          ·
            refine ⟨25627817403525639366399019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34170423204700852488532025 25627817403525639366399019)
            ·
              refine ⟨38441726105288459049598529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25627817403525639366399019 38441726105288459049598529)
              ·
                refine ⟨28831294578966344287198897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38441726105288459049598529 28831294578966344287198897)
                ·
                  refine ⟨21623470934224758215399173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28831294578966344287198897 21623470934224758215399173)
                  ·
                    refine ⟨4054400800167142165387345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21623470934224758215399173 4054400800167142165387345)
                    ·
                      refine ⟨3040800600125356624040509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4054400800167142165387345 3040800600125356624040509)
                      ·
                        rfl

theorem cell23_5921938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_5921938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921938 prefixEnd_5921938 := by exact prefixLift 5921938
  have htrace : WordTrace (prefixWord ++ tailWord_5921938) baseStart_5921938 baseEnd_5921938 := by
    simpa [prefixWord, tailWord_5921938, baseEnd_5921938] using wordTrace_append hprefix tailTrace_5921938
  have hstable : (prefixWord ++ tailWord_5921938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921938).length < 2 ^ (prefixWord ++ tailWord_5921938).sum := by decide
  have hdescent : baseEnd_5921938 < baseStart_5921938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921948 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 3, 4]
def baseStart_5921948 : Nat := 118140960795 + 5921948 * 2 ^ 59
def prefixEnd_5921948 : Nat := 4983230072969 + 3 ^ 40 * 5921948 * 2
def baseEnd_5921948 : Nat := 1013601911643967194971821

theorem tailTrace_5921948 : CollatzResearch.WordTrace tailWord_5921948 prefixEnd_5921948 1013601911643967194971821 := by
  unfold tailWord_5921948
  simp only [CollatzResearch.WordTrace]
  refine ⟨107995593974900629521391249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143994125299867506028521665 107995593974900629521391249)
  ·
    refine ⟨80996695481175472141043437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107995593974900629521391249 80996695481175472141043437)
    ·
      refine ⟨30373760805440802052891289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80996695481175472141043437 30373760805440802052891289)
      ·
        refine ⟨22780320604080601539668467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30373760805440802052891289 22780320604080601539668467)
        ·
          refine ⟨34170480906120902309502701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22780320604080601539668467 34170480906120902309502701)
          ·
            refine ⟨12813930339795338366063513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34170480906120902309502701 12813930339795338366063513)
            ·
              refine ⟨9610447754846503774547635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12813930339795338366063513 9610447754846503774547635)
              ·
                refine ⟨14415671632269755661821453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9610447754846503774547635 14415671632269755661821453)
                ·
                  refine ⟨5405876862101158373183045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14415671632269755661821453 5405876862101158373183045)
                  ·
                    refine ⟨1013601911643967194971821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5405876862101158373183045 1013601911643967194971821)
                    ·
                      rfl

theorem cell23_5921948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_5921948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921948 prefixEnd_5921948 := by exact prefixLift 5921948
  have htrace : WordTrace (prefixWord ++ tailWord_5921948) baseStart_5921948 baseEnd_5921948 := by
    simpa [prefixWord, tailWord_5921948, baseEnd_5921948] using wordTrace_append hprefix tailTrace_5921948
  have hstable : (prefixWord ++ tailWord_5921948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921948).length < 2 ^ (prefixWord ++ tailWord_5921948).sum := by decide
  have hdescent : baseEnd_5921948 < baseStart_5921948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921982 : List Nat := [4, 2, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_5921982 : Nat := 118140960795 + 5921982 * 2 ^ 59
def prefixEnd_5921982 : Nat := 4983230072969 + 3 ^ 40 * 5921982 * 2
def baseEnd_5921982 : Nat := 1013607731091384817296769

theorem tailTrace_5921982 : CollatzResearch.WordTrace tailWord_5921982 prefixEnd_5921982 1013607731091384817296769 := by
  unfold tailWord_5921982
  simp only [CollatzResearch.WordTrace]
  refine ⟨26999053503959760356190025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143994952021118721899680133 26999053503959760356190025)
  ·
    refine ⟨20249290127969820267142519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26999053503959760356190025 20249290127969820267142519)
    ·
      refine ⟨30373935191954730400713779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20249290127969820267142519 30373935191954730400713779)
      ·
        refine ⟨45560902787932095601070669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30373935191954730400713779 45560902787932095601070669)
        ·
          refine ⟨17085338545474535850401501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45560902787932095601070669 17085338545474535850401501)
          ·
            refine ⟨6407001954552950943900563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17085338545474535850401501 6407001954552950943900563)
            ·
              refine ⟨9610502931829426415850845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6407001954552950943900563 9610502931829426415850845)
              ·
                refine ⟨3603938599436034905944067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9610502931829426415850845 3603938599436034905944067)
                ·
                  refine ⟨5405907899154052358916101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603938599436034905944067 5405907899154052358916101)
                  ·
                    refine ⟨1013607731091384817296769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5405907899154052358916101 1013607731091384817296769)
                    ·
                      rfl

theorem cell23_5921982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_5921982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921982 prefixEnd_5921982 := by exact prefixLift 5921982
  have htrace : WordTrace (prefixWord ++ tailWord_5921982) baseStart_5921982 baseEnd_5921982 := by
    simpa [prefixWord, tailWord_5921982, baseEnd_5921982] using wordTrace_append hprefix tailTrace_5921982
  have hstable : (prefixWord ++ tailWord_5921982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921982).length < 2 ^ (prefixWord ++ tailWord_5921982).sum := by decide
  have hdescent : baseEnd_5921982 < baseStart_5921982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922005 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_5922005 : Nat := 118140960795 + 5922005 * 2 ^ 59
def prefixEnd_5922005 : Nat := 4983230072969 + 3 ^ 40 * 5922005 * 2
def baseEnd_5922005 : Nat := 3040835003329207861902701

theorem tailTrace_5922005 : CollatzResearch.WordTrace tailWord_5922005 prefixEnd_5922005 3040835003329207861902701 := by
  unfold tailWord_5922005
  simp only [CollatzResearch.WordTrace]
  refine ⟨215993266910594757777607469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143995511273729838518404979 215993266910594757777607469)
  ·
    refine ⟨80997475091473034166602801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215993266910594757777607469 80997475091473034166602801)
    ·
      refine ⟨60748106318604775624952101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80997475091473034166602801 60748106318604775624952101)
      ·
        refine ⟨11390269934738395429678519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60748106318604775624952101 11390269934738395429678519)
        ·
          refine ⟨17085404902107593144517779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11390269934738395429678519 17085404902107593144517779)
          ·
            refine ⟨25628107353161389716776669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17085404902107593144517779 25628107353161389716776669)
            ·
              refine ⟨9610540257435521143791251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25628107353161389716776669 9610540257435521143791251)
              ·
                refine ⟨14415810386153281715686877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9610540257435521143791251 14415810386153281715686877)
                ·
                  refine ⟨5405928894807480643382579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14415810386153281715686877 5405928894807480643382579)
                  ·
                    refine ⟨8108893342211220965073869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5405928894807480643382579 8108893342211220965073869)
                    ·
                      refine ⟨3040835003329207861902701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8108893342211220965073869 3040835003329207861902701)
                      ·
                        rfl

theorem cell23_5922005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_5922005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922005 prefixEnd_5922005 := by exact prefixLift 5922005
  have htrace : WordTrace (prefixWord ++ tailWord_5922005) baseStart_5922005 baseEnd_5922005 := by
    simpa [prefixWord, tailWord_5922005, baseEnd_5922005] using wordTrace_append hprefix tailTrace_5922005
  have hstable : (prefixWord ++ tailWord_5922005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922005).length < 2 ^ (prefixWord ++ tailWord_5922005).sum := by decide
  have hdescent : baseEnd_5922005 < baseStart_5922005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922028 : List Nat := [2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 4]
def baseStart_5922028 : Nat := 118140960795 + 5922028 * 2 ^ 59
def prefixEnd_5922028 : Nat := 4983230072969 + 3 ^ 40 * 5922028 * 2
def baseEnd_5922028 : Nat := 3040846813384261271915095

theorem tailTrace_5922028 : CollatzResearch.WordTrace tailWord_5922028 prefixEnd_5922028 3040846813384261271915095 := by
  unfold tailWord_5922028
  simp only [CollatzResearch.WordTrace]
  refine ⟨107997052894755716352847369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143996070526340955137129825 107997052894755716352847369)
  ·
    refine ⟨80997789671066787264635527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107997052894755716352847369 80997789671066787264635527)
    ·
      refine ⟨121496684506600180896953291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80997789671066787264635527 121496684506600180896953291)
      ·
        refine ⟨182245026759900271345429937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121496684506600180896953291 182245026759900271345429937)
        ·
          refine ⟨136683770069925203509072453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182245026759900271345429937 136683770069925203509072453)
          ·
            refine ⟨25628206888110975657951085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136683770069925203509072453 25628206888110975657951085)
            ·
              refine ⟨9610577583041615871731657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25628206888110975657951085 9610577583041615871731657)
              ·
                refine ⟨7207933187281211903798743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9610577583041615871731657 7207933187281211903798743)
                ·
                  refine ⟨10811899780921817855698115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7207933187281211903798743 10811899780921817855698115)
                  ·
                    refine ⟨16217849671382726783547173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10811899780921817855698115 16217849671382726783547173)
                    ·
                      refine ⟨3040846813384261271915095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16217849671382726783547173 3040846813384261271915095)
                      ·
                        rfl

theorem cell23_5922028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_5922028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922028 prefixEnd_5922028 := by exact prefixLift 5922028
  have htrace : WordTrace (prefixWord ++ tailWord_5922028) baseStart_5922028 baseEnd_5922028 := by
    simpa [prefixWord, tailWord_5922028, baseEnd_5922028] using wordTrace_append hprefix tailTrace_5922028
  have hstable : (prefixWord ++ tailWord_5922028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922028).length < 2 ^ (prefixWord ++ tailWord_5922028).sum := by decide
  have hdescent : baseEnd_5922028 < baseStart_5922028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922041 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 1, 2, 4]
def baseStart_5922041 : Nat := 118140960795 + 5922041 * 2 ^ 59
def prefixEnd_5922041 : Nat := 4983230072969 + 3 ^ 40 * 5922041 * 2
def baseEnd_5922041 : Nat := 3040853488632769721052535

theorem tailTrace_5922041 : CollatzResearch.WordTrace tailWord_5922041 prefixEnd_5922041 3040853488632769721052535 := by
  unfold tailWord_5922041
  simp only [CollatzResearch.WordTrace]
  refine ⟨215994579938464335925917977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143996386625642890617278651 215994579938464335925917977)
  ·
    refine ⟨161995934953848251944438483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215994579938464335925917977 161995934953848251944438483)
    ·
      refine ⟨242993902430772377916657725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161995934953848251944438483 242993902430772377916657725)
      ·
        refine ⟨91122713411539641718746647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242993902430772377916657725 91122713411539641718746647)
        ·
          refine ⟨136684070117309462578119971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91122713411539641718746647 136684070117309462578119971)
          ·
            refine ⟨205026105175964193867179957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136684070117309462578119971 205026105175964193867179957)
            ·
              refine ⟨19221197360246643175048121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205026105175964193867179957 19221197360246643175048121)
              ·
                refine ⟨14415898020184982381286091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19221197360246643175048121 14415898020184982381286091)
                ·
                  refine ⟨21623847030277473571929137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14415898020184982381286091 21623847030277473571929137)
                  ·
                    refine ⟨16217885272708105178946853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21623847030277473571929137 16217885272708105178946853)
                    ·
                      refine ⟨3040853488632769721052535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16217885272708105178946853 3040853488632769721052535)
                      ·
                        rfl

theorem cell23_5922041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_5922041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922041 prefixEnd_5922041 := by exact prefixLift 5922041
  have htrace : WordTrace (prefixWord ++ tailWord_5922041) baseStart_5922041 baseEnd_5922041 := by
    simpa [prefixWord, tailWord_5922041, baseEnd_5922041] using wordTrace_append hprefix tailTrace_5922041
  have hstable : (prefixWord ++ tailWord_5922041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922041).length < 2 ^ (prefixWord ++ tailWord_5922041).sum := by decide
  have hdescent : baseEnd_5922041 < baseStart_5922041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922056 : List Nat := [2, 1, 3, 2, 5, 1, 2, 2, 1, 1, 3]
def baseStart_5922056 : Nat := 118140960795 + 5922056 * 2 ^ 59
def prefixEnd_5922056 : Nat := 4983230072969 + 3 ^ 40 * 5922056 * 2
def baseEnd_5922056 : Nat := 3040861190842587162364967

theorem tailTrace_5922056 : CollatzResearch.WordTrace tailWord_5922056 prefixEnd_5922056 3040861190842587162364967 := by
  unfold tailWord_5922056
  simp only [CollatzResearch.WordTrace]
  refine ⟨107997563516704996743857011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143996751355606662325142681 107997563516704996743857011)
  ·
    refine ⟨161996345275057495115785517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107997563516704996743857011 161996345275057495115785517)
    ·
      refine ⟨60748629478146560668419569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161996345275057495115785517 60748629478146560668419569)
      ·
        refine ⟨45561472108609920501314677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60748629478146560668419569 45561472108609920501314677)
        ·
          refine ⟨4271388010182180046998251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45561472108609920501314677 4271388010182180046998251)
          ·
            refine ⟨6407082015273270070497377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4271388010182180046998251 6407082015273270070497377)
            ·
              refine ⟨4805311511454952552873033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6407082015273270070497377 4805311511454952552873033)
              ·
                refine ⟨3603983633591214414654775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4805311511454952552873033 3603983633591214414654775)
                ·
                  refine ⟨5405975450386821621982163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603983633591214414654775 5405975450386821621982163)
                  ·
                    refine ⟨8108963175580232432973245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5405975450386821621982163 8108963175580232432973245)
                    ·
                      refine ⟨3040861190842587162364967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8108963175580232432973245 3040861190842587162364967)
                      ·
                        rfl

theorem cell23_5922056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_5922056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922056 prefixEnd_5922056 := by exact prefixLift 5922056
  have htrace : WordTrace (prefixWord ++ tailWord_5922056) baseStart_5922056 baseEnd_5922056 := by
    simpa [prefixWord, tailWord_5922056, baseEnd_5922056] using wordTrace_append hprefix tailTrace_5922056
  have hstable : (prefixWord ++ tailWord_5922056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922056).length < 2 ^ (prefixWord ++ tailWord_5922056).sum := by decide
  have hdescent : baseEnd_5922056 < baseStart_5922056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922111 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 2, 6]
def baseStart_5922111 : Nat := 118140960795 + 5922111 * 2 ^ 59
def prefixEnd_5922111 : Nat := 4983230072969 + 3 ^ 40 * 5922111 * 2
def baseEnd_5922111 : Nat := 1013629810759528149059071

theorem tailTrace_5922111 : CollatzResearch.WordTrace tailWord_5922111 prefixEnd_5922111 1013629810759528149059071 := by
  unfold tailWord_5922111
  simp only [CollatzResearch.WordTrace]
  refine ⟨215997133048210737880966187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143998088698807158587310791 215997133048210737880966187)
  ·
    refine ⟨323995699572316106821449281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215997133048210737880966187 323995699572316106821449281)
    ·
      refine ⟨242996774679237080116086961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323995699572316106821449281 242996774679237080116086961)
      ·
        refine ⟨182247581009427810087065221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242996774679237080116086961 182247581009427810087065221)
        ·
          refine ⟨34171421439267714391324729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182247581009427810087065221 34171421439267714391324729)
          ·
            refine ⟨25628566079450785793493547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34171421439267714391324729 25628566079450785793493547)
            ·
              refine ⟨38442849119176178690240321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25628566079450785793493547 38442849119176178690240321)
              ·
                refine ⟨28832136839382134017680241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38442849119176178690240321 28832136839382134017680241)
                ·
                  refine ⟨21624102629536600513260181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28832136839382134017680241 21624102629536600513260181)
                  ·
                    refine ⟨1013629810759528149059071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21624102629536600513260181 1013629810759528149059071)
                    ·
                      rfl

theorem cell23_5922111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_5922111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922111 prefixEnd_5922111 := by exact prefixLift 5922111
  have htrace : WordTrace (prefixWord ++ tailWord_5922111) baseStart_5922111 baseEnd_5922111 := by
    simpa [prefixWord, tailWord_5922111, baseEnd_5922111] using wordTrace_append hprefix tailTrace_5922111
  have hstable : (prefixWord ++ tailWord_5922111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922111).length < 2 ^ (prefixWord ++ tailWord_5922111).sum := by decide
  have hdescent : baseEnd_5922111 < baseStart_5922111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922121 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 1, 6, 3]
def baseStart_5922121 : Nat := 118140960795 + 5922121 * 2 ^ 59
def prefixEnd_5922121 : Nat := 4983230072969 + 3 ^ 40 * 5922121 * 2
def baseEnd_5922121 : Nat := 3040894567085129408052167

theorem tailTrace_5922121 : CollatzResearch.WordTrace tailWord_5922121 prefixEnd_5922121 3040894567085129408052167 := by
  unfold tailWord_5922121
  simp only [CollatzResearch.WordTrace]
  refine ⟨215997497778174509588830217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143998331852116339725886811 215997497778174509588830217)
  ·
    refine ⟨161998123333630882191622663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215997497778174509588830217 161998123333630882191622663)
    ·
      refine ⟨242997185000446323287433995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161998123333630882191622663 242997185000446323287433995)
      ·
        refine ⟨364495777500669484931150993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242997185000446323287433995 364495777500669484931150993)
        ·
          refine ⟨273371833125502113698363245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364495777500669484931150993 273371833125502113698363245)
          ·
            refine ⟨102514437422063292636886217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273371833125502113698363245 102514437422063292636886217)
            ·
              refine ⟨76885828066547469477664663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102514437422063292636886217 76885828066547469477664663)
              ·
                refine ⟨115328742099821204216496995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76885828066547469477664663 115328742099821204216496995)
                ·
                  refine ⟨172993113149731806324745493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115328742099821204216496995 172993113149731806324745493)
                  ·
                    refine ⟨8109052178893678421472445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 172993113149731806324745493 8109052178893678421472445)
                    ·
                      refine ⟨3040894567085129408052167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8109052178893678421472445 3040894567085129408052167)
                      ·
                        rfl

theorem cell23_5922121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6, 3].length) (baseStart_5922121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922121 prefixEnd_5922121 := by exact prefixLift 5922121
  have htrace : WordTrace (prefixWord ++ tailWord_5922121) baseStart_5922121 baseEnd_5922121 := by
    simpa [prefixWord, tailWord_5922121, baseEnd_5922121] using wordTrace_append hprefix tailTrace_5922121
  have hstable : (prefixWord ++ tailWord_5922121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922121).length < 2 ^ (prefixWord ++ tailWord_5922121).sum := by decide
  have hdescent : baseEnd_5922121 < baseStart_5922121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922131 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 4]
def baseStart_5922131 : Nat := 118140960795 + 5922131 * 2 ^ 59
def prefixEnd_5922131 : Nat := 4983230072969 + 3 ^ 40 * 5922131 * 2
def baseEnd_5922131 : Nat := 3040899701891674368927121

theorem tailTrace_5922131 : CollatzResearch.WordTrace tailWord_5922131 prefixEnd_5922131 3040899701891674368927121 := by
  unfold tailWord_5922131
  simp only [CollatzResearch.WordTrace]
  refine ⟨215997862508138281296694247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143998575005425520864462831 215997862508138281296694247)
  ·
    refine ⟨323996793762207421945041371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215997862508138281296694247 323996793762207421945041371)
    ·
      refine ⟨485995190643311132917562057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323996793762207421945041371 485995190643311132917562057)
      ·
        refine ⟨364496392982483349688171543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485995190643311132917562057 364496392982483349688171543)
        ·
          refine ⟨546744589473725024532257315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364496392982483349688171543 546744589473725024532257315)
          ·
            refine ⟨820116884210587536798385973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546744589473725024532257315 820116884210587536798385973)
            ·
              refine ⟨76885957894742581574848685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 820116884210587536798385973 76885957894742581574848685)
              ·
                refine ⟨28832234210528468090568257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76885957894742581574848685 28832234210528468090568257)
                ·
                  refine ⟨21624175657896351067926193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28832234210528468090568257 21624175657896351067926193)
                  ·
                    refine ⟨16218131743422263300944645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21624175657896351067926193 16218131743422263300944645)
                    ·
                      refine ⟨3040899701891674368927121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16218131743422263300944645 3040899701891674368927121)
                      ·
                        rfl

theorem cell23_5922131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_5922131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922131 prefixEnd_5922131 := by exact prefixLift 5922131
  have htrace : WordTrace (prefixWord ++ tailWord_5922131) baseStart_5922131 baseEnd_5922131 := by
    simpa [prefixWord, tailWord_5922131, baseEnd_5922131] using wordTrace_append hprefix tailTrace_5922131
  have hstable : (prefixWord ++ tailWord_5922131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922131).length < 2 ^ (prefixWord ++ tailWord_5922131).sum := by decide
  have hdescent : baseEnd_5922131 < baseStart_5922131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922135 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 1, 4, 2]
def baseStart_5922135 : Nat := 118140960795 + 5922135 * 2 ^ 59
def prefixEnd_5922135 : Nat := 4983230072969 + 3 ^ 40 * 5922135 * 2
def baseEnd_5922135 : Nat := 3040901755814292353277103

theorem tailTrace_5922135 : CollatzResearch.WordTrace tailWord_5922135 prefixEnd_5922135 3040901755814292353277103 := by
  unfold tailWord_5922135
  simp only [CollatzResearch.WordTrace]
  refine ⟨215998008400123789979839859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143998672266749193319893239 215998008400123789979839859)
  ·
    refine ⟨323997012600185684969759789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215998008400123789979839859 323997012600185684969759789)
    ·
      refine ⟨121498879725069631863659921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323997012600185684969759789 121498879725069631863659921)
      ·
        refine ⟨91124159793802223897744941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121498879725069631863659921 91124159793802223897744941)
        ·
          refine ⟨34171559922675833961654353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91124159793802223897744941 34171559922675833961654353)
          ·
            refine ⟨25628669942006875471240765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34171559922675833961654353 25628669942006875471240765)
            ·
              refine ⟨9610751228252578301715287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25628669942006875471240765 9610751228252578301715287)
              ·
                refine ⟨14416126842378867452572931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9610751228252578301715287 14416126842378867452572931)
                ·
                  refine ⟨21624190263568301178859397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14416126842378867452572931 21624190263568301178859397)
                  ·
                    refine ⟨4054535674419056471036137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21624190263568301178859397 4054535674419056471036137)
                    ·
                      refine ⟨3040901755814292353277103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4054535674419056471036137 3040901755814292353277103)
                      ·
                        rfl

theorem cell23_5922135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_5922135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922135 prefixEnd_5922135 := by exact prefixLift 5922135
  have htrace : WordTrace (prefixWord ++ tailWord_5922135) baseStart_5922135 baseEnd_5922135 := by
    simpa [prefixWord, tailWord_5922135, baseEnd_5922135] using wordTrace_append hprefix tailTrace_5922135
  have hstable : (prefixWord ++ tailWord_5922135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922135).length < 2 ^ (prefixWord ++ tailWord_5922135).sum := by decide
  have hdescent : baseEnd_5922135 < baseStart_5922135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922181 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_5922181 : Nat := 118140960795 + 5922181 * 2 ^ 59
def prefixEnd_5922181 : Nat := 4983230072969 + 3 ^ 40 * 5922181 * 2
def baseEnd_5922181 : Nat := 3040925375924399173301891

theorem tailTrace_5922181 : CollatzResearch.WordTrace tailWord_5922181 prefixEnd_5922181 3040925375924399173301891 := by
  unfold tailWord_5922181
  simp only [CollatzResearch.WordTrace]
  refine ⟨215999686157957139836014397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143999790771971426557342931 215999686157957139836014397)
  ·
    refine ⟨80999882309233927438505399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215999686157957139836014397 80999882309233927438505399)
    ·
      refine ⟨121499823463850891157758099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80999882309233927438505399 121499823463850891157758099)
      ·
        refine ⟨182249735195776336736637149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121499823463850891157758099 182249735195776336736637149)
        ·
          refine ⟨68343650698416126276238931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182249735195776336736637149 68343650698416126276238931)
          ·
            refine ⟨102515476047624189414358397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68343650698416126276238931 102515476047624189414358397)
            ·
              refine ⟨38443303517859071030384399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102515476047624189414358397 38443303517859071030384399)
              ·
                refine ⟨57664955276788606545576599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38443303517859071030384399 57664955276788606545576599)
                ·
                  refine ⟨86497432915182909818364899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57664955276788606545576599 86497432915182909818364899)
                  ·
                    refine ⟨129746149372774364727547349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86497432915182909818364899 129746149372774364727547349)
                    ·
                      refine ⟨3040925375924399173301891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129746149372774364727547349 3040925375924399173301891)
                      ·
                        rfl

theorem cell23_5922181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_5922181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922181 prefixEnd_5922181 := by exact prefixLift 5922181
  have htrace : WordTrace (prefixWord ++ tailWord_5922181) baseStart_5922181 baseEnd_5922181 := by
    simpa [prefixWord, tailWord_5922181, baseEnd_5922181] using wordTrace_append hprefix tailTrace_5922181
  have hstable : (prefixWord ++ tailWord_5922181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922181).length < 2 ^ (prefixWord ++ tailWord_5922181).sum := by decide
  have hdescent : baseEnd_5922181 < baseStart_5922181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922205 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_5922205 : Nat := 118140960795 + 5922205 * 2 ^ 59
def prefixEnd_5922205 : Nat := 4983230072969 + 3 ^ 40 * 5922205 * 2
def baseEnd_5922205 : Nat := 1013645899820035693133927

theorem tailTrace_5922205 : CollatzResearch.WordTrace tailWord_5922205 prefixEnd_5922205 1013645899820035693133927 := by
  unfold tailWord_5922205
  simp only [CollatzResearch.WordTrace]
  refine ⟨216000561509870191934888069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144000374339913461289925379 216000561509870191934888069)
  ·
    refine ⟨40500105283100660987791513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216000561509870191934888069 40500105283100660987791513)
    ·
      refine ⟨30375078962325495740843635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40500105283100660987791513 30375078962325495740843635)
      ·
        refine ⟨45562618443488243611265453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30375078962325495740843635 45562618443488243611265453)
        ·
          refine ⟨17085981916308091354224545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45562618443488243611265453 17085981916308091354224545)
          ·
            refine ⟨12814486437231068515668409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17085981916308091354224545 12814486437231068515668409)
            ·
              refine ⟨9610864827923301386751307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12814486437231068515668409 9610864827923301386751307)
              ·
                refine ⟨14416297241884952080126961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9610864827923301386751307 14416297241884952080126961)
                ·
                  refine ⟨10812222931413714060095221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14416297241884952080126961 10812222931413714060095221)
                  ·
                    refine ⟨1013645899820035693133927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10812222931413714060095221 1013645899820035693133927)
                    ·
                      rfl

theorem cell23_5922205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_5922205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922205 prefixEnd_5922205 := by exact prefixLift 5922205
  have htrace : WordTrace (prefixWord ++ tailWord_5922205) baseStart_5922205 baseEnd_5922205 := by
    simpa [prefixWord, tailWord_5922205, baseEnd_5922205] using wordTrace_append hprefix tailTrace_5922205
  have hstable : (prefixWord ++ tailWord_5922205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922205).length < 2 ^ (prefixWord ++ tailWord_5922205).sum := by decide
  have hdescent : baseEnd_5922205 < baseStart_5922205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922225 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 2, 4, 2]
def baseStart_5922225 : Nat := 118140960795 + 5922225 * 2 ^ 59
def prefixEnd_5922225 : Nat := 4983230072969 + 3 ^ 40 * 5922225 * 2
def baseEnd_5922225 : Nat := 3040947969073197001151689

theorem tailTrace_5922225 : CollatzResearch.WordTrace tailWord_5922225 prefixEnd_5922225 3040947969073197001151689 := by
  unfold tailWord_5922225
  simp only [CollatzResearch.WordTrace]
  refine ⟨216001290969797735350616129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144000860646531823567077419 216001290969797735350616129)
  ·
    refine ⟨162000968227348301512962097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216001290969797735350616129 162000968227348301512962097)
    ·
      refine ⟨121500726170511226134721573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162000968227348301512962097 121500726170511226134721573)
      ·
        refine ⟨22781386156970854900260295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121500726170511226134721573 22781386156970854900260295)
        ·
          refine ⟨34172079235456282350390443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22781386156970854900260295 34172079235456282350390443)
          ·
            refine ⟨51258118853184423525585665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34172079235456282350390443 51258118853184423525585665)
            ·
              refine ⟨38443589139888317644189249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51258118853184423525585665 38443589139888317644189249)
              ·
                refine ⟨28832691854916238233141937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38443589139888317644189249 28832691854916238233141937)
                ·
                  refine ⟨21624518891187178674856453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28832691854916238233141937 21624518891187178674856453)
                  ·
                    refine ⟨4054597292097596001535585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21624518891187178674856453 4054597292097596001535585)
                    ·
                      refine ⟨3040947969073197001151689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4054597292097596001535585 3040947969073197001151689)
                      ·
                        rfl

theorem cell23_5922225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_5922225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922225 prefixEnd_5922225 := by exact prefixLift 5922225
  have htrace : WordTrace (prefixWord ++ tailWord_5922225) baseStart_5922225 baseEnd_5922225 := by
    simpa [prefixWord, tailWord_5922225, baseEnd_5922225] using wordTrace_append hprefix tailTrace_5922225
  have hstable : (prefixWord ++ tailWord_5922225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922225).length < 2 ^ (prefixWord ++ tailWord_5922225).sum := by decide
  have hdescent : baseEnd_5922225 < baseStart_5922225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922238 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_5922238 : Nat := 118140960795 + 5922238 * 2 ^ 59
def prefixEnd_5922238 : Nat := 4983230072969 + 3 ^ 40 * 5922238 * 2
def baseEnd_5922238 : Nat := 3040954644321705450289129

theorem tailTrace_5922238 : CollatzResearch.WordTrace tailWord_5922238 prefixEnd_5922238 3040954644321705450289129 := by
  unfold tailWord_5922238
  simp only [CollatzResearch.WordTrace]
  refine ⟨27000220639843829821354921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144001176745833759047226245 27000220639843829821354921)
  ·
    refine ⟨20250165479882872366016191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27000220639843829821354921 20250165479882872366016191)
    ·
      refine ⟨30375248219824308549024287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20250165479882872366016191 30375248219824308549024287)
      ·
        refine ⟨45562872329736462823536431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30375248219824308549024287 45562872329736462823536431)
        ·
          refine ⟨68344308494604694235304647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45562872329736462823536431 68344308494604694235304647)
          ·
            refine ⟨102516462741907041352956971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68344308494604694235304647 102516462741907041352956971)
            ·
              refine ⟨153774694112860562029435457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102516462741907041352956971 153774694112860562029435457)
              ·
                refine ⟨115331020584645421522076593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153774694112860562029435457 115331020584645421522076593)
                ·
                  refine ⟨86498265438484066141557445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115331020584645421522076593 86498265438484066141557445)
                  ·
                    refine ⟨16218424769715762401542021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86498265438484066141557445 16218424769715762401542021)
                    ·
                      refine ⟨3040954644321705450289129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16218424769715762401542021 3040954644321705450289129)
                      ·
                        rfl

theorem cell23_5922238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_5922238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922238 prefixEnd_5922238 := by exact prefixLift 5922238
  have htrace : WordTrace (prefixWord ++ tailWord_5922238) baseStart_5922238 baseEnd_5922238 := by
    simpa [prefixWord, tailWord_5922238, baseEnd_5922238] using wordTrace_append hprefix tailTrace_5922238
  have hstable : (prefixWord ++ tailWord_5922238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922238).length < 2 ^ (prefixWord ++ tailWord_5922238).sum := by decide
  have hdescent : baseEnd_5922238 < baseStart_5922238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922248 : List Nat := [2, 1, 3, 1, 3, 1, 1, 5, 6]
def baseStart_5922248 : Nat := 118140960795 + 5922248 * 2 ^ 59
def prefixEnd_5922248 : Nat := 4983230072969 + 3 ^ 40 * 5922248 * 2
def baseEnd_5922248 : Nat := 337884419903138934573787

theorem tailTrace_5922248 : CollatzResearch.WordTrace tailWord_5922248 prefixEnd_5922248 337884419903138934573787 := by
  unfold tailWord_5922248
  simp only [CollatzResearch.WordTrace]
  refine ⟨108001064924357205139351699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144001419899142940185802265 108001064924357205139351699)
  ·
    refine ⟨162001597386535807709027549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108001064924357205139351699 162001597386535807709027549)
    ·
      refine ⟨60750599019950927890885331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162001597386535807709027549 60750599019950927890885331)
      ·
        refine ⟨91125898529926391836327997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60750599019950927890885331 91125898529926391836327997)
        ·
          refine ⟨34172211948722396938622999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91125898529926391836327997 34172211948722396938622999)
          ·
            refine ⟨51258317923083595407934499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34172211948722396938622999 51258317923083595407934499)
            ·
              refine ⟨76887476884625393111901749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51258317923083595407934499 76887476884625393111901749)
              ·
                refine ⟨7208200957933630604240789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76887476884625393111901749 7208200957933630604240789)
                ·
                  refine ⟨337884419903138934573787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7208200957933630604240789 337884419903138934573787)
                  ·
                    rfl

theorem cell23_5922248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 6].length) (baseStart_5922248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922248 prefixEnd_5922248 := by exact prefixLift 5922248
  have htrace : WordTrace (prefixWord ++ tailWord_5922248) baseStart_5922248 baseEnd_5922248 := by
    simpa [prefixWord, tailWord_5922248, baseEnd_5922248] using wordTrace_append hprefix tailTrace_5922248
  have hstable : (prefixWord ++ tailWord_5922248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922248).length < 2 ^ (prefixWord ++ tailWord_5922248).sum := by decide
  have hdescent : baseEnd_5922248 < baseStart_5922248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922262 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_5922262 : Nat := 118140960795 + 5922262 * 2 ^ 59
def prefixEnd_5922262 : Nat := 4983230072969 + 3 ^ 40 * 5922262 * 2
def baseEnd_5922262 : Nat := 3040966967857413356389019

theorem tailTrace_5922262 : CollatzResearch.WordTrace tailWord_5922262 prefixEnd_5922262 3040966967857413356389019 := by
  unfold tailWord_5922262
  simp only [CollatzResearch.WordTrace]
  refine ⟨13500165029416480666857065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144001760313775793779808693 13500165029416480666857065)
  ·
    refine ⟨10125123772062360500142799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13500165029416480666857065 10125123772062360500142799)
    ·
      refine ⟨15187685658093540750214199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10125123772062360500142799 15187685658093540750214199)
      ·
        refine ⟨22781528487140311125321299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15187685658093540750214199 22781528487140311125321299)
        ·
          refine ⟨34172292730710466687981949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22781528487140311125321299 34172292730710466687981949)
          ·
            refine ⟨12814609774016425007993231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34172292730710466687981949 12814609774016425007993231)
            ·
              refine ⟨19221914661024637511989847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12814609774016425007993231 19221914661024637511989847)
              ·
                refine ⟨28832871991536956267984771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19221914661024637511989847 28832871991536956267984771)
                ·
                  refine ⟨43249307987305434401977157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28832871991536956267984771 43249307987305434401977157)
                  ·
                    refine ⟨8109245247619768950370717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43249307987305434401977157 8109245247619768950370717)
                    ·
                      refine ⟨3040966967857413356389019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8109245247619768950370717 3040966967857413356389019)
                      ·
                        rfl

theorem cell23_5922262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_5922262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922262 prefixEnd_5922262 := by exact prefixLift 5922262
  have htrace : WordTrace (prefixWord ++ tailWord_5922262) baseStart_5922262 baseEnd_5922262 := by
    simpa [prefixWord, tailWord_5922262, baseEnd_5922262] using wordTrace_append hprefix tailTrace_5922262
  have hstable : (prefixWord ++ tailWord_5922262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922262).length < 2 ^ (prefixWord ++ tailWord_5922262).sum := by decide
  have hdescent : baseEnd_5922262 < baseStart_5922262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922269 : List Nat := [1, 4, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_5922269 : Nat := 118140960795 + 5922269 * 2 ^ 59
def prefixEnd_5922269 : Nat := 4983230072969 + 3 ^ 40 * 5922269 * 2
def baseEnd_5922269 : Nat := 1013656854073998276333829

theorem tailTrace_5922269 : CollatzResearch.WordTrace tailWord_5922269 prefixEnd_5922269 1013656854073998276333829 := by
  unfold tailWord_5922269
  simp only [CollatzResearch.WordTrace]
  refine ⟨216002895781638330865217861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144001930521092220576811907 216002895781638330865217861)
  ·
    refine ⟨40500542959057187037228349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216002895781638330865217861 40500542959057187037228349)
    ·
      refine ⟨15187703609646445138960631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40500542959057187037228349 15187703609646445138960631)
      ·
        refine ⟨22781555414469667708440947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15187703609646445138960631 22781555414469667708440947)
        ·
          refine ⟨34172333121704501562661421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22781555414469667708440947 34172333121704501562661421)
          ·
            refine ⟨12814624920639188085998033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34172333121704501562661421 12814624920639188085998033)
            ·
              refine ⟨9610968690479391064498525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12814624920639188085998033 9610968690479391064498525)
              ·
                refine ⟨3604113258929771649186947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9610968690479391064498525 3604113258929771649186947)
                ·
                  refine ⟨5406169888394657473780421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604113258929771649186947 5406169888394657473780421)
                  ·
                    refine ⟨1013656854073998276333829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5406169888394657473780421 1013656854073998276333829)
                    ·
                      rfl

theorem cell23_5922269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_5922269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922269 prefixEnd_5922269 := by exact prefixLift 5922269
  have htrace : WordTrace (prefixWord ++ tailWord_5922269) baseStart_5922269 baseEnd_5922269 := by
    simpa [prefixWord, tailWord_5922269, baseEnd_5922269] using wordTrace_append hprefix tailTrace_5922269
  have hstable : (prefixWord ++ tailWord_5922269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922269).length < 2 ^ (prefixWord ++ tailWord_5922269).sum := by decide
  have hdescent : baseEnd_5922269 < baseStart_5922269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922282 : List Nat := [3, 1, 3, 1, 4, 2, 1, 2, 6]
def baseStart_5922282 : Nat := 118140960795 + 5922282 * 2 ^ 59
def prefixEnd_5922282 : Nat := 4983230072969 + 3 ^ 40 * 5922282 * 2
def baseEnd_5922282 : Nat := 337886359718944808682103

theorem tailTrace_5922282 : CollatzResearch.WordTrace tailWord_5922282 prefixEnd_5922282 337886359718944808682103 := by
  unfold tailWord_5922282
  simp only [CollatzResearch.WordTrace]
  refine ⟨54000842482647808521360275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144002246620394156056960733 54000842482647808521360275)
  ·
    refine ⟨81001263723971712782040413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54000842482647808521360275 81001263723971712782040413)
    ·
      refine ⟨30375473896489392293265155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81001263723971712782040413 30375473896489392293265155)
      ·
        refine ⟨45563210844734088439897733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30375473896489392293265155 45563210844734088439897733)
        ·
          refine ⟨8543102033387641582480825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45563210844734088439897733 8543102033387641582480825)
          ·
            refine ⟨6407326525040731186860619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8543102033387641582480825 6407326525040731186860619)
            ·
              refine ⟨9610989787561096780290929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6407326525040731186860619 9610989787561096780290929)
              ·
                refine ⟨7208242340670822585218197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9610989787561096780290929 7208242340670822585218197)
                ·
                  refine ⟨337886359718944808682103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7208242340670822585218197 337886359718944808682103)
                  ·
                    rfl

theorem cell23_5922282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_5922282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922282 prefixEnd_5922282 := by exact prefixLift 5922282
  have htrace : WordTrace (prefixWord ++ tailWord_5922282) baseStart_5922282 baseEnd_5922282 := by
    simpa [prefixWord, tailWord_5922282, baseEnd_5922282] using wordTrace_append hprefix tailTrace_5922282
  have hstable : (prefixWord ++ tailWord_5922282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922282).length < 2 ^ (prefixWord ++ tailWord_5922282).sum := by decide
  have hdescent : baseEnd_5922282 < baseStart_5922282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922325 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 4, 4]
def baseStart_5922325 : Nat := 118140960795 + 5922325 * 2 ^ 59
def prefixEnd_5922325 : Nat := 4983230072969 + 3 ^ 40 * 5922325 * 2
def baseEnd_5922325 : Nat := 1013666439046215536633743

theorem tailTrace_5922325 : CollatzResearch.WordTrace tailWord_5922325 prefixEnd_5922325 1013666439046215536633743 := by
  unfold tailWord_5922325
  simp only [CollatzResearch.WordTrace]
  refine ⟨216004938269435452429256429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144003292179623634952837619 216004938269435452429256429)
  ·
    refine ⟨81001851851038294660971161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216004938269435452429256429 81001851851038294660971161)
    ·
      refine ⟨60751388888278720995728371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81001851851038294660971161 60751388888278720995728371)
      ·
        refine ⟨91127083332418081493592557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60751388888278720995728371 91127083332418081493592557)
        ·
          refine ⟨34172656249656780560097209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91127083332418081493592557 34172656249656780560097209)
          ·
            refine ⟨25629492187242585420072907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34172656249656780560097209 25629492187242585420072907)
            ·
              refine ⟨38444238280863878130109361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25629492187242585420072907 38444238280863878130109361)
              ·
                refine ⟨28833178710647908597582021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38444238280863878130109361 28833178710647908597582021)
                ·
                  refine ⟨5406221008246482862046629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28833178710647908597582021 5406221008246482862046629)
                  ·
                    refine ⟨1013666439046215536633743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5406221008246482862046629 1013666439046215536633743)
                    ·
                      rfl

theorem cell23_5922325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_5922325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922325 prefixEnd_5922325 := by exact prefixLift 5922325
  have htrace : WordTrace (prefixWord ++ tailWord_5922325) baseStart_5922325 baseEnd_5922325 := by
    simpa [prefixWord, tailWord_5922325, baseEnd_5922325] using wordTrace_append hprefix tailTrace_5922325
  have hstable : (prefixWord ++ tailWord_5922325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922325).length < 2 ^ (prefixWord ++ tailWord_5922325).sum := by decide
  have hdescent : baseEnd_5922325 < baseStart_5922325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922338 : List Nat := [3, 3, 1, 1, 1, 1, 13]
def baseStart_5922338 : Nat := 118140960795 + 5922338 * 2 ^ 59
def prefixEnd_5922338 : Nat := 4983230072969 + 3 ^ 40 * 5922338 * 2
def baseEnd_5922338 : Nat := 37543283856631543938749

theorem tailTrace_5922338 : CollatzResearch.WordTrace tailWord_5922338 prefixEnd_5922338 37543283856631543938749 := by
  unfold tailWord_5922338
  simp only [CollatzResearch.WordTrace]
  refine ⟨54001353104597088912369917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144003608278925570432986445 54001353104597088912369917)
  ·
    refine ⟨20250507414223908342138719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54001353104597088912369917 20250507414223908342138719)
    ·
      refine ⟨30375761121335862513208079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20250507414223908342138719 30375761121335862513208079)
      ·
        refine ⟨45563641682003793769812119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30375761121335862513208079 45563641682003793769812119)
        ·
          refine ⟨68345462523005690654718179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45563641682003793769812119 68345462523005690654718179)
          ·
            refine ⟨102518193784508535982077269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68345462523005690654718179 102518193784508535982077269)
            ·
              refine ⟨37543283856631543938749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 102518193784508535982077269 37543283856631543938749)
              ·
                rfl

theorem cell23_5922338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 13].length) (baseStart_5922338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922338 prefixEnd_5922338 := by exact prefixLift 5922338
  have htrace : WordTrace (prefixWord ++ tailWord_5922338) baseStart_5922338 baseEnd_5922338 := by
    simpa [prefixWord, tailWord_5922338, baseEnd_5922338] using wordTrace_append hprefix tailTrace_5922338
  have hstable : (prefixWord ++ tailWord_5922338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922338).length < 2 ^ (prefixWord ++ tailWord_5922338).sum := by decide
  have hdescent : baseEnd_5922338 < baseStart_5922338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922359 : List Nat := [1, 1, 3, 1, 2, 6, 2, 1, 2, 4]
def baseStart_5922359 : Nat := 118140960795 + 5922359 * 2 ^ 59
def prefixEnd_5922359 : Nat := 4983230072969 + 3 ^ 40 * 5922359 * 2
def baseEnd_5922359 : Nat := 1013672258493633158958691

theorem tailTrace_5922359 : CollatzResearch.WordTrace tailWord_5922359 prefixEnd_5922359 1013672258493633158958691 := by
  unfold tailWord_5922359
  simp only [CollatzResearch.WordTrace]
  refine ⟨216006178351312276235994131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144004118900874850823996087 216006178351312276235994131)
  ·
    refine ⟨324009267526968414353991197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216006178351312276235994131 324009267526968414353991197)
    ·
      refine ⟨121503475322613155382746699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324009267526968414353991197 121503475322613155382746699)
      ·
        refine ⟨182255212983919733074120049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121503475322613155382746699 182255212983919733074120049)
        ·
          refine ⟨136691409737939799805590037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182255212983919733074120049 136691409737939799805590037)
          ·
            refine ⟨6407409831465928115887033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136691409737939799805590037 6407409831465928115887033)
            ·
              refine ⟨4805557373599446086915275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6407409831465928115887033 4805557373599446086915275)
              ·
                refine ⟨7208336060399169130372913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4805557373599446086915275 7208336060399169130372913)
                ·
                  refine ⟨5406252045299376847779685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7208336060399169130372913 5406252045299376847779685)
                  ·
                    refine ⟨1013672258493633158958691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5406252045299376847779685 1013672258493633158958691)
                    ·
                      rfl

theorem cell23_5922359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_5922359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922359 prefixEnd_5922359 := by exact prefixLift 5922359
  have htrace : WordTrace (prefixWord ++ tailWord_5922359) baseStart_5922359 baseEnd_5922359 := by
    simpa [prefixWord, tailWord_5922359, baseEnd_5922359] using wordTrace_append hprefix tailTrace_5922359
  have hstable : (prefixWord ++ tailWord_5922359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922359).length < 2 ^ (prefixWord ++ tailWord_5922359).sum := by decide
  have hdescent : baseEnd_5922359 < baseStart_5922359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922405 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_5922405 : Nat := 118140960795 + 5922405 * 2 ^ 59
def prefixEnd_5922405 : Nat := 4983230072969 + 3 ^ 40 * 5922405 * 2
def baseEnd_5922405 : Nat := 3041040395591006296900861

theorem tailTrace_5922405 : CollatzResearch.WordTrace tailWord_5922405 prefixEnd_5922405 3041040395591006296900861 := by
  unfold tailWord_5922405
  simp only [CollatzResearch.WordTrace]
  refine ⟨216007856109145626092168669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144005237406097084061445779 216007856109145626092168669)
  ·
    refine ⟨81002946040929609784563251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216007856109145626092168669 81002946040929609784563251)
    ·
      refine ⟨121504419061394414676844877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81002946040929609784563251 121504419061394414676844877)
      ·
        refine ⟨45564157148022905503816829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121504419061394414676844877 45564157148022905503816829)
        ·
          refine ⟨17086558930508589563931311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45564157148022905503816829 17086558930508589563931311)
          ·
            refine ⟨25629838395762884345896967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17086558930508589563931311 25629838395762884345896967)
            ·
              refine ⟨38444757593644326518845451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25629838395762884345896967 38444757593644326518845451)
              ·
                refine ⟨57667136390466489778268177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38444757593644326518845451 57667136390466489778268177)
                ·
                  refine ⟨43250352292849867333701133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57667136390466489778268177 43250352292849867333701133)
                  ·
                    refine ⟨16218882109818700250137925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43250352292849867333701133 16218882109818700250137925)
                    ·
                      refine ⟨3041040395591006296900861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16218882109818700250137925 3041040395591006296900861)
                      ·
                        rfl

theorem cell23_5922405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_5922405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922405 prefixEnd_5922405 := by exact prefixLift 5922405
  have htrace : WordTrace (prefixWord ++ tailWord_5922405) baseStart_5922405 baseEnd_5922405 := by
    simpa [prefixWord, tailWord_5922405, baseEnd_5922405] using wordTrace_append hprefix tailTrace_5922405
  have hstable : (prefixWord ++ tailWord_5922405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922405).length < 2 ^ (prefixWord ++ tailWord_5922405).sum := by decide
  have hdescent : baseEnd_5922405 < baseStart_5922405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922425 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 2, 4, 3]
def baseStart_5922425 : Nat := 118140960795 + 5922425 * 2 ^ 59
def prefixEnd_5922425 : Nat := 4983230072969 + 3 ^ 40 * 5922425 * 2
def baseEnd_5922425 : Nat := 3041050665204096218650769

theorem tailTrace_5922425 : CollatzResearch.WordTrace tailWord_5922425 prefixEnd_5922425 3041050665204096218650769 := by
  unfold tailWord_5922425
  simp only [CollatzResearch.WordTrace]
  refine ⟨216008585569073169507896729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144005723712715446338597819 216008585569073169507896729)
  ·
    refine ⟨162006439176804877130922547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216008585569073169507896729 162006439176804877130922547)
    ·
      refine ⟨243009658765207315696383821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162006439176804877130922547 243009658765207315696383821)
      ·
        refine ⟨91128622036952743386143933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243009658765207315696383821 91128622036952743386143933)
        ·
          refine ⟨34173233263857278769803975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91128622036952743386143933 34173233263857278769803975)
          ·
            refine ⟨51259849895785918154705963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34173233263857278769803975 51259849895785918154705963)
            ·
              refine ⟨76889774843678877232058945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51259849895785918154705963 76889774843678877232058945)
              ·
                refine ⟨57667331132759157924044209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76889774843678877232058945 57667331132759157924044209)
                ·
                  refine ⟨43250498349569368443033157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57667331132759157924044209 43250498349569368443033157)
                  ·
                    refine ⟨8109468440544256583068717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43250498349569368443033157 8109468440544256583068717)
                    ·
                      refine ⟨3041050665204096218650769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8109468440544256583068717 3041050665204096218650769)
                      ·
                        rfl

theorem cell23_5922425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_5922425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922425 prefixEnd_5922425 := by exact prefixLift 5922425
  have htrace : WordTrace (prefixWord ++ tailWord_5922425) baseStart_5922425 baseEnd_5922425 := by
    simpa [prefixWord, tailWord_5922425, baseEnd_5922425] using wordTrace_append hprefix tailTrace_5922425
  have hstable : (prefixWord ++ tailWord_5922425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922425).length < 2 ^ (prefixWord ++ tailWord_5922425).sum := by decide
  have hdescent : baseEnd_5922425 < baseStart_5922425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922456 : List Nat := [2, 1, 2, 4, 1, 2, 3, 2, 2, 2, 2]
def baseStart_5922456 : Nat := 118140960795 + 5922456 * 2 ^ 59
def prefixEnd_5922456 : Nat := 4983230072969 + 3 ^ 40 * 5922456 * 2
def baseEnd_5922456 : Nat := 3041066583104385597363127

theorem tailTrace_5922456 : CollatzResearch.WordTrace tailWord_5922456 prefixEnd_5922456 3041066583104385597363127 := by
  unfold tailWord_5922456
  simp only [CollatzResearch.WordTrace]
  refine ⟨108004858115980430901137611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144006477487973907868183481 108004858115980430901137611)
  ·
    refine ⟨162007287173970646351706417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108004858115980430901137611 162007287173970646351706417)
    ·
      refine ⟨121505465380477984763779813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162007287173970646351706417 121505465380477984763779813)
      ·
        refine ⟨22782274758839622143208715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121505465380477984763779813 22782274758839622143208715)
        ·
          refine ⟨34173412138259433214813073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22782274758839622143208715 34173412138259433214813073)
          ·
            refine ⟨25630059103694574911109805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34173412138259433214813073 25630059103694574911109805)
            ·
              refine ⟨9611272163885465591666177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25630059103694574911109805 9611272163885465591666177)
              ·
                refine ⟨7208454122914099193749633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9611272163885465591666177 7208454122914099193749633)
                ·
                  refine ⟨5406340592185574395312225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7208454122914099193749633 5406340592185574395312225)
                  ·
                    refine ⟨4054755444139180796484169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5406340592185574395312225 4054755444139180796484169)
                    ·
                      refine ⟨3041066583104385597363127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4054755444139180796484169 3041066583104385597363127)
                      ·
                        rfl

theorem cell23_5922456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_5922456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922456 prefixEnd_5922456 := by exact prefixLift 5922456
  have htrace : WordTrace (prefixWord ++ tailWord_5922456) baseStart_5922456 baseEnd_5922456 := by
    simpa [prefixWord, tailWord_5922456, baseEnd_5922456] using wordTrace_append hprefix tailTrace_5922456
  have hstable : (prefixWord ++ tailWord_5922456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922456).length < 2 ^ (prefixWord ++ tailWord_5922456).sum := by decide
  have hdescent : baseEnd_5922456 < baseStart_5922456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922462 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 7]
def baseStart_5922462 : Nat := 118140960795 + 5922462 * 2 ^ 59
def prefixEnd_5922462 : Nat := 4983230072969 + 3 ^ 40 * 5922462 * 2
def baseEnd_5922462 : Nat := 337896629332034730432011

theorem tailTrace_5922462 : CollatzResearch.WordTrace tailWord_5922462 prefixEnd_5922462 337896629332034730432011 := by
  unfold tailWord_5922462
  simp only [CollatzResearch.WordTrace]
  refine ⟨27001241883742390603374205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144006623379959416551329093 27001241883742390603374205)
  ·
    refine ⟨10125465706403396476265327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27001241883742390603374205 10125465706403396476265327)
    ·
      refine ⟨15188198559605094714397991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10125465706403396476265327 15188198559605094714397991)
      ·
        refine ⟨22782297839407642071596987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15188198559605094714397991 22782297839407642071596987)
        ·
          refine ⟨34173446759111463107395481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22782297839407642071596987 34173446759111463107395481)
          ·
            refine ⟨25630085069333597330546611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34173446759111463107395481 25630085069333597330546611)
            ·
              refine ⟨38445127604000395995819917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25630085069333597330546611 38445127604000395995819917)
              ·
                refine ⟨14416922851500148498432469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38445127604000395995819917 14416922851500148498432469)
                ·
                  refine ⟨337896629332034730432011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14416922851500148498432469 337896629332034730432011)
                  ·
                    rfl

theorem cell23_5922462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_5922462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922462 prefixEnd_5922462 := by exact prefixLift 5922462
  have htrace : WordTrace (prefixWord ++ tailWord_5922462) baseStart_5922462 baseEnd_5922462 := by
    simpa [prefixWord, tailWord_5922462, baseEnd_5922462] using wordTrace_append hprefix tailTrace_5922462
  have hstable : (prefixWord ++ tailWord_5922462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922462).length < 2 ^ (prefixWord ++ tailWord_5922462).sum := by decide
  have hdescent : baseEnd_5922462 < baseStart_5922462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922482 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2]
def baseStart_5922482 : Nat := 118140960795 + 5922482 * 2 ^ 59
def prefixEnd_5922482 : Nat := 4983230072969 + 3 ^ 40 * 5922482 * 2
def baseEnd_5922482 : Nat := 3041079933601402495638007

theorem tailTrace_5922482 : CollatzResearch.WordTrace tailWord_5922482 prefixEnd_5922482 3041079933601402495638007 := by
  unfold tailWord_5922482
  simp only [CollatzResearch.WordTrace]
  refine ⟨54002666132466667060680425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144007109686577778828481133 54002666132466667060680425)
  ·
    refine ⟨40501999599350000295510319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54002666132466667060680425 40501999599350000295510319)
    ·
      refine ⟨60752999399025000443265479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40501999599350000295510319 60752999399025000443265479)
      ·
        refine ⟨91129499098537500664898219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60752999399025000443265479 91129499098537500664898219)
        ·
          refine ⟨136694248647806250997347329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91129499098537500664898219 136694248647806250997347329)
          ·
            refine ⟨102520686485854688248010497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136694248647806250997347329 102520686485854688248010497)
            ·
              refine ⟨76890514864391016186007873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102520686485854688248010497 76890514864391016186007873)
              ·
                refine ⟨57667886148293262139505905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76890514864391016186007873 57667886148293262139505905)
                ·
                  refine ⟨43250914611219946604629429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57667886148293262139505905 43250914611219946604629429)
                  ·
                    refine ⟨4054773244801869994184009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43250914611219946604629429 4054773244801869994184009)
                    ·
                      refine ⟨3041079933601402495638007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4054773244801869994184009 3041079933601402495638007)
                      ·
                        rfl

theorem cell23_5922482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_5922482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922482 prefixEnd_5922482 := by exact prefixLift 5922482
  have htrace : WordTrace (prefixWord ++ tailWord_5922482) baseStart_5922482 baseEnd_5922482 := by
    simpa [prefixWord, tailWord_5922482, baseEnd_5922482] using wordTrace_append hprefix tailTrace_5922482
  have hstable : (prefixWord ++ tailWord_5922482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922482).length < 2 ^ (prefixWord ++ tailWord_5922482).sum := by decide
  have hdescent : baseEnd_5922482 < baseStart_5922482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922495 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 4]
def baseStart_5922495 : Nat := 118140960795 + 5922495 * 2 ^ 59
def prefixEnd_5922495 : Nat := 4983230072969 + 3 ^ 40 * 5922495 * 2
def baseEnd_5922495 : Nat := 3041086608849910944775447

theorem tailTrace_5922495 : CollatzResearch.WordTrace tailWord_5922495 prefixEnd_5922495 3041086608849910944775447 := by
  unfold tailWord_5922495
  simp only [CollatzResearch.WordTrace]
  refine ⟨216011138678819571462944939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144007425785879714308629959 216011138678819571462944939)
  ·
    refine ⟨324016708018229357194417409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216011138678819571462944939 324016708018229357194417409)
    ·
      refine ⟨243012531013672017895813057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324016708018229357194417409 243012531013672017895813057)
      ·
        refine ⟨182259398260254013421859793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243012531013672017895813057 182259398260254013421859793)
        ·
          refine ⟨136694548695190510066394845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182259398260254013421859793 136694548695190510066394845)
          ·
            refine ⟨51260455760696441274898067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136694548695190510066394845 51260455760696441274898067)
            ·
              refine ⟨76890683641044661912347101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51260455760696441274898067 76890683641044661912347101)
              ·
                refine ⟨28834006365391748217130163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76890683641044661912347101 28834006365391748217130163)
                ·
                  refine ⟨43251009548087622325695245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28834006365391748217130163 43251009548087622325695245)
                  ·
                    refine ⟨16219128580532858372135717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43251009548087622325695245 16219128580532858372135717)
                    ·
                      refine ⟨3041086608849910944775447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16219128580532858372135717 3041086608849910944775447)
                      ·
                        rfl

theorem cell23_5922495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_5922495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922495 prefixEnd_5922495 := by exact prefixLift 5922495
  have htrace : WordTrace (prefixWord ++ tailWord_5922495) baseStart_5922495 baseEnd_5922495 := by
    simpa [prefixWord, tailWord_5922495, baseEnd_5922495] using wordTrace_append hprefix tailTrace_5922495
  have hstable : (prefixWord ++ tailWord_5922495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922495).length < 2 ^ (prefixWord ++ tailWord_5922495).sum := by decide
  have hdescent : baseEnd_5922495 < baseStart_5922495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922509 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_5922509 : Nat := 118140960795 + 5922509 * 2 ^ 59
def prefixEnd_5922509 : Nat := 4983230072969 + 3 ^ 40 * 5922509 * 2
def baseEnd_5922509 : Nat := 1013697932526357963333461

theorem tailTrace_5922509 : CollatzResearch.WordTrace tailWord_5922509 prefixEnd_5922509 1013697932526357963333461 := by
  unfold tailWord_5922509
  simp only [CollatzResearch.WordTrace]
  refine ⟨216011649300768851853954581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144007766200512567902636387 216011649300768851853954581)
  ·
    refine ⟨10125546060973539930654121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 216011649300768851853954581 10125546060973539930654121)
    ·
      refine ⟨7594159545730154947990591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10125546060973539930654121 7594159545730154947990591)
      ·
        refine ⟨11391239318595232421985887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7594159545730154947990591 11391239318595232421985887)
        ·
          refine ⟨17086858977892848632978831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11391239318595232421985887 17086858977892848632978831)
          ·
            refine ⟨25630288466839272949468247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17086858977892848632978831 25630288466839272949468247)
            ·
              refine ⟨38445432700258909424202371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25630288466839272949468247 38445432700258909424202371)
              ·
                refine ⟨57668149050388364136303557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38445432700258909424202371 57668149050388364136303557)
                ·
                  refine ⟨10812777946947818275556917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57668149050388364136303557 10812777946947818275556917)
                  ·
                    refine ⟨1013697932526357963333461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10812777946947818275556917 1013697932526357963333461)
                    ·
                      rfl

theorem cell23_5922509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_5922509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922509 prefixEnd_5922509 := by exact prefixLift 5922509
  have htrace : WordTrace (prefixWord ++ tailWord_5922509) baseStart_5922509 baseEnd_5922509 := by
    simpa [prefixWord, tailWord_5922509, baseEnd_5922509] using wordTrace_append hprefix tailTrace_5922509
  have hstable : (prefixWord ++ tailWord_5922509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922509).length < 2 ^ (prefixWord ++ tailWord_5922509).sum := by decide
  have hdescent : baseEnd_5922509 < baseStart_5922509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922512 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 2, 4, 2]
def baseStart_5922512 : Nat := 118140960795 + 5922512 * 2 ^ 59
def prefixEnd_5922512 : Nat := 4983230072969 + 3 ^ 40 * 5922512 * 2
def baseEnd_5922512 : Nat := 3041095338021037378262869

theorem tailTrace_5922512 : CollatzResearch.WordTrace tailWord_5922512 prefixEnd_5922512 3041095338021037378262869 := by
  unfold tailWord_5922512
  simp only [CollatzResearch.WordTrace]
  refine ⟨108005879359878991683156895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144007839146505322244209193 108005879359878991683156895)
  ·
    refine ⟨162008819039818487524735343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108005879359878991683156895 162008819039818487524735343)
    ·
      refine ⟨243013228559727731287103015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162008819039818487524735343 243013228559727731287103015)
      ·
        refine ⟨364519842839591596930654523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243013228559727731287103015 364519842839591596930654523)
        ·
          refine ⟨546779764259387395395981785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364519842839591596930654523 546779764259387395395981785)
          ·
            refine ⟨410084823194540546546986339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546779764259387395395981785 410084823194540546546986339)
            ·
              refine ⟨615127234791810819820479509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410084823194540546546986339 615127234791810819820479509)
              ·
                refine ⟨28834089130866132179084977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 615127234791810819820479509 28834089130866132179084977)
                ·
                  refine ⟨21625566848149599134313733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28834089130866132179084977 21625566848149599134313733)
                  ·
                    refine ⟨4054793784028049837683825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21625566848149599134313733 4054793784028049837683825)
                    ·
                      refine ⟨3041095338021037378262869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4054793784028049837683825 3041095338021037378262869)
                      ·
                        rfl

theorem cell23_5922512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 4, 2].length) (baseStart_5922512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922512 prefixEnd_5922512 := by exact prefixLift 5922512
  have htrace : WordTrace (prefixWord ++ tailWord_5922512) baseStart_5922512 baseEnd_5922512 := by
    simpa [prefixWord, tailWord_5922512, baseEnd_5922512] using wordTrace_append hprefix tailTrace_5922512
  have hstable : (prefixWord ++ tailWord_5922512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922512).length < 2 ^ (prefixWord ++ tailWord_5922512).sum := by decide
  have hdescent : baseEnd_5922512 < baseStart_5922512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922532 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_5922532 : Nat := 118140960795 + 5922532 * 2 ^ 59
def prefixEnd_5922532 : Nat := 4983230072969 + 3 ^ 40 * 5922532 * 2
def baseEnd_5922532 : Nat := 3041105607634127300012777

theorem tailTrace_5922532 : CollatzResearch.WordTrace tailWord_5922532 prefixEnd_5922532 3041105607634127300012777 := by
  unfold tailWord_5922532
  simp only [CollatzResearch.WordTrace]
  refine ⟨108006244089842763391020925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144008325453123684521361233 108006244089842763391020925)
  ·
    refine ⟨40502341533691036271632847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108006244089842763391020925 40502341533691036271632847)
    ·
      refine ⟨60753512300536554407449271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40502341533691036271632847 60753512300536554407449271)
      ·
        refine ⟨91130268450804831611173907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60753512300536554407449271 91130268450804831611173907)
        ·
          refine ⟨136695402676207247416760861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91130268450804831611173907 136695402676207247416760861)
          ·
            refine ⟨51260776003577717781285323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136695402676207247416760861 51260776003577717781285323)
            ·
              refine ⟨76891164005366576671927985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51260776003577717781285323 76891164005366576671927985)
              ·
                refine ⟨57668373004024932503945989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76891164005366576671927985 57668373004024932503945989)
                ·
                  refine ⟨10812819938254674844489873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57668373004024932503945989 10812819938254674844489873)
                  ·
                    refine ⟨8109614953691006133367405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10812819938254674844489873 8109614953691006133367405)
                    ·
                      refine ⟨3041105607634127300012777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8109614953691006133367405 3041105607634127300012777)
                      ·
                        rfl

theorem cell23_5922532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_5922532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922532 prefixEnd_5922532 := by exact prefixLift 5922532
  have htrace : WordTrace (prefixWord ++ tailWord_5922532) baseStart_5922532 baseEnd_5922532 := by
    simpa [prefixWord, tailWord_5922532, baseEnd_5922532] using wordTrace_append hprefix tailTrace_5922532
  have hstable : (prefixWord ++ tailWord_5922532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922532).length < 2 ^ (prefixWord ++ tailWord_5922532).sum := by decide
  have hdescent : baseEnd_5922532 < baseStart_5922532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922580 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5922580 : Nat := 118140960795 + 5922580 * 2 ^ 59
def prefixEnd_5922580 : Nat := 4983230072969 + 3 ^ 40 * 5922580 * 2
def baseEnd_5922580 : Nat := 3041130254705543112212557

theorem tailTrace_5922580 : CollatzResearch.WordTrace tailWord_5922580 prefixEnd_5922580 3041130254705543112212557 := by
  unfold tailWord_5922580
  simp only [CollatzResearch.WordTrace]
  refine ⟨108007119441755815489894597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144009492589007753986526129 108007119441755815489894597)
  ·
    refine ⟨20251334895329215404355237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108007119441755815489894597 20251334895329215404355237)
    ·
      refine ⟨3797125292874227888316607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20251334895329215404355237 3797125292874227888316607)
      ·
        refine ⟨5695687939311341832474911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3797125292874227888316607 5695687939311341832474911)
        ·
          refine ⟨8543531908967012748712367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5695687939311341832474911 8543531908967012748712367)
          ·
            refine ⟨12815297863450519123068551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8543531908967012748712367 12815297863450519123068551)
            ·
              refine ⟨19222946795175778684602827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12815297863450519123068551 19222946795175778684602827)
              ·
                refine ⟨28834420192763668026904241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19222946795175778684602827 28834420192763668026904241)
                ·
                  refine ⟨21625815144572751020178181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28834420192763668026904241 21625815144572751020178181)
                  ·
                    refine ⟨4054840339607390816283409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21625815144572751020178181 4054840339607390816283409)
                    ·
                      refine ⟨3041130254705543112212557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4054840339607390816283409 3041130254705543112212557)
                      ·
                        rfl

theorem cell23_5922580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5922580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922580 prefixEnd_5922580 := by exact prefixLift 5922580
  have htrace : WordTrace (prefixWord ++ tailWord_5922580) baseStart_5922580 baseEnd_5922580 := by
    simpa [prefixWord, tailWord_5922580, baseEnd_5922580] using wordTrace_append hprefix tailTrace_5922580
  have hstable : (prefixWord ++ tailWord_5922580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922580).length < 2 ^ (prefixWord ++ tailWord_5922580).sum := by decide
  have hdescent : baseEnd_5922580 < baseStart_5922580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922596 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_5922596 : Nat := 118140960795 + 5922596 * 2 ^ 59
def prefixEnd_5922596 : Nat := 4983230072969 + 3 ^ 40 * 5922596 * 2
def baseEnd_5922596 : Nat := 3041138470396015049612483

theorem tailTrace_5922596 : CollatzResearch.WordTrace tailWord_5922596 prefixEnd_5922596 3041138470396015049612483 := by
  unfold tailWord_5922596
  simp only [CollatzResearch.WordTrace]
  refine ⟨108007411225726832856185821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144009881634302443808247761 108007411225726832856185821)
  ·
    refine ⟨40502779209647562321069683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108007411225726832856185821 40502779209647562321069683)
    ·
      refine ⟨60754168814471343481604525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40502779209647562321069683 60754168814471343481604525)
      ·
        refine ⟨22782813305426753805601697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60754168814471343481604525 22782813305426753805601697)
        ·
          refine ⟨17087109979070065354201273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22782813305426753805601697 17087109979070065354201273)
          ·
            refine ⟨12815332484302549015650955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17087109979070065354201273 12815332484302549015650955)
            ·
              refine ⟨19222998726453823523476433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12815332484302549015650955 19222998726453823523476433)
              ·
                refine ⟨14417249044840367642607325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19222998726453823523476433 14417249044840367642607325)
                ·
                  refine ⟨5406468391815137865977747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14417249044840367642607325 5406468391815137865977747)
                  ·
                    refine ⟨8109702587722706798966621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5406468391815137865977747 8109702587722706798966621)
                    ·
                      refine ⟨3041138470396015049612483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8109702587722706798966621 3041138470396015049612483)
                      ·
                        rfl

theorem cell23_5922596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_5922596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922596 prefixEnd_5922596 := by exact prefixLift 5922596
  have htrace : WordTrace (prefixWord ++ tailWord_5922596) baseStart_5922596 baseEnd_5922596 := by
    simpa [prefixWord, tailWord_5922596, baseEnd_5922596] using wordTrace_append hprefix tailTrace_5922596
  have hstable : (prefixWord ++ tailWord_5922596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922596).length < 2 ^ (prefixWord ++ tailWord_5922596).sum := by decide
  have hdescent : baseEnd_5922596 < baseStart_5922596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922616 : List Nat := [2, 1, 2, 1, 3, 5, 2, 1, 1, 5]
def baseStart_5922616 : Nat := 118140960795 + 5922616 * 2 ^ 59
def prefixEnd_5922616 : Nat := 4983230072969 + 3 ^ 40 * 5922616 * 2
def baseEnd_5922616 : Nat := 1013716246669701657120797

theorem tailTrace_5922616 : CollatzResearch.WordTrace tailWord_5922616 prefixEnd_5922616 1013716246669701657120797 := by
  unfold tailWord_5922616
  simp only [CollatzResearch.WordTrace]
  refine ⟨108007775955690604564049851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144010367940920806085399801 108007775955690604564049851)
  ·
    refine ⟨162011663933535906846074777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108007775955690604564049851 162011663933535906846074777)
    ·
      refine ⟨121508747950151930134556083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162011663933535906846074777 121508747950151930134556083)
      ·
        refine ⟨182263121925227895201834125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121508747950151930134556083 182263121925227895201834125)
        ·
          refine ⟨68348670721960460700687797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182263121925227895201834125 68348670721960460700687797)
          ·
            refine ⟨6407687880183793190689481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68348670721960460700687797 6407687880183793190689481)
            ·
              refine ⟨4805765910137844893017111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6407687880183793190689481 4805765910137844893017111)
              ·
                refine ⟨7208648865206767339525667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4805765910137844893017111 7208648865206767339525667)
                ·
                  refine ⟨10812973297810151009288501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7208648865206767339525667 10812973297810151009288501)
                  ·
                    refine ⟨1013716246669701657120797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10812973297810151009288501 1013716246669701657120797)
                    ·
                      rfl

theorem cell23_5922616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_5922616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922616 prefixEnd_5922616 := by exact prefixLift 5922616
  have htrace : WordTrace (prefixWord ++ tailWord_5922616) baseStart_5922616 baseEnd_5922616 := by
    simpa [prefixWord, tailWord_5922616, baseEnd_5922616] using wordTrace_append hprefix tailTrace_5922616
  have hstable : (prefixWord ++ tailWord_5922616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922616).length < 2 ^ (prefixWord ++ tailWord_5922616).sum := by decide
  have hdescent : baseEnd_5922616 < baseStart_5922616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922630 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_5922630 : Nat := 118140960795 + 5922630 * 2 ^ 59
def prefixEnd_5922630 : Nat := 4983230072969 + 3 ^ 40 * 5922630 * 2
def baseEnd_5922630 : Nat := 3041155928738267916587327

theorem tailTrace_5922630 : CollatzResearch.WordTrace tailWord_5922630 prefixEnd_5922630 3041155928738267916587327 := by
  unfold tailWord_5922630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6750501954166577797472167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 144010708355553659679406229 6750501954166577797472167)
  ·
    refine ⟨10125752931249866696208251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6750501954166577797472167 10125752931249866696208251)
    ·
      refine ⟨15188629396874800044312377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10125752931249866696208251 15188629396874800044312377)
      ·
        refine ⟨11391472047656100033234283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15188629396874800044312377 11391472047656100033234283)
        ·
          refine ⟨17087208071484150049851425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11391472047656100033234283 17087208071484150049851425)
          ·
            refine ⟨12815406053613112537388569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17087208071484150049851425 12815406053613112537388569)
            ·
              refine ⟨9611554540209834403041427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12815406053613112537388569 9611554540209834403041427)
              ·
                refine ⟨14417331810314751604562141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9611554540209834403041427 14417331810314751604562141)
                ·
                  refine ⟨5406499428868031851710803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14417331810314751604562141 5406499428868031851710803)
                  ·
                    refine ⟨8109749143302047777566205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5406499428868031851710803 8109749143302047777566205)
                    ·
                      refine ⟨3041155928738267916587327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8109749143302047777566205 3041155928738267916587327)
                      ·
                        rfl

theorem cell23_5922630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_5922630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922630 prefixEnd_5922630 := by exact prefixLift 5922630
  have htrace : WordTrace (prefixWord ++ tailWord_5922630) baseStart_5922630 baseEnd_5922630 := by
    simpa [prefixWord, tailWord_5922630, baseEnd_5922630] using wordTrace_append hprefix tailTrace_5922630
  have hstable : (prefixWord ++ tailWord_5922630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922630).length < 2 ^ (prefixWord ++ tailWord_5922630).sum := by decide
  have hdescent : baseEnd_5922630 < baseStart_5922630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922656 : List Nat := [2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 3]
def baseStart_5922656 : Nat := 118140960795 + 5922656 * 2 ^ 59
def prefixEnd_5922656 : Nat := 4983230072969 + 3 ^ 40 * 5922656 * 2
def baseEnd_5922656 : Nat := 3041169279235284814862207

theorem tailTrace_5922656 : CollatzResearch.WordTrace tailWord_5922656 prefixEnd_5922656 3041169279235284814862207 := by
  unfold tailWord_5922656
  simp only [CollatzResearch.WordTrace]
  refine ⟨108008505415618147979777911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144011340554157530639703881 108008505415618147979777911)
  ·
    refine ⟨162012758123427221969666867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108008505415618147979777911 162012758123427221969666867)
    ·
      refine ⟨243019137185140832954500301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162012758123427221969666867 243019137185140832954500301)
      ·
        refine ⟨91132176444427812357937613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243019137185140832954500301 91132176444427812357937613)
        ·
          refine ⟨34174566166660429634226605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91132176444427812357937613 34174566166660429634226605)
          ·
            refine ⟨12815462312497661112834977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34174566166660429634226605 12815462312497661112834977)
            ·
              refine ⟨9611596734373245834626233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12815462312497661112834977 9611596734373245834626233)
              ·
                refine ⟨7208697550779934375969675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9611596734373245834626233 7208697550779934375969675)
                ·
                  refine ⟨10813046326169901563954513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7208697550779934375969675 10813046326169901563954513)
                  ·
                    refine ⟨8109784744627426172965885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10813046326169901563954513 8109784744627426172965885)
                    ·
                      refine ⟨3041169279235284814862207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8109784744627426172965885 3041169279235284814862207)
                      ·
                        rfl

theorem cell23_5922656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_5922656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922656 prefixEnd_5922656 := by exact prefixLift 5922656
  have htrace : WordTrace (prefixWord ++ tailWord_5922656) baseStart_5922656 baseEnd_5922656 := by
    simpa [prefixWord, tailWord_5922656, baseEnd_5922656] using wordTrace_append hprefix tailTrace_5922656
  have hstable : (prefixWord ++ tailWord_5922656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922656).length < 2 ^ (prefixWord ++ tailWord_5922656).sum := by decide
  have hdescent : baseEnd_5922656 < baseStart_5922656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922669 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_5922669 : Nat := 118140960795 + 5922669 * 2 ^ 59
def prefixEnd_5922669 : Nat := 4983230072969 + 3 ^ 40 * 5922669 * 2
def baseEnd_5922669 : Nat := 3041175954483793263999647

theorem tailTrace_5922669 : CollatzResearch.WordTrace tailWord_5922669 prefixEnd_5922669 3041175954483793263999647 := by
  unfold tailWord_5922669
  simp only [CollatzResearch.WordTrace]
  refine ⟨216017484980189199179779061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144011656653459466119852707 216017484980189199179779061)
  ·
    refine ⟨20251639216892737423104287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 216017484980189199179779061 20251639216892737423104287)
    ·
      refine ⟨30377458825339106134656431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20251639216892737423104287 30377458825339106134656431)
      ·
        refine ⟨45566188238008659201984647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30377458825339106134656431 45566188238008659201984647)
        ·
          refine ⟨68349282357012988802976971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45566188238008659201984647 68349282357012988802976971)
          ·
            refine ⟨102523923535519483204465457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68349282357012988802976971 102523923535519483204465457)
            ·
              refine ⟨76892942651639612403349093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102523923535519483204465457 76892942651639612403349093)
              ·
                refine ⟨14417426747182427325627955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76892942651639612403349093 14417426747182427325627955)
                ·
                  refine ⟨21626140120773640988441933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14417426747182427325627955 21626140120773640988441933)
                  ·
                    refine ⟨8109802545290115370665725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21626140120773640988441933 8109802545290115370665725)
                    ·
                      refine ⟨3041175954483793263999647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8109802545290115370665725 3041175954483793263999647)
                      ·
                        rfl

theorem cell23_5922669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_5922669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922669 prefixEnd_5922669 := by exact prefixLift 5922669
  have htrace : WordTrace (prefixWord ++ tailWord_5922669) baseStart_5922669 baseEnd_5922669 := by
    simpa [prefixWord, tailWord_5922669, baseEnd_5922669] using wordTrace_append hprefix tailTrace_5922669
  have hstable : (prefixWord ++ tailWord_5922669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922669).length < 2 ^ (prefixWord ++ tailWord_5922669).sum := by decide
  have hdescent : baseEnd_5922669 < baseStart_5922669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922679 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 7, 3, 2]
def baseStart_5922679 : Nat := 118140960795 + 5922679 * 2 ^ 59
def prefixEnd_5922679 : Nat := 4983230072969 + 3 ^ 40 * 5922679 * 2
def baseEnd_5922679 : Nat := 3041181089290338224874601

theorem tailTrace_5922679 : CollatzResearch.WordTrace tailWord_5922679 prefixEnd_5922679 3041181089290338224874601 := by
  unfold tailWord_5922679
  simp only [CollatzResearch.WordTrace]
  refine ⟨216017849710152970887643091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144011899806768647258428727 216017849710152970887643091)
  ·
    refine ⟨324026774565229456331464637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216017849710152970887643091 324026774565229456331464637)
    ·
      refine ⟨121510040461961046124299239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324026774565229456331464637 121510040461961046124299239)
      ·
        refine ⟨182265060692941569186448859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121510040461961046124299239 182265060692941569186448859)
        ·
          refine ⟨273397591039412353779673289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182265060692941569186448859 273397591039412353779673289)
          ·
            refine ⟨205048193279559265334754967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273397591039412353779673289 205048193279559265334754967)
            ·
              refine ⟨307572289919338898002132451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205048193279559265334754967 307572289919338898002132451)
              ·
                refine ⟨461358434879008347003198677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307572289919338898002132451 461358434879008347003198677)
                ·
                  refine ⟨10813088317476758132887469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 461358434879008347003198677 10813088317476758132887469)
                  ·
                    refine ⟨4054908119053784299832801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10813088317476758132887469 4054908119053784299832801)
                    ·
                      refine ⟨3041181089290338224874601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4054908119053784299832801 3041181089290338224874601)
                      ·
                        rfl

theorem cell23_5922679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 3, 2].length) (baseStart_5922679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922679 prefixEnd_5922679 := by exact prefixLift 5922679
  have htrace : WordTrace (prefixWord ++ tailWord_5922679) baseStart_5922679 baseEnd_5922679 := by
    simpa [prefixWord, tailWord_5922679, baseEnd_5922679] using wordTrace_append hprefix tailTrace_5922679
  have hstable : (prefixWord ++ tailWord_5922679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922679).length < 2 ^ (prefixWord ++ tailWord_5922679).sum := by decide
  have hdescent : baseEnd_5922679 < baseStart_5922679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922799 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 4]
def baseStart_5922799 : Nat := 118140960795 + 5922799 * 2 ^ 59
def prefixEnd_5922799 : Nat := 4983230072969 + 3 ^ 40 * 5922799 * 2
def baseEnd_5922799 : Nat := 3041242706968877755374049

theorem tailTrace_5922799 : CollatzResearch.WordTrace tailWord_5922799 prefixEnd_5922799 3041242706968877755374049 := by
  unfold tailWord_5922799
  simp only [CollatzResearch.WordTrace]
  refine ⟨216022226469718231382011451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144014817646478820921340967 216022226469718231382011451)
  ·
    refine ⟨324033339704577347073017177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216022226469718231382011451 324033339704577347073017177)
    ·
      refine ⟨243025004778433010304762883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324033339704577347073017177 243025004778433010304762883)
      ·
        refine ⟨364537507167649515457144325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243025004778433010304762883 364537507167649515457144325)
        ·
          refine ⟨68350782593934284148214561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 364537507167649515457144325 68350782593934284148214561)
          ·
            refine ⟨51263086945450713111160921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68350782593934284148214561 51263086945450713111160921)
            ·
              refine ⟨38447315209088034833370691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51263086945450713111160921 38447315209088034833370691)
              ·
                refine ⟨57670972813632052250056037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38447315209088034833370691 57670972813632052250056037)
                ·
                  refine ⟨10813307402556009796885507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57670972813632052250056037 10813307402556009796885507)
                  ·
                    refine ⟨16219961103834014695328261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10813307402556009796885507 16219961103834014695328261)
                    ·
                      refine ⟨3041242706968877755374049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16219961103834014695328261 3041242706968877755374049)
                      ·
                        rfl

theorem cell23_5922799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_5922799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922799 prefixEnd_5922799 := by exact prefixLift 5922799
  have htrace : WordTrace (prefixWord ++ tailWord_5922799) baseStart_5922799 baseEnd_5922799 := by
    simpa [prefixWord, tailWord_5922799, baseEnd_5922799] using wordTrace_append hprefix tailTrace_5922799
  have hstable : (prefixWord ++ tailWord_5922799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922799).length < 2 ^ (prefixWord ++ tailWord_5922799).sum := by decide
  have hdescent : baseEnd_5922799 < baseStart_5922799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922900 : List Nat := [2, 4, 1, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_5922900 : Nat := 118140960795 + 5922900 * 2 ^ 59
def prefixEnd_5922900 : Nat := 4983230072969 + 3 ^ 40 * 5922900 * 2
def baseEnd_5922900 : Nat := 3041294568514981860211085

theorem tailTrace_5922900 : CollatzResearch.WordTrace tailWord_5922900 prefixEnd_5922900 3041294568514981860211085 := by
  unfold tailWord_5922900
  simp only [CollatzResearch.WordTrace]
  refine ⟨108012955121176162815719077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144017273494901550420958769 108012955121176162815719077)
  ·
    refine ⟨20252429085220530527947327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108012955121176162815719077 20252429085220530527947327)
    ·
      refine ⟨30378643627830795791920991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20252429085220530527947327 30378643627830795791920991)
      ·
        refine ⟨45567965441746193687881487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30378643627830795791920991 45567965441746193687881487)
        ·
          refine ⟨68351948162619290531822231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45567965441746193687881487 68351948162619290531822231)
          ·
            refine ⟨102527922243928935797733347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68351948162619290531822231 102527922243928935797733347)
            ·
              refine ⟨153791883365893403696600021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102527922243928935797733347 153791883365893403696600021)
              ·
                refine ⟨3604497266388126649139063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 153791883365893403696600021 3604497266388126649139063)
                ·
                  refine ⟨5406745899582189973708595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604497266388126649139063 5406745899582189973708595)
                  ·
                    refine ⟨8110118849373284960562893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5406745899582189973708595 8110118849373284960562893)
                    ·
                      refine ⟨3041294568514981860211085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8110118849373284960562893 3041294568514981860211085)
                      ·
                        rfl

theorem cell23_5922900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_5922900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922900 prefixEnd_5922900 := by exact prefixLift 5922900
  have htrace : WordTrace (prefixWord ++ tailWord_5922900) baseStart_5922900 baseEnd_5922900 := by
    simpa [prefixWord, tailWord_5922900, baseEnd_5922900] using wordTrace_append hprefix tailTrace_5922900
  have hstable : (prefixWord ++ tailWord_5922900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922900).length < 2 ^ (prefixWord ++ tailWord_5922900).sum := by decide
  have hdescent : baseEnd_5922900 < baseStart_5922900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922916 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_5922916 : Nat := 118140960795 + 5922916 * 2 ^ 59
def prefixEnd_5922916 : Nat := 4983230072969 + 3 ^ 40 * 5922916 * 2
def baseEnd_5922916 : Nat := 1013767594735151265870337

theorem tailTrace_5922916 : CollatzResearch.WordTrace tailWord_5922916 prefixEnd_5922916 1013767594735151265870337 := by
  unfold tailWord_5922916
  simp only [CollatzResearch.WordTrace]
  refine ⟨108013246905147180182010301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144017662540196240242680401 108013246905147180182010301)
  ·
    refine ⟨40504967589430192568253863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108013246905147180182010301 40504967589430192568253863)
    ·
      refine ⟨60757451384145288852380795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40504967589430192568253863 60757451384145288852380795)
      ·
        refine ⟨91136177076217933278571193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60757451384145288852380795 91136177076217933278571193)
        ·
          refine ⟨68352132807163449958928395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91136177076217933278571193 68352132807163449958928395)
          ·
            refine ⟨102528199210745174938392593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68352132807163449958928395 102528199210745174938392593)
            ·
              refine ⟨76896149408058881203794445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102528199210745174938392593 76896149408058881203794445)
              ·
                refine ⟨28836056028022080451422917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76896149408058881203794445 28836056028022080451422917)
                ·
                  refine ⟨5406760505254140084641797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28836056028022080451422917 5406760505254140084641797)
                  ·
                    refine ⟨1013767594735151265870337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5406760505254140084641797 1013767594735151265870337)
                    ·
                      rfl

theorem cell23_5922916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_5922916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922916 prefixEnd_5922916 := by exact prefixLift 5922916
  have htrace : WordTrace (prefixWord ++ tailWord_5922916) baseStart_5922916 baseEnd_5922916 := by
    simpa [prefixWord, tailWord_5922916, baseEnd_5922916] using wordTrace_append hprefix tailTrace_5922916
  have hstable : (prefixWord ++ tailWord_5922916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922916).length < 2 ^ (prefixWord ++ tailWord_5922916).sum := by decide
  have hdescent : baseEnd_5922916 < baseStart_5922916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922917 : List Nat := [1, 3, 1, 3, 2, 2, 4, 2, 1, 1, 3]
def baseStart_5922917 : Nat := 118140960795 + 5922917 * 2 ^ 59
def prefixEnd_5922917 : Nat := 4983230072969 + 3 ^ 40 * 5922917 * 2
def baseEnd_5922917 : Nat := 3041303297686108293698507

theorem tailTrace_5922917 : CollatzResearch.WordTrace tailWord_5922917 prefixEnd_5922917 3041303297686108293698507 := by
  unfold tailWord_5922917
  simp only [CollatzResearch.WordTrace]
  refine ⟨216026530283290737534807005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144017686855527158356538003 216026530283290737534807005)
  ·
    refine ⟨81009948856234026575552627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216026530283290737534807005 81009948856234026575552627)
    ·
      refine ⟨121514923284351039863328941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81009948856234026575552627 121514923284351039863328941)
      ·
        refine ⟨45568096231631639948748353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121514923284351039863328941 45568096231631639948748353)
        ·
          refine ⟨34176072173723729961561265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45568096231631639948748353 34176072173723729961561265)
          ·
            refine ⟨25632054130292797471170949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34176072173723729961561265 25632054130292797471170949)
            ·
              refine ⟨4806010149429899525844553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25632054130292797471170949 4806010149429899525844553)
              ·
                refine ⟨3604507612072424644383415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4806010149429899525844553 3604507612072424644383415)
                ·
                  refine ⟨5406761418108636966575123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604507612072424644383415 5406761418108636966575123)
                  ·
                    refine ⟨8110142127162955449862685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5406761418108636966575123 8110142127162955449862685)
                    ·
                      refine ⟨3041303297686108293698507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8110142127162955449862685 3041303297686108293698507)
                      ·
                        rfl

theorem cell23_5922917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_5922917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922917 prefixEnd_5922917 := by exact prefixLift 5922917
  have htrace : WordTrace (prefixWord ++ tailWord_5922917) baseStart_5922917 baseEnd_5922917 := by
    simpa [prefixWord, tailWord_5922917, baseEnd_5922917] using wordTrace_append hprefix tailTrace_5922917
  have hstable : (prefixWord ++ tailWord_5922917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922917).length < 2 ^ (prefixWord ++ tailWord_5922917).sum := by decide
  have hdescent : baseEnd_5922917 < baseStart_5922917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922926 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_5922926 : Nat := 118140960795 + 5922926 * 2 ^ 59
def prefixEnd_5922926 : Nat := 4983230072969 + 3 ^ 40 * 5922926 * 2
def baseEnd_5922926 : Nat := 3041307919011998758485965

theorem tailTrace_5922926 : CollatzResearch.WordTrace tailWord_5922926 prefixEnd_5922926 3041307919011998758485965 := by
  unfold tailWord_5922926
  simp only [CollatzResearch.WordTrace]
  refine ⟨27003357317532266508985579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144017905693505421381256421 27003357317532266508985579)
  ·
    refine ⟨40505035976298399763478369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27003357317532266508985579 40505035976298399763478369)
    ·
      refine ⟨30378776982223799822608777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40505035976298399763478369 30378776982223799822608777)
      ·
        refine ⟨22784082736667849866956583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30378776982223799822608777 22784082736667849866956583)
        ·
          refine ⟨34176124105001774800434875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22784082736667849866956583 34176124105001774800434875)
          ·
            refine ⟨51264186157502662200652313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34176124105001774800434875 51264186157502662200652313)
            ·
              refine ⟨38448139618126996650489235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51264186157502662200652313 38448139618126996650489235)
              ·
                refine ⟨57672209427190494975733853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38448139618126996650489235 57672209427190494975733853)
                ·
                  refine ⟨21627078535196435615900195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57672209427190494975733853 21627078535196435615900195)
                  ·
                    refine ⟨32440617802794653423850293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21627078535196435615900195 32440617802794653423850293)
                    ·
                      refine ⟨3041307919011998758485965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32440617802794653423850293 3041307919011998758485965)
                      ·
                        rfl

theorem cell23_5922926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_5922926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922926 prefixEnd_5922926 := by exact prefixLift 5922926
  have htrace : WordTrace (prefixWord ++ tailWord_5922926) baseStart_5922926 baseEnd_5922926 := by
    simpa [prefixWord, tailWord_5922926, baseEnd_5922926] using wordTrace_append hprefix tailTrace_5922926
  have hstable : (prefixWord ++ tailWord_5922926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922926).length < 2 ^ (prefixWord ++ tailWord_5922926).sum := by decide
  have hdescent : baseEnd_5922926 < baseStart_5922926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922940 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 3, 2, 2]
def baseStart_5922940 : Nat := 118140960795 + 5922940 * 2 ^ 59
def prefixEnd_5922940 : Nat := 4983230072969 + 3 ^ 40 * 5922940 * 2
def baseEnd_5922940 : Nat := 3041315107741161703710901

theorem tailTrace_5922940 : CollatzResearch.WordTrace tailWord_5922940 prefixEnd_5922940 3041315107741161703710901 := by
  unfold tailWord_5922940
  simp only [CollatzResearch.WordTrace]
  refine ⟨108013684581103706231447137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144018246108138274975262849 108013684581103706231447137)
  ·
    refine ⟨81010263435827779673585353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108013684581103706231447137 81010263435827779673585353)
    ·
      refine ⟨60757697576870834755189015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81010263435827779673585353 60757697576870834755189015)
      ·
        refine ⟨91136546365306252132783523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60757697576870834755189015 91136546365306252132783523)
        ·
          refine ⟨136704819547959378199175285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91136546365306252132783523 136704819547959378199175285)
          ·
            refine ⟨12816076832621191706172683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136704819547959378199175285 12816076832621191706172683)
            ·
              refine ⟨19224115248931787559259025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12816076832621191706172683 19224115248931787559259025)
              ·
                refine ⟨14418086436698840669444269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19224115248931787559259025 14418086436698840669444269)
                ·
                  refine ⟨5406782413762065251041601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14418086436698840669444269 5406782413762065251041601)
                  ·
                    refine ⟨4055086810321548938281201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5406782413762065251041601 4055086810321548938281201)
                    ·
                      refine ⟨3041315107741161703710901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055086810321548938281201 3041315107741161703710901)
                      ·
                        rfl

theorem cell23_5922940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_5922940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922940 prefixEnd_5922940 := by exact prefixLift 5922940
  have htrace : WordTrace (prefixWord ++ tailWord_5922940) baseStart_5922940 baseEnd_5922940 := by
    simpa [prefixWord, tailWord_5922940, baseEnd_5922940] using wordTrace_append hprefix tailTrace_5922940
  have hstable : (prefixWord ++ tailWord_5922940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922940).length < 2 ^ (prefixWord ++ tailWord_5922940).sum := by decide
  have hdescent : baseEnd_5922940 < baseStart_5922940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922967 : List Nat := [1, 1, 3, 3, 5, 1, 1, 2, 2, 4]
def baseStart_5922967 : Nat := 118140960795 + 5922967 * 2 ^ 59
def prefixEnd_5922967 : Nat := 4983230072969 + 3 ^ 40 * 5922967 * 2
def baseEnd_5922967 : Nat := 1013776323906277699357759

theorem tailTrace_5922967 : CollatzResearch.WordTrace tailWord_5922967 prefixEnd_5922967 1013776323906277699357759 := by
  unfold tailWord_5922967
  simp only [CollatzResearch.WordTrace]
  refine ⟨216028353933109596074127155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144018902622073064049418103 216028353933109596074127155)
  ·
    refine ⟨324042530899664394111190733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216028353933109596074127155 324042530899664394111190733)
    ·
      refine ⟨121515949087374147791696525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324042530899664394111190733 121515949087374147791696525)
      ·
        refine ⟨45568480907765305421886197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121515949087374147791696525 45568480907765305421886197)
        ·
          refine ⟨4272045085102997383301831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45568480907765305421886197 4272045085102997383301831)
          ·
            refine ⟨6408067627654496074952747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272045085102997383301831 6408067627654496074952747)
            ·
              refine ⟨9612101441481744112429121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6408067627654496074952747 9612101441481744112429121)
              ·
                refine ⟨7209076081111308084321841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9612101441481744112429121 7209076081111308084321841)
                ·
                  refine ⟨5406807060833481063241381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7209076081111308084321841 5406807060833481063241381)
                  ·
                    refine ⟨1013776323906277699357759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5406807060833481063241381 1013776323906277699357759)
                    ·
                      rfl

theorem cell23_5922967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_5922967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922967 prefixEnd_5922967 := by exact prefixLift 5922967
  have htrace : WordTrace (prefixWord ++ tailWord_5922967) baseStart_5922967 baseEnd_5922967 := by
    simpa [prefixWord, tailWord_5922967, baseEnd_5922967] using wordTrace_append hprefix tailTrace_5922967
  have hstable : (prefixWord ++ tailWord_5922967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922967).length < 2 ^ (prefixWord ++ tailWord_5922967).sum := by decide
  have hdescent : baseEnd_5922967 < baseStart_5922967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922974 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_5922974 : Nat := 118140960795 + 5922974 * 2 ^ 59
def prefixEnd_5922974 : Nat := 4983230072969 + 3 ^ 40 * 5922974 * 2
def baseEnd_5922974 : Nat := 3041332566083414570685745

theorem tailTrace_5922974 : CollatzResearch.WordTrace tailWord_5922974 prefixEnd_5922974 3041332566083414570685745 := by
  unfold tailWord_5922974
  simp only [CollatzResearch.WordTrace]
  refine ⟨27003576155510529533703997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144019072829389490846421317 27003576155510529533703997)
  ·
    refine ⟨10126341058316448575138999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27003576155510529533703997 10126341058316448575138999)
    ·
      refine ⟨15189511587474672862708499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10126341058316448575138999 15189511587474672862708499)
      ·
        refine ⟨22784267381212009294062749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15189511587474672862708499 22784267381212009294062749)
        ·
          refine ⟨8544100267954503485273531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22784267381212009294062749 8544100267954503485273531)
          ·
            refine ⟨12816150401931755227910297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8544100267954503485273531 12816150401931755227910297)
            ·
              refine ⟨9612112801448816420932723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12816150401931755227910297 9612112801448816420932723)
              ·
                refine ⟨14418169202173224631399085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9612112801448816420932723 14418169202173224631399085)
                ·
                  refine ⟨5406813450814959236774657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14418169202173224631399085 5406813450814959236774657)
                  ·
                    refine ⟨4055110088111219427580993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5406813450814959236774657 4055110088111219427580993)
                    ·
                      refine ⟨3041332566083414570685745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055110088111219427580993 3041332566083414570685745)
                      ·
                        rfl

theorem cell23_5922974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_5922974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922974 prefixEnd_5922974 := by exact prefixLift 5922974
  have htrace : WordTrace (prefixWord ++ tailWord_5922974) baseStart_5922974 baseEnd_5922974 := by
    simpa [prefixWord, tailWord_5922974, baseEnd_5922974] using wordTrace_append hprefix tailTrace_5922974
  have hstable : (prefixWord ++ tailWord_5922974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922974).length < 2 ^ (prefixWord ++ tailWord_5922974).sum := by decide
  have hdescent : baseEnd_5922974 < baseStart_5922974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5922997 : List Nat := [1, 3, 3, 4, 2, 1, 2, 7]
def baseStart_5922997 : Nat := 118140960795 + 5922997 * 2 ^ 59
def prefixEnd_5922997 : Nat := 4983230072969 + 3 ^ 40 * 5922997 * 2
def baseEnd_5922997 : Nat := 112642384301424740025857

theorem tailTrace_5922997 : CollatzResearch.WordTrace tailWord_5922997 prefixEnd_5922997 112642384301424740025857 := by
  unfold tailWord_5922997
  simp only [CollatzResearch.WordTrace]
  refine ⟨216029448123000911197719245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144019632082000607465146163 216029448123000911197719245)
  ·
    refine ⟨81011043046125341699144717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216029448123000911197719245 81011043046125341699144717)
    ·
      refine ⟨30379141142297003137179269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81011043046125341699144717 30379141142297003137179269)
      ·
        refine ⟨5696088964180688088221113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30379141142297003137179269 5696088964180688088221113)
        ·
          refine ⟨4272066723135516066165835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5696088964180688088221113 4272066723135516066165835)
          ·
            refine ⟨6408100084703274099248753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272066723135516066165835 6408100084703274099248753)
            ·
              refine ⟨4806075063527455574436565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6408100084703274099248753 4806075063527455574436565)
              ·
                refine ⟨112642384301424740025857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4806075063527455574436565 112642384301424740025857)
                ·
                  rfl

theorem cell23_5922997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 7].length) (baseStart_5922997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922997 prefixEnd_5922997 := by exact prefixLift 5922997
  have htrace : WordTrace (prefixWord ++ tailWord_5922997) baseStart_5922997 baseEnd_5922997 := by
    simpa [prefixWord, tailWord_5922997, baseEnd_5922997] using wordTrace_append hprefix tailTrace_5922997
  have hstable : (prefixWord ++ tailWord_5922997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922997).length < 2 ^ (prefixWord ++ tailWord_5922997).sum := by decide
  have hdescent : baseEnd_5922997 < baseStart_5922997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923000 : List Nat := [2, 1, 2, 1, 2, 1, 6, 2, 1, 3, 2]
def baseStart_5923000 : Nat := 118140960795 + 5923000 * 2 ^ 59
def prefixEnd_5923000 : Nat := 4983230072969 + 3 ^ 40 * 5923000 * 2
def baseEnd_5923000 : Nat := 3041345916580431468960625

theorem tailTrace_5923000 : CollatzResearch.WordTrace tailWord_5923000 prefixEnd_5923000 3041345916580431468960625 := by
  unfold tailWord_5923000
  simp only [CollatzResearch.WordTrace]
  refine ⟨108014778770995021355039227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144019705027993361806718969 108014778770995021355039227)
  ·
    refine ⟨162022168156492532032558841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108014778770995021355039227 162022168156492532032558841)
    ·
      refine ⟨121516626117369399024419131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162022168156492532032558841 121516626117369399024419131)
      ·
        refine ⟨182274939176054098536628697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121516626117369399024419131 182274939176054098536628697)
        ·
          refine ⟨136706204382040573902471523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182274939176054098536628697 136706204382040573902471523)
          ·
            refine ⟨205059306573060860853707285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136706204382040573902471523 205059306573060860853707285)
            ·
              refine ⟨9612154995612227852517529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205059306573060860853707285 9612154995612227852517529)
              ·
                refine ⟨7209116246709170889388147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9612154995612227852517529 7209116246709170889388147)
                ·
                  refine ⟨10813674370063756334082221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7209116246709170889388147 10813674370063756334082221)
                  ·
                    refine ⟨4055127888773908625280833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10813674370063756334082221 4055127888773908625280833)
                    ·
                      refine ⟨3041345916580431468960625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055127888773908625280833 3041345916580431468960625)
                      ·
                        rfl

theorem cell23_5923000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 1, 3, 2].length) (baseStart_5923000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923000 prefixEnd_5923000 := by exact prefixLift 5923000
  have htrace : WordTrace (prefixWord ++ tailWord_5923000) baseStart_5923000 baseEnd_5923000 := by
    simpa [prefixWord, tailWord_5923000, baseEnd_5923000] using wordTrace_append hprefix tailTrace_5923000
  have hstable : (prefixWord ++ tailWord_5923000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923000).length < 2 ^ (prefixWord ++ tailWord_5923000).sum := by decide
  have hdescent : baseEnd_5923000 < baseStart_5923000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923013 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 1, 4, 2]
def baseStart_5923013 : Nat := 118140960795 + 5923013 * 2 ^ 59
def prefixEnd_5923013 : Nat := 4983230072969 + 3 ^ 40 * 5923013 * 2
def baseEnd_5923013 : Nat := 3041352591828939918098065

theorem tailTrace_5923013 : CollatzResearch.WordTrace tailWord_5923013 prefixEnd_5923013 3041352591828939918098065 := by
  unfold tailWord_5923013
  simp only [CollatzResearch.WordTrace]
  refine ⟨216030031690942945930301693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144020021127295297286867795 216030031690942945930301693)
  ·
    refine ⟨81011261884103604723863135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216030031690942945930301693 81011261884103604723863135)
    ·
      refine ⟨121516892826155407085794703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81011261884103604723863135 121516892826155407085794703)
      ·
        refine ⟨182275339239233110628692055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121516892826155407085794703 182275339239233110628692055)
        ·
          refine ⟨273413008858849665943038083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182275339239233110628692055 273413008858849665943038083)
          ·
            refine ⟨410119513288274498914557125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273413008858849665943038083 410119513288274498914557125)
            ·
              refine ⟨76897408741551468546479461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 410119513288274498914557125 76897408741551468546479461)
              ·
                refine ⟨14418264139040900352464899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76897408741551468546479461 14418264139040900352464899)
                ·
                  refine ⟨21627396208561350528697349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14418264139040900352464899 21627396208561350528697349)
                  ·
                    refine ⟨4055136789105253224130753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21627396208561350528697349 4055136789105253224130753)
                    ·
                      refine ⟨3041352591828939918098065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055136789105253224130753 3041352591828939918098065)
                      ·
                        rfl

theorem cell23_5923013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 4, 2].length) (baseStart_5923013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923013 prefixEnd_5923013 := by exact prefixLift 5923013
  have htrace : WordTrace (prefixWord ++ tailWord_5923013) baseStart_5923013 baseEnd_5923013 := by
    simpa [prefixWord, tailWord_5923013, baseEnd_5923013] using wordTrace_append hprefix tailTrace_5923013
  have hstable : (prefixWord ++ tailWord_5923013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923013).length < 2 ^ (prefixWord ++ tailWord_5923013).sum := by decide
  have hdescent : baseEnd_5923013 < baseStart_5923013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923016 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_5923016 : Nat := 118140960795 + 5923016 * 2 ^ 59
def prefixEnd_5923016 : Nat := 4983230072969 + 3 ^ 40 * 5923016 * 2
def baseEnd_5923016 : Nat := 3041354132270903406360551

theorem tailTrace_5923016 : CollatzResearch.WordTrace tailWord_5923016 prefixEnd_5923016 3041354132270903406360551 := by
  unfold tailWord_5923016
  simp only [CollatzResearch.WordTrace]
  refine ⟨108015070554966038721330451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144020094073288051628440601 108015070554966038721330451)
  ·
    refine ⟨162022605832449058081995677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108015070554966038721330451 162022605832449058081995677)
    ·
      refine ⟨60758477187168396780748379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162022605832449058081995677 60758477187168396780748379)
      ·
        refine ⟨91137715780752595171122569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60758477187168396780748379 91137715780752595171122569)
        ·
          refine ⟨68353286835564446378341927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91137715780752595171122569 68353286835564446378341927)
          ·
            refine ⟨102529930253346669567512891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68353286835564446378341927 102529930253346669567512891)
            ·
              refine ⟨153794895380020004351269337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102529930253346669567512891 153794895380020004351269337)
              ·
                refine ⟨115346171535015003263452003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153794895380020004351269337 115346171535015003263452003)
                ·
                  refine ⟨173019257302522504895178005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115346171535015003263452003 173019257302522504895178005)
                  ·
                    refine ⟨8110277686055742416961469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 173019257302522504895178005 8110277686055742416961469)
                    ·
                      refine ⟨3041354132270903406360551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8110277686055742416961469 3041354132270903406360551)
                      ·
                        rfl

theorem cell23_5923016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_5923016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923016 prefixEnd_5923016 := by exact prefixLift 5923016
  have htrace : WordTrace (prefixWord ++ tailWord_5923016) baseStart_5923016 baseEnd_5923016 := by
    simpa [prefixWord, tailWord_5923016, baseEnd_5923016] using wordTrace_append hprefix tailTrace_5923016
  have hstable : (prefixWord ++ tailWord_5923016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923016).length < 2 ^ (prefixWord ++ tailWord_5923016).sum := by decide
  have hdescent : baseEnd_5923016 < baseStart_5923016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923070 : List Nat := [4, 2, 2, 1, 1, 1, 2, 5, 5]
def baseStart_5923070 : Nat := 118140960795 + 5923070 * 2 ^ 59
def prefixEnd_5923070 : Nat := 4983230072969 + 3 ^ 40 * 5923070 * 2
def baseEnd_5923070 : Nat := 337931317802916243898367

theorem tailTrace_5923070 : CollatzResearch.WordTrace tailWord_5923070 prefixEnd_5923070 337931317802916243898367 := by
  unfold tailWord_5923070
  simp only [CollatzResearch.WordTrace]
  refine ⟨27004013831467055583140833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144021407101157629776751109 27004013831467055583140833)
  ·
    refine ⟨20253010373600291687355625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27004013831467055583140833 20253010373600291687355625)
    ·
      refine ⟨15189757780200218765516719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20253010373600291687355625 15189757780200218765516719)
      ·
        refine ⟨22784636670300328148275079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15189757780200218765516719 22784636670300328148275079)
        ·
          refine ⟨34176955005450492222412619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22784636670300328148275079 34176955005450492222412619)
          ·
            refine ⟨51265432508175738333618929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34176955005450492222412619 51265432508175738333618929)
            ·
              refine ⟨38449074381131803750214197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51265432508175738333618929 38449074381131803750214197)
              ·
                refine ⟨3604600723231106601582581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38449074381131803750214197 3604600723231106601582581)
                ·
                  refine ⟨337931317802916243898367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3604600723231106601582581 337931317802916243898367)
                  ·
                    rfl

theorem cell23_5923070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_5923070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923070 prefixEnd_5923070 := by exact prefixLift 5923070
  have htrace : WordTrace (prefixWord ++ tailWord_5923070) baseStart_5923070 baseEnd_5923070 := by
    simpa [prefixWord, tailWord_5923070, baseEnd_5923070] using wordTrace_append hprefix tailTrace_5923070
  have hstable : (prefixWord ++ tailWord_5923070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923070).length < 2 ^ (prefixWord ++ tailWord_5923070).sum := by decide
  have hdescent : baseEnd_5923070 < baseStart_5923070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923123 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 3]
def baseStart_5923123 : Nat := 118140960795 + 5923123 * 2 ^ 59
def prefixEnd_5923123 : Nat := 4983230072969 + 3 ^ 40 * 5923123 * 2
def baseEnd_5923123 : Nat := 3041409074700934487722559

theorem tailTrace_5923123 : CollatzResearch.WordTrace tailWord_5923123 prefixEnd_5923123 3041409074700934487722559 := by
  unfold tailWord_5923123
  simp only [CollatzResearch.WordTrace]
  refine ⟨216034043720544434716806023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144022695813696289811204015 216034043720544434716806023)
  ·
    refine ⟨324051065580816652075209035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216034043720544434716806023 324051065580816652075209035)
    ·
      refine ⟨486076598371224978112813553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324051065580816652075209035 486076598371224978112813553)
      ·
        refine ⟨364557448778418733584610165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486076598371224978112813553 364557448778418733584610165)
        ·
          refine ⟨34177260822976756273557203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 364557448778418733584610165 34177260822976756273557203)
          ·
            refine ⟨51265891234465134410335805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34177260822976756273557203 51265891234465134410335805)
            ·
              refine ⟨19224709212924425403875927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51265891234465134410335805 19224709212924425403875927)
              ·
                refine ⟨28837063819386638105813891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19224709212924425403875927 28837063819386638105813891)
                ·
                  refine ⟨43255595729079957158720837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28837063819386638105813891 43255595729079957158720837)
                  ·
                    refine ⟨8110424199202491967260157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43255595729079957158720837 8110424199202491967260157)
                    ·
                      refine ⟨3041409074700934487722559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8110424199202491967260157 3041409074700934487722559)
                      ·
                        rfl

theorem cell23_5923123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 3].length) (baseStart_5923123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923123 prefixEnd_5923123 := by exact prefixLift 5923123
  have htrace : WordTrace (prefixWord ++ tailWord_5923123) baseStart_5923123 baseEnd_5923123 := by
    simpa [prefixWord, tailWord_5923123, baseEnd_5923123] using wordTrace_append hprefix tailTrace_5923123
  have hstable : (prefixWord ++ tailWord_5923123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923123).length < 2 ^ (prefixWord ++ tailWord_5923123).sum := by decide
  have hdescent : baseEnd_5923123 < baseStart_5923123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923193 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 5, 1, 4]
def baseStart_5923193 : Nat := 118140960795 + 5923193 * 2 ^ 59
def prefixEnd_5923193 : Nat := 4983230072969 + 3 ^ 40 * 5923193 * 2
def baseEnd_5923193 : Nat := 3041445018346749213847237

theorem tailTrace_5923193 : CollatzResearch.WordTrace tailWord_5923193 prefixEnd_5923193 3041445018346749213847237 := by
  unfold tailWord_5923193
  simp only [CollatzResearch.WordTrace]
  refine ⟨216036596830290836671854233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144024397886860557781236155 216036596830290836671854233)
  ·
    refine ⟨162027447622718127503890675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216036596830290836671854233 162027447622718127503890675)
    ·
      refine ⟨243041171434077191255836013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162027447622718127503890675 243041171434077191255836013)
      ·
        refine ⟨91140439287778946720938505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243041171434077191255836013 91140439287778946720938505)
        ·
          refine ⟨68355329465834210040703879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91140439287778946720938505 68355329465834210040703879)
          ·
            refine ⟨102532994198751315061055819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68355329465834210040703879 102532994198751315061055819)
            ·
              refine ⟨153799491298126972591583729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102532994198751315061055819 153799491298126972591583729)
              ·
                refine ⟨115349618473595229443687797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153799491298126972591583729 115349618473595229443687797)
                ·
                  refine ⟨10814026731899552760345731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115349618473595229443687797 10814026731899552760345731)
                  ·
                    refine ⟨16221040097849329140518597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10814026731899552760345731 16221040097849329140518597)
                    ·
                      refine ⟨3041445018346749213847237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16221040097849329140518597 3041445018346749213847237)
                      ·
                        rfl

theorem cell23_5923193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_5923193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923193 prefixEnd_5923193 := by exact prefixLift 5923193
  have htrace : WordTrace (prefixWord ++ tailWord_5923193) baseStart_5923193 baseEnd_5923193 := by
    simpa [prefixWord, tailWord_5923193, baseEnd_5923193] using wordTrace_append hprefix tailTrace_5923193
  have hstable : (prefixWord ++ tailWord_5923193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923193).length < 2 ^ (prefixWord ++ tailWord_5923193).sum := by decide
  have hdescent : baseEnd_5923193 < baseStart_5923193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923197 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 2, 3, 2]
def baseStart_5923197 : Nat := 118140960795 + 5923197 * 2 ^ 59
def prefixEnd_5923197 : Nat := 4983230072969 + 3 ^ 40 * 5923197 * 2
def baseEnd_5923197 : Nat := 3041447072269367198197219

theorem tailTrace_5923197 : CollatzResearch.WordTrace tailWord_5923197 prefixEnd_5923197 3041447072269367198197219 := by
  unfold tailWord_5923197
  simp only [CollatzResearch.WordTrace]
  refine ⟨216036742722276345354999845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144024495148184230236666563 216036742722276345354999845)
  ·
    refine ⟨40506889260426814754062471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216036742722276345354999845 40506889260426814754062471)
    ·
      refine ⟨60760333890640222131093707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40506889260426814754062471 60760333890640222131093707)
      ·
        refine ⟨91140500835960333196640561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60760333890640222131093707 91140500835960333196640561)
        ·
          refine ⟨68355375626970249897480421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91140500835960333196640561 68355375626970249897480421)
          ·
            refine ⟨12816632930056921855777579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68355375626970249897480421 12816632930056921855777579)
            ·
              refine ⟨19224949395085382783666369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12816632930056921855777579 19224949395085382783666369)
              ·
                refine ⟨14418712046314037087749777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19224949395085382783666369 14418712046314037087749777)
                ·
                  refine ⟨10814034034735527815812333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14418712046314037087749777 10814034034735527815812333)
                  ·
                    refine ⟨4055262763025822930929625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10814034034735527815812333 4055262763025822930929625)
                    ·
                      refine ⟨3041447072269367198197219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055262763025822930929625 3041447072269367198197219)
                      ·
                        rfl

theorem cell23_5923197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_5923197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923197 prefixEnd_5923197 := by exact prefixLift 5923197
  have htrace : WordTrace (prefixWord ++ tailWord_5923197) baseStart_5923197 baseEnd_5923197 := by
    simpa [prefixWord, tailWord_5923197, baseEnd_5923197] using wordTrace_append hprefix tailTrace_5923197
  have hstable : (prefixWord ++ tailWord_5923197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923197).length < 2 ^ (prefixWord ++ tailWord_5923197).sum := by decide
  have hdescent : baseEnd_5923197 < baseStart_5923197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923223 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_5923223 : Nat := 118140960795 + 5923223 * 2 ^ 59
def prefixEnd_5923223 : Nat := 4983230072969 + 3 ^ 40 * 5923223 * 2
def baseEnd_5923223 : Nat := 3041460422766384096472099

theorem tailTrace_5923223 : CollatzResearch.WordTrace tailWord_5923223 prefixEnd_5923223 3041460422766384096472099 := by
  unfold tailWord_5923223
  simp only [CollatzResearch.WordTrace]
  refine ⟨216037691020182151795446323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144025127346788101196964215 216037691020182151795446323)
  ·
    refine ⟨324056536530273227693169485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216037691020182151795446323 324056536530273227693169485)
    ·
      refine ⟨121521201198852460384938557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324056536530273227693169485 121521201198852460384938557)
      ·
        refine ⟨45570450449569672644351959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121521201198852460384938557 45570450449569672644351959)
        ·
          refine ⟨68355675674354508966527939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45570450449569672644351959 68355675674354508966527939)
          ·
            refine ⟨102533513511531763449791909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68355675674354508966527939 102533513511531763449791909)
            ·
              refine ⟨19225033783412205646835983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102533513511531763449791909 19225033783412205646835983)
              ·
                refine ⟨28837550675118308470253975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19225033783412205646835983 28837550675118308470253975)
                ·
                  refine ⟨43256326012677462705380963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28837550675118308470253975 43256326012677462705380963)
                  ·
                    refine ⟨64884489019016194058071445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43256326012677462705380963 64884489019016194058071445)
                    ·
                      refine ⟨3041460422766384096472099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64884489019016194058071445 3041460422766384096472099)
                      ·
                        rfl

theorem cell23_5923223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_5923223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923223 prefixEnd_5923223 := by exact prefixLift 5923223
  have htrace : WordTrace (prefixWord ++ tailWord_5923223) baseStart_5923223 baseEnd_5923223 := by
    simpa [prefixWord, tailWord_5923223, baseEnd_5923223] using wordTrace_append hprefix tailTrace_5923223
  have hstable : (prefixWord ++ tailWord_5923223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923223).length < 2 ^ (prefixWord ++ tailWord_5923223).sum := by decide
  have hdescent : baseEnd_5923223 < baseStart_5923223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923244 : List Nat := [2, 2, 1, 1, 1, 1, 3, 7, 1, 2, 2]
def baseStart_5923244 : Nat := 118140960795 + 5923244 * 2 ^ 59
def prefixEnd_5923244 : Nat := 4983230072969 + 3 ^ 40 * 5923244 * 2
def baseEnd_5923244 : Nat := 3041471205860128514309503

theorem tailTrace_5923244 : CollatzResearch.WordTrace tailWord_5923244 prefixEnd_5923244 3041471205860128514309503 := by
  unfold tailWord_5923244
  simp only [CollatzResearch.WordTrace]
  refine ⟨108019228476553036190980393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144025637968737381587973857 108019228476553036190980393)
  ·
    refine ⟨81014421357414777143235295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108019228476553036190980393 81014421357414777143235295)
    ·
      refine ⟨121521632036122165714852943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81014421357414777143235295 121521632036122165714852943)
      ·
        refine ⟨182282448054183248572279415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121521632036122165714852943 182282448054183248572279415)
        ·
          refine ⟨273423672081274872858419123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182282448054183248572279415 273423672081274872858419123)
          ·
            refine ⟨410135508121912309287628685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273423672081274872858419123 410135508121912309287628685)
            ·
              refine ⟨153800815545717115982860757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 410135508121912309287628685 153800815545717115982860757)
              ·
                refine ⟨3604706614352744905848299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 153800815545717115982860757 3604706614352744905848299)
                ·
                  refine ⟨5407059921529117358772449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604706614352744905848299 5407059921529117358772449)
                  ·
                    refine ⟨4055294941146838019079337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5407059921529117358772449 4055294941146838019079337)
                    ·
                      refine ⟨3041471205860128514309503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055294941146838019079337 3041471205860128514309503)
                      ·
                        rfl

theorem cell23_5923244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 1, 2, 2].length) (baseStart_5923244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923244 prefixEnd_5923244 := by exact prefixLift 5923244
  have htrace : WordTrace (prefixWord ++ tailWord_5923244) baseStart_5923244 baseEnd_5923244 := by
    simpa [prefixWord, tailWord_5923244, baseEnd_5923244] using wordTrace_append hprefix tailTrace_5923244
  have hstable : (prefixWord ++ tailWord_5923244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923244).length < 2 ^ (prefixWord ++ tailWord_5923244).sum := by decide
  have hdescent : baseEnd_5923244 < baseStart_5923244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923261 : List Nat := [1, 4, 1, 2, 2, 3, 1, 4, 1, 2, 2]
def baseStart_5923261 : Nat := 118140960795 + 5923261 * 2 ^ 59
def prefixEnd_5923261 : Nat := 4983230072969 + 3 ^ 40 * 5923261 * 2
def baseEnd_5923261 : Nat := 3041479935031254947796925

theorem tailTrace_5923261 : CollatzResearch.WordTrace tailWord_5923261 prefixEnd_5923261 3041479935031254947796925 := by
  unfold tailWord_5923261
  simp only [CollatzResearch.WordTrace]
  refine ⟨216039076994044484285329637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144026051329362989523553091 216039076994044484285329637)
  ·
    refine ⟨40507326936383340803499307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216039076994044484285329637 40507326936383340803499307)
    ·
      refine ⟨60760990404575011205248961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40507326936383340803499307 60760990404575011205248961)
      ·
        refine ⟨45570742803431258403936721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60760990404575011205248961 45570742803431258403936721)
        ·
          refine ⟨34178057102573443802952541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45570742803431258403936721 34178057102573443802952541)
          ·
            refine ⟨12816771413465041426107203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34178057102573443802952541 12816771413465041426107203)
            ·
              refine ⟨19225157120197562139160805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12816771413465041426107203 19225157120197562139160805)
              ·
                refine ⟨3604716960037042901092651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19225157120197562139160805 3604716960037042901092651)
                ·
                  refine ⟨5407075440055564351638977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604716960037042901092651 5407075440055564351638977)
                  ·
                    refine ⟨4055306580041673263729233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5407075440055564351638977 4055306580041673263729233)
                    ·
                      refine ⟨3041479935031254947796925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055306580041673263729233 3041479935031254947796925)
                      ·
                        rfl

theorem cell23_5923261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_5923261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923261 prefixEnd_5923261 := by exact prefixLift 5923261
  have htrace : WordTrace (prefixWord ++ tailWord_5923261) baseStart_5923261 baseEnd_5923261 := by
    simpa [prefixWord, tailWord_5923261, baseEnd_5923261] using wordTrace_append hprefix tailTrace_5923261
  have hstable : (prefixWord ++ tailWord_5923261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923261).length < 2 ^ (prefixWord ++ tailWord_5923261).sum := by decide
  have hdescent : baseEnd_5923261 < baseStart_5923261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923304 : List Nat := [2, 1, 4, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_5923304 : Nat := 118140960795 + 5923304 * 2 ^ 59
def prefixEnd_5923304 : Nat := 4983230072969 + 3 ^ 40 * 5923304 * 2
def baseEnd_5923304 : Nat := 3041502014699398279559227

theorem tailTrace_5923304 : CollatzResearch.WordTrace tailWord_5923304 prefixEnd_5923304 3041502014699398279559227 := by
  unfold tailWord_5923304
  simp only [CollatzResearch.WordTrace]
  refine ⟨108020322666444351314572483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144027096888592468419429977 108020322666444351314572483)
  ·
    refine ⟨162030483999666526971858725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108020322666444351314572483 162030483999666526971858725)
    ·
      refine ⟨30380715749937473807223511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162030483999666526971858725 30380715749937473807223511)
      ·
        refine ⟨45571073624906210710835267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30380715749937473807223511 45571073624906210710835267)
        ·
          refine ⟨68356610437359316066252901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45571073624906210710835267 68356610437359316066252901)
          ·
            refine ⟨12816864457004871762422419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68356610437359316066252901 12816864457004871762422419)
            ·
              refine ⟨19225296685507307643633629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12816864457004871762422419 19225296685507307643633629)
              ·
                refine ⟨7209486257065240366362611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19225296685507307643633629 7209486257065240366362611)
                ·
                  refine ⟨10814229385597860549543917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7209486257065240366362611 10814229385597860549543917)
                  ·
                    refine ⟨4055336019599197706078969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10814229385597860549543917 4055336019599197706078969)
                    ·
                      refine ⟨3041502014699398279559227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055336019599197706078969 3041502014699398279559227)
                      ·
                        rfl

theorem cell23_5923304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_5923304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923304 prefixEnd_5923304 := by exact prefixLift 5923304
  have htrace : WordTrace (prefixWord ++ tailWord_5923304) baseStart_5923304 baseEnd_5923304 := by
    simpa [prefixWord, tailWord_5923304, baseEnd_5923304] using wordTrace_append hprefix tailTrace_5923304
  have hstable : (prefixWord ++ tailWord_5923304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923304).length < 2 ^ (prefixWord ++ tailWord_5923304).sum := by decide
  have hdescent : baseEnd_5923304 < baseStart_5923304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923310 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_5923310 : Nat := 118140960795 + 5923310 * 2 ^ 59
def prefixEnd_5923310 : Nat := 4983230072969 + 3 ^ 40 * 5923310 * 2
def baseEnd_5923310 : Nat := 1013835031861108418694733

theorem tailTrace_5923310 : CollatzResearch.WordTrace tailWord_5923310 prefixEnd_5923310 1013835031861108418694733 := by
  unfold tailWord_5923310
  simp only [CollatzResearch.WordTrace]
  refine ⟨27005108021358370706732923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144027242780577977102575589 27005108021358370706732923)
  ·
    refine ⟨40507662032037556060099385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27005108021358370706732923 40507662032037556060099385)
    ·
      refine ⟨30380746524028167045074539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40507662032037556060099385 30380746524028167045074539)
      ·
        refine ⟨45571119786042250567611809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30380746524028167045074539 45571119786042250567611809)
        ·
          refine ⟨34178339839531687925708857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45571119786042250567611809 34178339839531687925708857)
          ·
            refine ⟨25633754879648765944281643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34178339839531687925708857 25633754879648765944281643)
            ·
              refine ⟨38450632319473148916422465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25633754879648765944281643 38450632319473148916422465)
              ·
                refine ⟨28837974239604861687316849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38450632319473148916422465 28837974239604861687316849)
                ·
                  refine ⟨21628480679703646265487637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28837974239604861687316849 21628480679703646265487637)
                  ·
                    refine ⟨1013835031861108418694733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21628480679703646265487637 1013835031861108418694733)
                    ·
                      rfl

theorem cell23_5923310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_5923310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923310 prefixEnd_5923310 := by exact prefixLift 5923310
  have htrace : WordTrace (prefixWord ++ tailWord_5923310) baseStart_5923310 baseEnd_5923310 := by
    simpa [prefixWord, tailWord_5923310, baseEnd_5923310] using wordTrace_append hprefix tailTrace_5923310
  have hstable : (prefixWord ++ tailWord_5923310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923310).length < 2 ^ (prefixWord ++ tailWord_5923310).sum := by decide
  have hdescent : baseEnd_5923310 < baseStart_5923310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923340 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 7]
def baseStart_5923340 : Nat := 118140960795 + 5923340 * 2 ^ 59
def prefixEnd_5923340 : Nat := 4983230072969 + 3 ^ 40 * 5923340 * 2
def baseEnd_5923340 : Nat := 337946722222551126523229

theorem tailTrace_5923340 : CollatzResearch.WordTrace tailWord_5923340 prefixEnd_5923340 337946722222551126523229 := by
  unfold tailWord_5923340
  simp only [CollatzResearch.WordTrace]
  refine ⟨108020979180379140388727737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144027972240505520518303649 108020979180379140388727737)
  ·
    refine ⟨81015734385284355291545803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108020979180379140388727737 81015734385284355291545803)
    ·
      refine ⟨121523601577926532937318705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81015734385284355291545803 121523601577926532937318705)
      ·
        refine ⟨91142701183444899702989029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121523601577926532937318705 91142701183444899702989029)
        ·
          refine ⟨17089256471895918694310443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91142701183444899702989029 17089256471895918694310443)
          ·
            refine ⟨25633884707843878041465665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17089256471895918694310443 25633884707843878041465665)
            ·
              refine ⟨19225413530882908531099249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25633884707843878041465665 19225413530882908531099249)
              ·
                refine ⟨14419060148162181398324437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19225413530882908531099249 14419060148162181398324437)
                ·
                  refine ⟨337946722222551126523229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14419060148162181398324437 337946722222551126523229)
                  ·
                    rfl

theorem cell23_5923340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_5923340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923340 prefixEnd_5923340 := by exact prefixLift 5923340
  have htrace : WordTrace (prefixWord ++ tailWord_5923340) baseStart_5923340 baseEnd_5923340 := by
    simpa [prefixWord, tailWord_5923340, baseEnd_5923340] using wordTrace_append hprefix tailTrace_5923340
  have hstable : (prefixWord ++ tailWord_5923340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923340).length < 2 ^ (prefixWord ++ tailWord_5923340).sum := by decide
  have hdescent : baseEnd_5923340 < baseStart_5923340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923374 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 7]
def baseStart_5923374 : Nat := 118140960795 + 5923374 * 2 ^ 59
def prefixEnd_5923374 : Nat := 4983230072969 + 3 ^ 40 * 5923374 * 2
def baseEnd_5923374 : Nat := 337948662038357000631545

theorem tailTrace_5923374 : CollatzResearch.WordTrace tailWord_5923374 prefixEnd_5923374 337948662038357000631545 := by
  unfold tailWord_5923374
  simp only [CollatzResearch.WordTrace]
  refine ⟨27005399805329388073024147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144028798961756736389462117 27005399805329388073024147)
  ·
    refine ⟨40508099707994082109536221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27005399805329388073024147 40508099707994082109536221)
    ·
      refine ⟨15190537390497780791076083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40508099707994082109536221 15190537390497780791076083)
      ·
        refine ⟨22785806085746671186614125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15190537390497780791076083 22785806085746671186614125)
        ·
          refine ⟨8544677282155001694980297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22785806085746671186614125 8544677282155001694980297)
          ·
            refine ⟨6408507961616251271235223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8544677282155001694980297 6408507961616251271235223)
            ·
              refine ⟨9612761942424376906852835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6408507961616251271235223 9612761942424376906852835)
              ·
                refine ⟨14419142913636565360279253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9612761942424376906852835 14419142913636565360279253)
                ·
                  refine ⟨337948662038357000631545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14419142913636565360279253 337948662038357000631545)
                  ·
                    rfl

theorem cell23_5923374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_5923374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923374 prefixEnd_5923374 := by exact prefixLift 5923374
  have htrace : WordTrace (prefixWord ++ tailWord_5923374) baseStart_5923374 baseEnd_5923374 := by
    simpa [prefixWord, tailWord_5923374, baseEnd_5923374] using wordTrace_append hprefix tailTrace_5923374
  have hstable : (prefixWord ++ tailWord_5923374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923374).length < 2 ^ (prefixWord ++ tailWord_5923374).sum := by decide
  have hdescent : baseEnd_5923374 < baseStart_5923374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923427 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 3]
def baseStart_5923427 : Nat := 118140960795 + 5923427 * 2 ^ 59
def prefixEnd_5923427 : Nat := 4983230072969 + 3 ^ 40 * 5923427 * 2
def baseEnd_5923427 : Nat := 3041565172819901298321161

theorem tailTrace_5923427 : CollatzResearch.WordTrace tailWord_5923427 prefixEnd_5923427 3041565172819901298321161 := by
  unfold tailWord_5923427
  simp only [CollatzResearch.WordTrace]
  refine ⟨216045131511443094635872535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144030087674295396423915023 216045131511443094635872535)
  ·
    refine ⟨324067697267164641953808803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216045131511443094635872535 324067697267164641953808803)
    ·
      refine ⟨486101545900746962930713205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324067697267164641953808803 486101545900746962930713205)
      ·
        refine ⟨45572019928195027774754363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 486101545900746962930713205 45572019928195027774754363)
        ·
          refine ⟨68358029892292541662131545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45572019928195027774754363 68358029892292541662131545)
          ·
            refine ⟨51268522419219406246598659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68358029892292541662131545 51268522419219406246598659)
            ·
              refine ⟨76902783628829109369897989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51268522419219406246598659 76902783628829109369897989)
              ·
                refine ⟨14419271930405458006855873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76902783628829109369897989 14419271930405458006855873)
                ·
                  refine ⟨10814453947804093505141905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14419271930405458006855873 10814453947804093505141905)
                  ·
                    refine ⟨8110840460853070128856429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10814453947804093505141905 8110840460853070128856429)
                    ·
                      refine ⟨3041565172819901298321161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8110840460853070128856429 3041565172819901298321161)
                      ·
                        rfl

theorem cell23_5923427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_5923427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923427 prefixEnd_5923427 := by exact prefixLift 5923427
  have htrace : WordTrace (prefixWord ++ tailWord_5923427) baseStart_5923427 baseEnd_5923427 := by
    simpa [prefixWord, tailWord_5923427, baseEnd_5923427] using wordTrace_append hprefix tailTrace_5923427
  have hstable : (prefixWord ++ tailWord_5923427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923427).length < 2 ^ (prefixWord ++ tailWord_5923427).sum := by decide
  have hdescent : baseEnd_5923427 < baseStart_5923427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923458 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5923458 : Nat := 118140960795 + 5923458 * 2 ^ 59
def prefixEnd_5923458 : Nat := 4983230072969 + 3 ^ 40 * 5923458 * 2
def baseEnd_5923458 : Nat := 3041581090720190677033519

theorem tailTrace_5923458 : CollatzResearch.WordTrace tailWord_5923458 prefixEnd_5923458 3041581090720190677033519 := by
  unfold tailWord_5923458
  simp only [CollatzResearch.WordTrace]
  refine ⟨54011565543582696732562757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144030841449553857953500685 54011565543582696732562757)
  ·
    refine ⟨10127168539421755637355517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54011565543582696732562757 10127168539421755637355517)
    ·
      refine ⟨3797688202283158364008319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10127168539421755637355517 3797688202283158364008319)
      ·
        refine ⟨5696532303424737546012479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3797688202283158364008319 5696532303424737546012479)
        ·
          refine ⟨8544798455137106319018719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5696532303424737546012479 8544798455137106319018719)
          ·
            refine ⟨12817197682705659478528079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8544798455137106319018719 12817197682705659478528079)
            ·
              refine ⟨19225796524058489217792119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12817197682705659478528079 19225796524058489217792119)
              ·
                refine ⟨28838694786087733826688179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19225796524058489217792119 28838694786087733826688179)
                ·
                  refine ⟨43258042179131600740032269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28838694786087733826688179 43258042179131600740032269)
                  ·
                    refine ⟨16221765817174350277512101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43258042179131600740032269 16221765817174350277512101)
                    ·
                      refine ⟨3041581090720190677033519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16221765817174350277512101 3041581090720190677033519)
                      ·
                        rfl

theorem cell23_5923458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5923458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923458 prefixEnd_5923458 := by exact prefixLift 5923458
  have htrace : WordTrace (prefixWord ++ tailWord_5923458) baseStart_5923458 baseEnd_5923458 := by
    simpa [prefixWord, tailWord_5923458, baseEnd_5923458] using wordTrace_append hprefix tailTrace_5923458
  have hstable : (prefixWord ++ tailWord_5923458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923458).length < 2 ^ (prefixWord ++ tailWord_5923458).sum := by decide
  have hdescent : baseEnd_5923458 < baseStart_5923458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923497 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 2, 6, 2]
def baseStart_5923497 : Nat := 118140960795 + 5923497 * 2 ^ 59
def prefixEnd_5923497 : Nat := 4983230072969 + 3 ^ 40 * 5923497 * 2
def baseEnd_5923497 : Nat := 3041601116465716024445839

theorem tailTrace_5923497 : CollatzResearch.WordTrace tailWord_5923497 prefixEnd_5923497 3041601116465716024445839 := by
  unfold tailWord_5923497
  simp only [CollatzResearch.WordTrace]
  refine ⟨216047684621189496590920745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144031789747459664393947163 216047684621189496590920745)
  ·
    refine ⟨162035763465892122443190559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216047684621189496590920745 162035763465892122443190559)
    ·
      refine ⟨243053645198838183664785839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162035763465892122443190559 243053645198838183664785839)
      ·
        refine ⟨364580467798257275497178759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243053645198838183664785839 364580467798257275497178759)
        ·
          refine ⟨546870701697385913245768139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364580467798257275497178759 546870701697385913245768139)
          ·
            refine ⟨820306052546078869868652209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546870701697385913245768139 820306052546078869868652209)
            ·
              refine ⟨615229539409559152401489157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820306052546078869868652209 615229539409559152401489157)
              ·
                refine ⟨115355538639292341075279217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 615229539409559152401489157 115355538639292341075279217)
                ·
                  refine ⟨86516653979469255806459413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115355538639292341075279217 86516653979469255806459413)
                  ·
                    refine ⟨4055468155287621365927785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86516653979469255806459413 4055468155287621365927785)
                    ·
                      refine ⟨3041601116465716024445839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055468155287621365927785 3041601116465716024445839)
                      ·
                        rfl

theorem cell23_5923497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 6, 2].length) (baseStart_5923497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923497 prefixEnd_5923497 := by exact prefixLift 5923497
  have htrace : WordTrace (prefixWord ++ tailWord_5923497) baseStart_5923497 baseEnd_5923497 := by
    simpa [prefixWord, tailWord_5923497, baseEnd_5923497] using wordTrace_append hprefix tailTrace_5923497
  have hstable : (prefixWord ++ tailWord_5923497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923497).length < 2 ^ (prefixWord ++ tailWord_5923497).sum := by decide
  have hdescent : baseEnd_5923497 < baseStart_5923497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923498 : List Nat := [3, 1, 5, 2, 1, 1, 3, 1, 6]
def baseStart_5923498 : Nat := 118140960795 + 5923498 * 2 ^ 59
def prefixEnd_5923498 : Nat := 4983230072969 + 3 ^ 40 * 5923498 * 2
def baseEnd_5923498 : Nat := 337955736660707835614815

theorem tailTrace_5923498 : CollatzResearch.WordTrace tailWord_5923498 prefixEnd_5923498 337955736660707835614815 := by
  unfold tailWord_5923498
  simp only [CollatzResearch.WordTrace]
  refine ⟨54011930273546468440426787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144031814062790582507804765 54011930273546468440426787)
  ·
    refine ⟨81017895410319702660640181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54011930273546468440426787 81017895410319702660640181)
    ·
      refine ⟨7595427694717472124435017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81017895410319702660640181 7595427694717472124435017)
      ·
        refine ⟨5696570771038104093326263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7595427694717472124435017 5696570771038104093326263)
        ·
          refine ⟨8544856156557156139989395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5696570771038104093326263 8544856156557156139989395)
          ·
            refine ⟨12817284234835734209984093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8544856156557156139989395 12817284234835734209984093)
            ·
              refine ⟨4806481588063400328744035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12817284234835734209984093 4806481588063400328744035)
              ·
                refine ⟨7209722382095100493116053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4806481588063400328744035 7209722382095100493116053)
                ·
                  refine ⟨337955736660707835614815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7209722382095100493116053 337955736660707835614815)
                  ·
                    rfl

theorem cell23_5923498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 6].length) (baseStart_5923498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923498 prefixEnd_5923498 := by exact prefixLift 5923498
  have htrace : WordTrace (prefixWord ++ tailWord_5923498) baseStart_5923498 baseEnd_5923498 := by
    simpa [prefixWord, tailWord_5923498, baseEnd_5923498] using wordTrace_append hprefix tailTrace_5923498
  have hstable : (prefixWord ++ tailWord_5923498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923498).length < 2 ^ (prefixWord ++ tailWord_5923498).sum := by decide
  have hdescent : baseEnd_5923498 < baseStart_5923498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923507 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 1, 6]
def baseStart_5923507 : Nat := 118140960795 + 5923507 * 2 ^ 59
def prefixEnd_5923507 : Nat := 4983230072969 + 3 ^ 40 * 5923507 * 2
def baseEnd_5923507 : Nat := 1013868750424086995106931

theorem tailTrace_5923507 : CollatzResearch.WordTrace tailWord_5923507 prefixEnd_5923507 1013868750424086995106931 := by
  unfold tailWord_5923507
  simp only [CollatzResearch.WordTrace]
  refine ⟨216048049351153268298784775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144032032900768845532523183 216048049351153268298784775)
  ·
    refine ⟨324072074026729902448177163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216048049351153268298784775 324072074026729902448177163)
    ·
      refine ⟨486108111040094853672265745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324072074026729902448177163 486108111040094853672265745)
      ·
        refine ⟨364581083280071140254199309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486108111040094853672265745 364581083280071140254199309)
        ·
          refine ⟨136717906230026677595324741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364581083280071140254199309 136717906230026677595324741)
          ·
            refine ⟨25634607418130002049123389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136717906230026677595324741 25634607418130002049123389)
            ·
              refine ⟨9612977781798750768421271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25634607418130002049123389 9612977781798750768421271)
              ·
                refine ⟨14419466672698126152631907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9612977781798750768421271 14419466672698126152631907)
                ·
                  refine ⟨21629200009047189228947861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14419466672698126152631907 21629200009047189228947861)
                  ·
                    refine ⟨1013868750424086995106931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21629200009047189228947861 1013868750424086995106931)
                    ·
                      rfl

theorem cell23_5923507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 6].length) (baseStart_5923507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923507 prefixEnd_5923507 := by exact prefixLift 5923507
  have htrace : WordTrace (prefixWord ++ tailWord_5923507) baseStart_5923507 baseEnd_5923507 := by
    simpa [prefixWord, tailWord_5923507, baseEnd_5923507] using wordTrace_append hprefix tailTrace_5923507
  have hstable : (prefixWord ++ tailWord_5923507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923507).length < 2 ^ (prefixWord ++ tailWord_5923507).sum := by decide
  have hdescent : baseEnd_5923507 < baseStart_5923507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923514 : List Nat := [3, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4]
def baseStart_5923514 : Nat := 118140960795 + 5923514 * 2 ^ 59
def prefixEnd_5923514 : Nat := 4983230072969 + 3 ^ 40 * 5923514 * 2
def baseEnd_5923514 : Nat := 3041609845636842457933261

theorem tailTrace_5923514 : CollatzResearch.WordTrace tailWord_5923514 prefixEnd_5923514 3041609845636842457933261 := by
  unfold tailWord_5923514
  simp only [CollatzResearch.WordTrace]
  refine ⟨54012076165531977123572399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144032203108085272329526397 54012076165531977123572399)
  ·
    refine ⟨81018114248297965685358599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54012076165531977123572399 81018114248297965685358599)
    ·
      refine ⟨121527171372446948528037899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81018114248297965685358599 121527171372446948528037899)
      ·
        refine ⟨182290757058670422792056849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121527171372446948528037899 182290757058670422792056849)
        ·
          refine ⟨136718067794002817094042637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182290757058670422792056849 136718067794002817094042637)
          ·
            refine ⟨51269275422751056410265989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136718067794002817094042637 51269275422751056410265989)
            ·
              refine ⟨9612989141765823076924873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51269275422751056410265989 9612989141765823076924873)
              ·
                refine ⟨7209741856324367307693655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9612989141765823076924873 7209741856324367307693655)
                ·
                  refine ⟨10814612784486550961540483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7209741856324367307693655 10814612784486550961540483)
                  ·
                    refine ⟨16221919176729826442310725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10814612784486550961540483 16221919176729826442310725)
                    ·
                      refine ⟨3041609845636842457933261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16221919176729826442310725 3041609845636842457933261)
                      ·
                        rfl

theorem cell23_5923514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_5923514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923514 prefixEnd_5923514 := by exact prefixLift 5923514
  have htrace : WordTrace (prefixWord ++ tailWord_5923514) baseStart_5923514 baseEnd_5923514 := by
    simpa [prefixWord, tailWord_5923514, baseEnd_5923514] using wordTrace_append hprefix tailTrace_5923514
  have hstable : (prefixWord ++ tailWord_5923514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923514).length < 2 ^ (prefixWord ++ tailWord_5923514).sum := by decide
  have hdescent : baseEnd_5923514 < baseStart_5923514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923524 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_5923524 : Nat := 118140960795 + 5923524 * 2 ^ 59
def prefixEnd_5923524 : Nat := 4983230072969 + 3 ^ 40 * 5923524 * 2
def baseEnd_5923524 : Nat := 1013871660147795806269405

theorem tailTrace_5923524 : CollatzResearch.WordTrace tailWord_5923524 prefixEnd_5923524 1013871660147795806269405 := by
  unfold tailWord_5923524
  simp only [CollatzResearch.WordTrace]
  refine ⟨108024334696045840101076813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144032446261394453468102417 108024334696045840101076813)
  ·
    refine ⟨40509125511017190037903805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108024334696045840101076813 40509125511017190037903805)
    ·
      refine ⟨15190922066631446264213927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40509125511017190037903805 15190922066631446264213927)
      ·
        refine ⟨22786383099947169396320891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15190922066631446264213927 22786383099947169396320891)
        ·
          refine ⟨34179574649920754094481337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22786383099947169396320891 34179574649920754094481337)
          ·
            refine ⟨25634680987440565570861003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34179574649920754094481337 25634680987440565570861003)
            ·
              refine ⟨38452021481160848356291505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25634680987440565570861003 38452021481160848356291505)
              ·
                refine ⟨28839016110870636267218629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38452021481160848356291505 28839016110870636267218629)
                ·
                  refine ⟨5407315520788244300103493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28839016110870636267218629 5407315520788244300103493)
                  ·
                    refine ⟨1013871660147795806269405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5407315520788244300103493 1013871660147795806269405)
                    ·
                      rfl

theorem cell23_5923524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_5923524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923524 prefixEnd_5923524 := by exact prefixLift 5923524
  have htrace : WordTrace (prefixWord ++ tailWord_5923524) baseStart_5923524 baseEnd_5923524 := by
    simpa [prefixWord, tailWord_5923524, baseEnd_5923524] using wordTrace_append hprefix tailTrace_5923524
  have hstable : (prefixWord ++ tailWord_5923524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923524).length < 2 ^ (prefixWord ++ tailWord_5923524).sum := by decide
  have hdescent : baseEnd_5923524 < baseStart_5923524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923534 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_5923534 : Nat := 118140960795 + 5923534 * 2 ^ 59
def prefixEnd_5923534 : Nat := 4983230072969 + 3 ^ 40 * 5923534 * 2
def baseEnd_5923534 : Nat := 3041620115249932379683169

theorem tailTrace_5923534 : CollatzResearch.WordTrace tailWord_5923534 prefixEnd_5923534 3041620115249932379683169 := by
  unfold tailWord_5923534
  simp only [CollatzResearch.WordTrace]
  refine ⟨27006129265256931488752207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144032689414703634606678437 27006129265256931488752207)
  ·
    refine ⟨40509193897885397233128311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27006129265256931488752207 40509193897885397233128311)
    ·
      refine ⟨60763790846828095849692467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40509193897885397233128311 60763790846828095849692467)
      ·
        refine ⟨91145686270242143774538701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60763790846828095849692467 91145686270242143774538701)
        ·
          refine ⟨34179632351340803915452013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91145686270242143774538701 34179632351340803915452013)
          ·
            refine ⟨12817362131752801468294505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34179632351340803915452013 12817362131752801468294505)
            ·
              refine ⟨9613021598814601101220879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12817362131752801468294505 9613021598814601101220879)
              ·
                refine ⟨14419532398221901651831319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9613021598814601101220879 14419532398221901651831319)
                ·
                  refine ⟨21629298597332852477746979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14419532398221901651831319 21629298597332852477746979)
                  ·
                    refine ⟨32443947895999278716620469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21629298597332852477746979 32443947895999278716620469)
                    ·
                      refine ⟨3041620115249932379683169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32443947895999278716620469 3041620115249932379683169)
                      ·
                        rfl

theorem cell23_5923534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_5923534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923534 prefixEnd_5923534 := by exact prefixLift 5923534
  have htrace : WordTrace (prefixWord ++ tailWord_5923534) baseStart_5923534 baseEnd_5923534 := by
    simpa [prefixWord, tailWord_5923534, baseEnd_5923534] using wordTrace_append hprefix tailTrace_5923534
  have hstable : (prefixWord ++ tailWord_5923534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923534).length < 2 ^ (prefixWord ++ tailWord_5923534).sum := by decide
  have hdescent : baseEnd_5923534 < baseStart_5923534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923621 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 1, 4, 2]
def baseStart_5923621 : Nat := 118140960795 + 5923621 * 2 ^ 59
def prefixEnd_5923621 : Nat := 4983230072969 + 3 ^ 40 * 5923621 * 2
def baseEnd_5923621 : Nat := 3041664788066873539295269

theorem tailTrace_5923621 : CollatzResearch.WordTrace tailWord_5923621 prefixEnd_5923621 3041664788066873539295269 := by
  unfold tailWord_5923621
  simp only [CollatzResearch.WordTrace]
  refine ⟨216052207272740265768434717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144034804848493510512289811 216052207272740265768434717)
  ·
    refine ⟨81019577727277599663163019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216052207272740265768434717 81019577727277599663163019)
    ·
      refine ⟨121529366590916399494744529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81019577727277599663163019 121529366590916399494744529)
      ·
        refine ⟨91147024943187299621058397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121529366590916399494744529 91147024943187299621058397)
        ·
          refine ⟨34180134353695237357896899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91147024943187299621058397 34180134353695237357896899)
          ·
            refine ⟨51270201530542856036845349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34180134353695237357896899 51270201530542856036845349)
            ·
              refine ⟨9613162786976785506908503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51270201530542856036845349 9613162786976785506908503)
              ·
                refine ⟨14419744180465178260362755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9613162786976785506908503 14419744180465178260362755)
                ·
                  refine ⟨21629616270697767390544133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14419744180465178260362755 21629616270697767390544133)
                  ·
                    refine ⟨4055553050755831385727025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21629616270697767390544133 4055553050755831385727025)
                    ·
                      refine ⟨3041664788066873539295269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055553050755831385727025 3041664788066873539295269)
                      ·
                        rfl

theorem cell23_5923621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_5923621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923621 prefixEnd_5923621 := by exact prefixLift 5923621
  have htrace : WordTrace (prefixWord ++ tailWord_5923621) baseStart_5923621 baseEnd_5923621 := by
    simpa [prefixWord, tailWord_5923621, baseEnd_5923621] using wordTrace_append hprefix tailTrace_5923621
  have hstable : (prefixWord ++ tailWord_5923621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923621).length < 2 ^ (prefixWord ++ tailWord_5923621).sum := by decide
  have hdescent : baseEnd_5923621 < baseStart_5923621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923624 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_5923624 : Nat := 118140960795 + 5923624 * 2 ^ 59
def prefixEnd_5923624 : Nat := 4983230072969 + 3 ^ 40 * 5923624 * 2
def baseEnd_5923624 : Nat := 3041666328508837027557755

theorem tailTrace_5923624 : CollatzResearch.WordTrace tailWord_5923624 prefixEnd_5923624 3041666328508837027557755 := by
  unfold tailWord_5923624
  simp only [CollatzResearch.WordTrace]
  refine ⟨108026158345864698640396963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144034877794486264853862617 108026158345864698640396963)
  ·
    refine ⟨162039237518797047960595445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108026158345864698640396963 162039237518797047960595445)
    ·
      refine ⟨15191178517387223246305823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162039237518797047960595445 15191178517387223246305823)
      ·
        refine ⟨22786767776080834869458735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15191178517387223246305823 22786767776080834869458735)
        ·
          refine ⟨34180151664121252304188103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22786767776080834869458735 34180151664121252304188103)
          ·
            refine ⟨51270227496181878456282155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34180151664121252304188103 51270227496181878456282155)
            ·
              refine ⟨76905341244272817684423233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51270227496181878456282155 76905341244272817684423233)
              ·
                refine ⟨57679005933204613263317425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76905341244272817684423233 57679005933204613263317425)
                ·
                  refine ⟨43259254449903459947488069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57679005933204613263317425 43259254449903459947488069)
                  ·
                    refine ⟨8111110209356898740154013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43259254449903459947488069 8111110209356898740154013)
                    ·
                      refine ⟨3041666328508837027557755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8111110209356898740154013 3041666328508837027557755)
                      ·
                        rfl

theorem cell23_5923624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_5923624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923624 prefixEnd_5923624 := by exact prefixLift 5923624
  have htrace : WordTrace (prefixWord ++ tailWord_5923624) baseStart_5923624 baseEnd_5923624 := by
    simpa [prefixWord, tailWord_5923624, baseEnd_5923624] using wordTrace_append hprefix tailTrace_5923624
  have hstable : (prefixWord ++ tailWord_5923624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923624).length < 2 ^ (prefixWord ++ tailWord_5923624).sum := by decide
  have hdescent : baseEnd_5923624 < baseStart_5923624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923642 : List Nat := [3, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2]
def baseStart_5923642 : Nat := 118140960795 + 5923642 * 2 ^ 59
def prefixEnd_5923642 : Nat := 4983230072969 + 3 ^ 40 * 5923642 * 2
def baseEnd_5923642 : Nat := 3041675571160617957132673

theorem tailTrace_5923642 : CollatzResearch.WordTrace tailWord_5923642 prefixEnd_5923642 3041675571160617957132673 := by
  unfold tailWord_5923642
  simp only [CollatzResearch.WordTrace]
  refine ⟨54013243301416046588737295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144035315470442790903299453 54013243301416046588737295)
  ·
    refine ⟨81019864952124069883105943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54013243301416046588737295 81019864952124069883105943)
    ·
      refine ⟨121529797428186104824658915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81019864952124069883105943 121529797428186104824658915)
      ·
        refine ⟨182294696142279157236988373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121529797428186104824658915 182294696142279157236988373)
        ·
          refine ⟨4272531940834667747741915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 182294696142279157236988373 4272531940834667747741915)
          ·
            refine ⟨6408797911252001621612873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272531940834667747741915 6408797911252001621612873)
            ·
              refine ⟨4806598433439001216209655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6408797911252001621612873 4806598433439001216209655)
              ·
                refine ⟨7209897650158501824314483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4806598433439001216209655 7209897650158501824314483)
                ·
                  refine ⟨10814846475237752736471725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7209897650158501824314483 10814846475237752736471725)
                  ·
                    refine ⟨4055567428214157276176897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10814846475237752736471725 4055567428214157276176897)
                    ·
                      refine ⟨3041675571160617957132673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055567428214157276176897 3041675571160617957132673)
                      ·
                        rfl

theorem cell23_5923642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2].length) (baseStart_5923642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923642 prefixEnd_5923642 := by exact prefixLift 5923642
  have htrace : WordTrace (prefixWord ++ tailWord_5923642) baseStart_5923642 baseEnd_5923642 := by
    simpa [prefixWord, tailWord_5923642, baseEnd_5923642] using wordTrace_append hprefix tailTrace_5923642
  have hstable : (prefixWord ++ tailWord_5923642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923642).length < 2 ^ (prefixWord ++ tailWord_5923642).sum := by decide
  have hdescent : baseEnd_5923642 < baseStart_5923642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923664 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 1, 7, 2]
def baseStart_5923664 : Nat := 118140960795 + 5923664 * 2 ^ 59
def prefixEnd_5923664 : Nat := 4983230072969 + 3 ^ 40 * 5923664 * 2
def baseEnd_5923664 : Nat := 3041686867735016871057571

theorem tailTrace_5923664 : CollatzResearch.WordTrace tailWord_5923664 prefixEnd_5923664 3041686867735016871057571 := by
  unfold tailWord_5923664
  simp only [CollatzResearch.WordTrace]
  refine ⟨108026887805792242056125023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144035850407722989408166697 108026887805792242056125023)
  ·
    refine ⟨162040331708688363084187535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108026887805792242056125023 162040331708688363084187535)
    ·
      refine ⟨243060497563032544626281303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162040331708688363084187535 243060497563032544626281303)
      ·
        refine ⟨364590746344548816939421955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243060497563032544626281303 364590746344548816939421955)
        ·
          refine ⟨546886119516823225409132933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364590746344548816939421955 546886119516823225409132933)
          ·
            refine ⟨102541147409404354764212425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 546886119516823225409132933 102541147409404354764212425)
            ·
              refine ⟨76905860557053266073159319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102541147409404354764212425 76905860557053266073159319)
              ·
                refine ⟨115358790835579899109738979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76905860557053266073159319 115358790835579899109738979)
                ·
                  refine ⟨173038186253369848664608469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115358790835579899109738979 173038186253369848664608469)
                  ·
                    refine ⟨4055582490313355828076761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 173038186253369848664608469 4055582490313355828076761)
                    ·
                      refine ⟨3041686867735016871057571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055582490313355828076761 3041686867735016871057571)
                      ·
                        rfl

theorem cell23_5923664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 7, 2].length) (baseStart_5923664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923664 prefixEnd_5923664 := by exact prefixLift 5923664
  have htrace : WordTrace (prefixWord ++ tailWord_5923664) baseStart_5923664 baseEnd_5923664 := by
    simpa [prefixWord, tailWord_5923664, baseEnd_5923664] using wordTrace_append hprefix tailTrace_5923664
  have hstable : (prefixWord ++ tailWord_5923664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923664).length < 2 ^ (prefixWord ++ tailWord_5923664).sum := by decide
  have hdescent : baseEnd_5923664 < baseStart_5923664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923667 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 5]
def baseStart_5923667 : Nat := 118140960795 + 5923667 * 2 ^ 59
def prefixEnd_5923667 : Nat := 4983230072969 + 3 ^ 40 * 5923667 * 2
def baseEnd_5923667 : Nat := 3041688408176980359320057

theorem tailTrace_5923667 : CollatzResearch.WordTrace tailWord_5923667 prefixEnd_5923667 3041688408176980359320057 := by
  unfold tailWord_5923667
  simp only [CollatzResearch.WordTrace]
  refine ⟨216053885030573615624609255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144035923353715743749739503 216053885030573615624609255)
  ·
    refine ⟨324080827545860423436913883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216053885030573615624609255 324080827545860423436913883)
    ·
      refine ⟨486121241318790635155370825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324080827545860423436913883 486121241318790635155370825)
      ·
        refine ⟨364590930989092976366528119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486121241318790635155370825 364590930989092976366528119)
        ·
          refine ⟨546886396483639464549792179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364590930989092976366528119 546886396483639464549792179)
          ·
            refine ⟨820329594725459196824688269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546886396483639464549792179 820329594725459196824688269)
            ·
              refine ⟨307623598022047198809258101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 820329594725459196824688269 307623598022047198809258101)
              ·
                refine ⟨28839712314566924888367947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 307623598022047198809258101 28839712314566924888367947)
                ·
                  refine ⟨43259568471850387332551921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28839712314566924888367947 43259568471850387332551921)
                  ·
                    refine ⟨32444676353887790499413941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43259568471850387332551921 32444676353887790499413941)
                    ·
                      refine ⟨3041688408176980359320057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32444676353887790499413941 3041688408176980359320057)
                      ·
                        rfl

theorem cell23_5923667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_5923667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923667 prefixEnd_5923667 := by exact prefixLift 5923667
  have htrace : WordTrace (prefixWord ++ tailWord_5923667) baseStart_5923667 baseEnd_5923667 := by
    simpa [prefixWord, tailWord_5923667, baseEnd_5923667] using wordTrace_append hprefix tailTrace_5923667
  have hstable : (prefixWord ++ tailWord_5923667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923667).length < 2 ^ (prefixWord ++ tailWord_5923667).sum := by decide
  have hdescent : baseEnd_5923667 < baseStart_5923667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923707 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 6]
def baseStart_5923707 : Nat := 118140960795 + 5923707 * 2 ^ 59
def prefixEnd_5923707 : Nat := 4983230072969 + 3 ^ 40 * 5923707 * 2
def baseEnd_5923707 : Nat := 3041708947403160202819873

theorem tailTrace_5923707 : CollatzResearch.WordTrace tailWord_5923707 prefixEnd_5923707 3041708947403160202819873 := by
  unfold tailWord_5923707
  simp only [CollatzResearch.WordTrace]
  refine ⟨216055343950428702456065375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144036895966952468304043583 216055343950428702456065375)
  ·
    refine ⟨324083015925643053684098063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216055343950428702456065375 324083015925643053684098063)
    ·
      refine ⟨486124523888464580526147095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324083015925643053684098063 486124523888464580526147095)
      ·
        refine ⟨729186785832696870789220643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486124523888464580526147095 729186785832696870789220643)
        ·
          refine ⟨1093780178749045306183830965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729186785832696870789220643 1093780178749045306183830965)
          ·
            refine ⟨102541891757722997454734153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1093780178749045306183830965 102541891757722997454734153)
            ·
              refine ⟨76906418818292248091050615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102541891757722997454734153 76906418818292248091050615)
              ·
                refine ⟨115359628227438372136575923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76906418818292248091050615 115359628227438372136575923)
                ·
                  refine ⟨173039442341157558204863885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115359628227438372136575923 173039442341157558204863885)
                  ·
                    refine ⟨64889790877934084326823957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173039442341157558204863885 64889790877934084326823957)
                    ·
                      refine ⟨3041708947403160202819873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64889790877934084326823957 3041708947403160202819873)
                      ·
                        rfl

theorem cell23_5923707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_5923707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923707 prefixEnd_5923707 := by exact prefixLift 5923707
  have htrace : WordTrace (prefixWord ++ tailWord_5923707) baseStart_5923707 baseEnd_5923707 := by
    simpa [prefixWord, tailWord_5923707, baseEnd_5923707] using wordTrace_append hprefix tailTrace_5923707
  have hstable : (prefixWord ++ tailWord_5923707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923707).length < 2 ^ (prefixWord ++ tailWord_5923707).sum := by decide
  have hdescent : baseEnd_5923707 < baseStart_5923707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923721 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 3, 4]
def baseStart_5923721 : Nat := 118140960795 + 5923721 * 2 ^ 59
def prefixEnd_5923721 : Nat := 4983230072969 + 3 ^ 40 * 5923721 * 2
def baseEnd_5923721 : Nat := 1013905378710774382681603

theorem tailTrace_5923721 : CollatzResearch.WordTrace tailWord_5923721 prefixEnd_5923721 1013905378710774382681603 := by
  unfold tailWord_5923721
  simp only [CollatzResearch.WordTrace]
  refine ⟨216055854572377982847075017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144037236381585321898050011 216055854572377982847075017)
  ·
    refine ⟨162041890929283487135306263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216055854572377982847075017 162041890929283487135306263)
    ·
      refine ⟨243062836393925230702959395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162041890929283487135306263 243062836393925230702959395)
      ·
        refine ⟨364594254590887846054439093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243062836393925230702959395 364594254590887846054439093)
        ·
          refine ⟨34180711367895735567603665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 364594254590887846054439093 34180711367895735567603665)
          ·
            refine ⟨25635533525921801675702749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34180711367895735567603665 25635533525921801675702749)
            ·
              refine ⟨9613325072220675628388531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25635533525921801675702749 9613325072220675628388531)
              ·
                refine ⟨14419987608331013442582797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9613325072220675628388531 14419987608331013442582797)
                ·
                  refine ⟨5407495353124130040968549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14419987608331013442582797 5407495353124130040968549)
                  ·
                    refine ⟨1013905378710774382681603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5407495353124130040968549 1013905378710774382681603)
                    ·
                      rfl

theorem cell23_5923721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 4].length) (baseStart_5923721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923721 prefixEnd_5923721 := by exact prefixLift 5923721
  have htrace : WordTrace (prefixWord ++ tailWord_5923721) baseStart_5923721 baseEnd_5923721 := by
    simpa [prefixWord, tailWord_5923721, baseEnd_5923721] using wordTrace_append hprefix tailTrace_5923721
  have hstable : (prefixWord ++ tailWord_5923721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923721).length < 2 ^ (prefixWord ++ tailWord_5923721).sum := by decide
  have hdescent : baseEnd_5923721 < baseStart_5923721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923744 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 3]
def baseStart_5923744 : Nat := 118140960795 + 5923744 * 2 ^ 59
def prefixEnd_5923744 : Nat := 4983230072969 + 3 ^ 40 * 5923744 * 2
def baseEnd_5923744 : Nat := 3041727946187376558057203

theorem tailTrace_5923744 : CollatzResearch.WordTrace tailWord_5923744 prefixEnd_5923744 3041727946187376558057203 := by
  unfold tailWord_5923744
  simp only [CollatzResearch.WordTrace]
  refine ⟨108028346725647328887581143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144037795634196438516774857 108028346725647328887581143)
  ·
    refine ⟨162042520088470993331371715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108028346725647328887581143 162042520088470993331371715)
    ·
      refine ⟨243063780132706489997057573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162042520088470993331371715 243063780132706489997057573)
      ·
        refine ⟨45574458774882466874448295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243063780132706489997057573 45574458774882466874448295)
        ·
          refine ⟨68361688162323700311672443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45574458774882466874448295 68361688162323700311672443)
          ·
            refine ⟨102542532243485550467508665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68361688162323700311672443 102542532243485550467508665)
            ·
              refine ⟨76906899182614162850631499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102542532243485550467508665 76906899182614162850631499)
              ·
                refine ⟨115360348773921244275947249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76906899182614162850631499 115360348773921244275947249)
                ·
                  refine ⟨86520261580440933206960437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115360348773921244275947249 86520261580440933206960437)
                  ·
                    refine ⟨8111274523166337488152541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86520261580440933206960437 8111274523166337488152541)
                    ·
                      refine ⟨3041727946187376558057203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8111274523166337488152541 3041727946187376558057203)
                      ·
                        rfl

theorem cell23_5923744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_5923744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923744 prefixEnd_5923744 := by exact prefixLift 5923744
  have htrace : WordTrace (prefixWord ++ tailWord_5923744) baseStart_5923744 baseEnd_5923744 := by
    simpa [prefixWord, tailWord_5923744, baseEnd_5923744] using wordTrace_append hprefix tailTrace_5923744
  have hstable : (prefixWord ++ tailWord_5923744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923744).length < 2 ^ (prefixWord ++ tailWord_5923744).sum := by decide
  have hdescent : baseEnd_5923744 < baseStart_5923744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923798 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_5923798 : Nat := 118140960795 + 5923798 * 2 ^ 59
def prefixEnd_5923798 : Nat := 4983230072969 + 3 ^ 40 * 5923798 * 2
def baseEnd_5923798 : Nat := 1013918558047573115593985

theorem tailTrace_5923798 : CollatzResearch.WordTrace tailWord_5923798 prefixEnd_5923798 1013918558047573115593985 := by
  unfold tailWord_5923798
  simp only [CollatzResearch.WordTrace]
  refine ⟨13503666437068689062351753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144039108662066016665085365 13503666437068689062351753)
  ·
    refine ⟨10127749827801516796763815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13503666437068689062351753 10127749827801516796763815)
    ·
      refine ⟨15191624741702275195145723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10127749827801516796763815 15191624741702275195145723)
      ·
        refine ⟨22787437112553412792718585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15191624741702275195145723 22787437112553412792718585)
        ·
          refine ⟨17090577834415059594538939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22787437112553412792718585 17090577834415059594538939)
          ·
            refine ⟨25635866751622589391808409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17090577834415059594538939 25635866751622589391808409)
            ·
              refine ⟨19226900063716942043856307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25635866751622589391808409 19226900063716942043856307)
              ·
                refine ⟨28840350095575413065784461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19226900063716942043856307 28840350095575413065784461)
                ·
                  refine ⟨10815131285840779899669173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28840350095575413065784461 10815131285840779899669173)
                  ·
                    refine ⟨1013918558047573115593985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10815131285840779899669173 1013918558047573115593985)
                    ·
                      rfl

theorem cell23_5923798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_5923798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923798 prefixEnd_5923798 := by exact prefixLift 5923798
  have htrace : WordTrace (prefixWord ++ tailWord_5923798) baseStart_5923798 baseEnd_5923798 := by
    simpa [prefixWord, tailWord_5923798, baseEnd_5923798] using wordTrace_append hprefix tailTrace_5923798
  have hstable : (prefixWord ++ tailWord_5923798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923798).length < 2 ^ (prefixWord ++ tailWord_5923798).sum := by decide
  have hdescent : baseEnd_5923798 < baseStart_5923798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923801 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 3, 1, 4]
def baseStart_5923801 : Nat := 118140960795 + 5923801 * 2 ^ 59
def prefixEnd_5923801 : Nat := 4983230072969 + 3 ^ 40 * 5923801 * 2
def baseEnd_5923801 : Nat := 3041757214584682835044441

theorem tailTrace_5923801 : CollatzResearch.WordTrace tailWord_5923801 prefixEnd_5923801 3041757214584682835044441 := by
  unfold tailWord_5923801
  simp only [CollatzResearch.WordTrace]
  refine ⟨216058772412088156509987257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144039181608058771006658171 216058772412088156509987257)
  ·
    refine ⟨162044079309066117382490443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216058772412088156509987257 162044079309066117382490443)
    ·
      refine ⟨243066118963599176073735665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162044079309066117382490443 243066118963599176073735665)
      ·
        refine ⟨182299589222699382055301749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243066118963599176073735665 182299589222699382055301749)
        ·
          refine ⟨17090586489628067067684539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182299589222699382055301749 17090586489628067067684539)
          ·
            refine ⟨25635879734442100601526809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17090586489628067067684539 25635879734442100601526809)
            ·
              refine ⟨19226909800831575451145107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25635879734442100601526809 19226909800831575451145107)
              ·
                refine ⟨28840364701247363176717661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19226909800831575451145107 28840364701247363176717661)
                ·
                  refine ⟨10815136762967761191269123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28840364701247363176717661 10815136762967761191269123)
                  ·
                    refine ⟨16222705144451641786903685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10815136762967761191269123 16222705144451641786903685)
                    ·
                      refine ⟨3041757214584682835044441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16222705144451641786903685 3041757214584682835044441)
                      ·
                        rfl

theorem cell23_5923801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_5923801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923801 prefixEnd_5923801 := by exact prefixLift 5923801
  have htrace : WordTrace (prefixWord ++ tailWord_5923801) baseStart_5923801 baseEnd_5923801 := by
    simpa [prefixWord, tailWord_5923801, baseEnd_5923801] using wordTrace_append hprefix tailTrace_5923801
  have hstable : (prefixWord ++ tailWord_5923801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923801).length < 2 ^ (prefixWord ++ tailWord_5923801).sum := by decide
  have hdescent : baseEnd_5923801 < baseStart_5923801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923805 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_5923805 : Nat := 118140960795 + 5923805 * 2 ^ 59
def prefixEnd_5923805 : Nat := 4983230072969 + 3 ^ 40 * 5923805 * 2
def baseEnd_5923805 : Nat := 3041759268507300819394423

theorem tailTrace_5923805 : CollatzResearch.WordTrace tailWord_5923805 prefixEnd_5923805 3041759268507300819394423 := by
  unfold tailWord_5923805
  simp only [CollatzResearch.WordTrace]
  refine ⟨216058918304073665193132869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144039278869382443462088579 216058918304073665193132869)
  ·
    refine ⟨40511047182013812223712413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216058918304073665193132869 40511047182013812223712413)
    ·
      refine ⟨15191642693255179583892155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40511047182013812223712413 15191642693255179583892155)
      ·
        refine ⟨22787464039882769375838233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15191642693255179583892155 22787464039882769375838233)
        ·
          refine ⟨17090598029912077031878675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22787464039882769375838233 17090598029912077031878675)
          ·
            refine ⟨25635897044868115547818013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17090598029912077031878675 25635897044868115547818013)
            ·
              refine ⟨9613461391825543330431755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25635897044868115547818013 9613461391825543330431755)
              ·
                refine ⟨14420192087738314995647633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9613461391825543330431755 14420192087738314995647633)
                ·
                  refine ⟨10815144065803736246735725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14420192087738314995647633 10815144065803736246735725)
                  ·
                    refine ⟨4055679024676401092525897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10815144065803736246735725 4055679024676401092525897)
                    ·
                      refine ⟨3041759268507300819394423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055679024676401092525897 3041759268507300819394423)
                      ·
                        rfl

theorem cell23_5923805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_5923805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923805 prefixEnd_5923805 := by exact prefixLift 5923805
  have htrace : WordTrace (prefixWord ++ tailWord_5923805) baseStart_5923805 baseEnd_5923805 := by
    simpa [prefixWord, tailWord_5923805, baseEnd_5923805] using wordTrace_append hprefix tailTrace_5923805
  have hstable : (prefixWord ++ tailWord_5923805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923805).length < 2 ^ (prefixWord ++ tailWord_5923805).sum := by decide
  have hdescent : baseEnd_5923805 < baseStart_5923805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923811 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 4, 4]
def baseStart_5923811 : Nat := 118140960795 + 5923811 * 2 ^ 59
def prefixEnd_5923811 : Nat := 4983230072969 + 3 ^ 40 * 5923811 * 2
def baseEnd_5923811 : Nat := 1013920783130409265306465

theorem tailTrace_5923811 : CollatzResearch.WordTrace tailWord_5923811 prefixEnd_5923811 1013920783130409265306465 := by
  unfold tailWord_5923811
  simp only [CollatzResearch.WordTrace]
  refine ⟨216059137142051928217851287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144039424761367952145234191 216059137142051928217851287)
  ·
    refine ⟨324088705713077892326776931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216059137142051928217851287 324088705713077892326776931)
    ·
      refine ⟨486133058569616838490165397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324088705713077892326776931 486133058569616838490165397)
      ·
        refine ⟨22787487120450789304226503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 486133058569616838490165397 22787487120450789304226503)
        ·
          refine ⟨34181230680676183956339755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22787487120450789304226503 34181230680676183956339755)
          ·
            refine ⟨51271846021014275934509633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34181230680676183956339755 51271846021014275934509633)
            ·
              refine ⟨38453884515760706950882225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51271846021014275934509633 38453884515760706950882225)
              ·
                refine ⟨28840413386820530213161669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38453884515760706950882225 28840413386820530213161669)
                ·
                  refine ⟨5407577510028849414967813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28840413386820530213161669 5407577510028849414967813)
                  ·
                    refine ⟨1013920783130409265306465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5407577510028849414967813 1013920783130409265306465)
                    ·
                      rfl

theorem cell23_5923811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 4].length) (baseStart_5923811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923811 prefixEnd_5923811 := by exact prefixLift 5923811
  have htrace : WordTrace (prefixWord ++ tailWord_5923811) baseStart_5923811 baseEnd_5923811 := by
    simpa [prefixWord, tailWord_5923811, baseEnd_5923811] using wordTrace_append hprefix tailTrace_5923811
  have hstable : (prefixWord ++ tailWord_5923811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923811).length < 2 ^ (prefixWord ++ tailWord_5923811).sum := by decide
  have hdescent : baseEnd_5923811 < baseStart_5923811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923815 : List Nat := [1, 1, 5, 2, 2, 3, 2, 1, 1, 5]
def baseStart_5923815 : Nat := 118140960795 + 5923815 * 2 ^ 59
def prefixEnd_5923815 : Nat := 4983230072969 + 3 ^ 40 * 5923815 * 2
def baseEnd_5923815 : Nat := 1013921467771281926756459

theorem tailTrace_5923815 : CollatzResearch.WordTrace tailWord_5923815 prefixEnd_5923815 1013921467771281926756459 := by
  unfold tailWord_5923815
  simp only [CollatzResearch.WordTrace]
  refine ⟨216059283034037436900996899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144039522022691624600664599 216059283034037436900996899)
  ·
    refine ⟨324088924551056155351495349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216059283034037436900996899 324088924551056155351495349)
    ·
      refine ⟨30383336676661514564202689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 324088924551056155351495349 30383336676661514564202689)
      ·
        refine ⟨22787502507496135923152017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30383336676661514564202689 22787502507496135923152017)
        ·
          refine ⟨17090626880622101942364013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22787502507496135923152017 17090626880622101942364013)
          ·
            refine ⟨6408985080233288228386505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17090626880622101942364013 6408985080233288228386505)
            ·
              refine ⟨4806738810174966171289879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6408985080233288228386505 4806738810174966171289879)
              ·
                refine ⟨7210108215262449256934819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4806738810174966171289879 7210108215262449256934819)
                ·
                  refine ⟨10815162322893673885402229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7210108215262449256934819 10815162322893673885402229)
                  ·
                    refine ⟨1013921467771281926756459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10815162322893673885402229 1013921467771281926756459)
                    ·
                      rfl

theorem cell23_5923815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_5923815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923815 prefixEnd_5923815 := by exact prefixLift 5923815
  have htrace : WordTrace (prefixWord ++ tailWord_5923815) baseStart_5923815 baseEnd_5923815 := by
    simpa [prefixWord, tailWord_5923815, baseEnd_5923815] using wordTrace_append hprefix tailTrace_5923815
  have hstable : (prefixWord ++ tailWord_5923815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923815).length < 2 ^ (prefixWord ++ tailWord_5923815).sum := by decide
  have hdescent : baseEnd_5923815 < baseStart_5923815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923818 : List Nat := [3, 1, 3, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_5923818 : Nat := 118140960795 + 5923818 * 2 ^ 59
def prefixEnd_5923818 : Nat := 4983230072969 + 3 ^ 40 * 5923818 * 2
def baseEnd_5923818 : Nat := 3041765943755809268531863

theorem tailTrace_5923818 : CollatzResearch.WordTrace tailWord_5923818 prefixEnd_5923818 3041765943755809268531863 := by
  unfold tailWord_5923818
  simp only [CollatzResearch.WordTrace]
  refine ⟨54014848113256642103339027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144039594968684378942237405 54014848113256642103339027)
  ·
    refine ⟨81022272169884963155008541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54014848113256642103339027 81022272169884963155008541)
    ·
      refine ⟨30383352063706861183128203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81022272169884963155008541 30383352063706861183128203)
      ·
        refine ⟨45575028095560291774692305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30383352063706861183128203 45575028095560291774692305)
        ·
          refine ⟨34181271071670218831019229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45575028095560291774692305 34181271071670218831019229)
          ·
            refine ⟨12817976651876332061632211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34181271071670218831019229 12817976651876332061632211)
            ·
              refine ⟨19226964977814498092448317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12817976651876332061632211 19226964977814498092448317)
              ·
                refine ⟨7210111866680436784668119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19226964977814498092448317 7210111866680436784668119)
                ·
                  refine ⟨10815167800020655177002179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7210111866680436784668119 10815167800020655177002179)
                  ·
                    refine ⟨16222751700030982765503269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10815167800020655177002179 16222751700030982765503269)
                    ·
                      refine ⟨3041765943755809268531863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16222751700030982765503269 3041765943755809268531863)
                      ·
                        rfl

theorem cell23_5923818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_5923818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923818 prefixEnd_5923818 := by exact prefixLift 5923818
  have htrace : WordTrace (prefixWord ++ tailWord_5923818) baseStart_5923818 baseEnd_5923818 := by
    simpa [prefixWord, tailWord_5923818, baseEnd_5923818] using wordTrace_append hprefix tailTrace_5923818
  have hstable : (prefixWord ++ tailWord_5923818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923818).length < 2 ^ (prefixWord ++ tailWord_5923818).sum := by decide
  have hdescent : baseEnd_5923818 < baseStart_5923818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923848 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_5923848 : Nat := 118140960795 + 5923848 * 2 ^ 59
def prefixEnd_5923848 : Nat := 4983230072969 + 3 ^ 40 * 5923848 * 2
def baseEnd_5923848 : Nat := 3041781348175444151156725

theorem tailTrace_5923848 : CollatzResearch.WordTrace tailWord_5923848 prefixEnd_5923848 3041781348175444151156725 := by
  unfold tailWord_5923848
  simp only [CollatzResearch.WordTrace]
  refine ⟨108030243321458941768474099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144040324428611922357965465 108030243321458941768474099)
  ·
    refine ⟨162045364982188412652711149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108030243321458941768474099 162045364982188412652711149)
    ·
      refine ⟨60767011868320654744766681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162045364982188412652711149 60767011868320654744766681)
      ·
        refine ⟨45575258901240491058575011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60767011868320654744766681 45575258901240491058575011)
        ·
          refine ⟨68362888351860736587862517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45575258901240491058575011 68362888351860736587862517)
          ·
            refine ⟨6409020782986944055112111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68362888351860736587862517 6409020782986944055112111)
            ·
              refine ⟨9613531174480416082668167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6409020782986944055112111 9613531174480416082668167)
              ·
                refine ⟨14420296761720624124002251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9613531174480416082668167 14420296761720624124002251)
                ·
                  refine ⟨21630445142580936186003377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14420296761720624124002251 21630445142580936186003377)
                  ·
                    refine ⟨16222833856935702139502533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21630445142580936186003377 16222833856935702139502533)
                    ·
                      refine ⟨3041781348175444151156725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16222833856935702139502533 3041781348175444151156725)
                      ·
                        rfl

theorem cell23_5923848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_5923848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923848 prefixEnd_5923848 := by exact prefixLift 5923848
  have htrace : WordTrace (prefixWord ++ tailWord_5923848) baseStart_5923848 baseEnd_5923848 := by
    simpa [prefixWord, tailWord_5923848, baseEnd_5923848] using wordTrace_append hprefix tailTrace_5923848
  have hstable : (prefixWord ++ tailWord_5923848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923848).length < 2 ^ (prefixWord ++ tailWord_5923848).sum := by decide
  have hdescent : baseEnd_5923848 < baseStart_5923848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923902 : List Nat := [4, 2, 1, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_5923902 : Nat := 118140960795 + 5923902 * 2 ^ 59
def prefixEnd_5923902 : Nat := 4983230072969 + 3 ^ 40 * 5923902 * 2
def baseEnd_5923902 : Nat := 3041809076130786939881477

theorem tailTrace_5923902 : CollatzResearch.WordTrace tailWord_5923902 prefixEnd_5923902 3041809076130786939881477 := by
  unfold tailWord_5923902
  simp only [CollatzResearch.WordTrace]
  refine ⟨27007807023090281344926745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144041637456481500506275973 27007807023090281344926745)
  ·
    refine ⟨20255855267317711008695059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27007807023090281344926745 20255855267317711008695059)
    ·
      refine ⟨30383782900976566513042589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20255855267317711008695059 30383782900976566513042589)
      ·
        refine ⟨11393918587866212442390971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30383782900976566513042589 11393918587866212442390971)
        ·
          refine ⟨17090877881799318663586457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11393918587866212442390971 17090877881799318663586457)
          ·
            refine ⟨12818158411349488997689843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17090877881799318663586457 12818158411349488997689843)
            ·
              refine ⟨19227237617024233496534765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12818158411349488997689843 19227237617024233496534765)
              ·
                refine ⟨7210214106384087561200537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19227237617024233496534765 7210214106384087561200537)
                ·
                  refine ⟨5407660579788065670900403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7210214106384087561200537 5407660579788065670900403)
                  ·
                    refine ⟨8111490869682098506350605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5407660579788065670900403 8111490869682098506350605)
                    ·
                      refine ⟨3041809076130786939881477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8111490869682098506350605 3041809076130786939881477)
                      ·
                        rfl

theorem cell23_5923902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_5923902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923902 prefixEnd_5923902 := by exact prefixLift 5923902
  have htrace : WordTrace (prefixWord ++ tailWord_5923902) baseStart_5923902 baseEnd_5923902 := by
    simpa [prefixWord, tailWord_5923902, baseEnd_5923902] using wordTrace_append hprefix tailTrace_5923902
  have hstable : (prefixWord ++ tailWord_5923902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923902).length < 2 ^ (prefixWord ++ tailWord_5923902).sum := by decide
  have hdescent : baseEnd_5923902 < baseStart_5923902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923911 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_5923911 : Nat := 118140960795 + 5923911 * 2 ^ 59
def prefixEnd_5923911 : Nat := 4983230072969 + 3 ^ 40 * 5923911 * 2
def baseEnd_5923911 : Nat := 3041813697456677404668935

theorem tailTrace_5923911 : CollatzResearch.WordTrace tailWord_5923911 prefixEnd_5923911 3041813697456677404668935 := by
  unfold tailWord_5923911
  simp only [CollatzResearch.WordTrace]
  refine ⟨216062784441689645296491587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144041856294459763530994391 216062784441689645296491587)
  ·
    refine ⟨324094176662534467944737381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216062784441689645296491587 324094176662534467944737381)
    ·
      refine ⟨60767658124225212739638259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 324094176662534467944737381 60767658124225212739638259)
      ·
        refine ⟨91151487186337819109457389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60767658124225212739638259 91151487186337819109457389)
        ·
          refine ⟨34181807694876682166046521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91151487186337819109457389 34181807694876682166046521)
          ·
            refine ⟨25636355771157511624534891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34181807694876682166046521 25636355771157511624534891)
            ·
              refine ⟨38454533656736267436802337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25636355771157511624534891 38454533656736267436802337)
              ·
                refine ⟨28840900242552200577601753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38454533656736267436802337 28840900242552200577601753)
                ·
                  refine ⟨21630675181914150433201315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28840900242552200577601753 21630675181914150433201315)
                  ·
                    refine ⟨32446012772871225649801973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21630675181914150433201315 32446012772871225649801973)
                    ·
                      refine ⟨3041813697456677404668935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32446012772871225649801973 3041813697456677404668935)
                      ·
                        rfl

theorem cell23_5923911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_5923911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923911 prefixEnd_5923911 := by exact prefixLift 5923911
  have htrace : WordTrace (prefixWord ++ tailWord_5923911) baseStart_5923911 baseEnd_5923911 := by
    simpa [prefixWord, tailWord_5923911, baseEnd_5923911] using wordTrace_append hprefix tailTrace_5923911
  have hstable : (prefixWord ++ tailWord_5923911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923911).length < 2 ^ (prefixWord ++ tailWord_5923911).sum := by decide
  have hdescent : baseEnd_5923911 < baseStart_5923911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5923948 : List Nat := [2, 2, 1, 1, 3, 2, 3, 4, 5]
def baseStart_5923948 : Nat := 118140960795 + 5923948 * 2 ^ 59
def prefixEnd_5923948 : Nat := 4983230072969 + 3 ^ 40 * 5923948 * 2
def baseEnd_5923948 : Nat := 337981410693432639989585

theorem tailTrace_5923948 : CollatzResearch.WordTrace tailWord_5923948 prefixEnd_5923948 337981410693432639989585 := by
  unfold tailWord_5923948
  simp only [CollatzResearch.WordTrace]
  refine ⟨108032066971277800307794249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144042755961703733743725665 108032066971277800307794249)
  ·
    refine ⟨81024050228458350230845687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108032066971277800307794249 81024050228458350230845687)
    ·
      refine ⟨121536075342687525346268531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81024050228458350230845687 121536075342687525346268531)
      ·
        refine ⟨182304113014031288019402797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121536075342687525346268531 182304113014031288019402797)
        ·
          refine ⟨68364042380261733007276049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182304113014031288019402797 68364042380261733007276049)
          ·
            refine ⟨51273031785196299755457037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68364042380261733007276049 51273031785196299755457037)
            ·
              refine ⟨19227386919448612408296389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51273031785196299755457037 19227386919448612408296389)
              ·
                refine ⟨3605135047396614826555573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19227386919448612408296389 3605135047396614826555573)
                ·
                  refine ⟨337981410693432639989585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3605135047396614826555573 337981410693432639989585)
                  ·
                    rfl

theorem cell23_5923948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 5].length) (baseStart_5923948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5923948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5923948 prefixEnd_5923948 := by exact prefixLift 5923948
  have htrace : WordTrace (prefixWord ++ tailWord_5923948) baseStart_5923948 baseEnd_5923948 := by
    simpa [prefixWord, tailWord_5923948, baseEnd_5923948] using wordTrace_append hprefix tailTrace_5923948
  have hstable : (prefixWord ++ tailWord_5923948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5923948).length < 2 ^ (prefixWord ++ tailWord_5923948).sum := by decide
  have hdescent : baseEnd_5923948 < baseStart_5923948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5923948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924018 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_5924018 : Nat := 118140960795 + 5924018 * 2 ^ 59
def prefixEnd_5924018 : Nat := 4983230072969 + 3 ^ 40 * 5924018 * 2
def baseEnd_5924018 : Nat := 3041868639886708486030943

theorem tailTrace_5924018 : CollatzResearch.WordTrace tailWord_5924018 prefixEnd_5924018 3041868639886708486030943 := by
  unfold tailWord_5924018
  simp only [CollatzResearch.WordTrace]
  refine ⟨54016671763075500642659177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144044458034868001713757805 54016671763075500642659177)
  ·
    refine ⟨40512503822306625481994383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54016671763075500642659177 40512503822306625481994383)
    ·
      refine ⟨60768755733459938222991575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40512503822306625481994383 60768755733459938222991575)
      ·
        refine ⟨91153133600189907334487363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60768755733459938222991575 91153133600189907334487363)
        ·
          refine ⟨136729700400284861001731045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91153133600189907334487363 136729700400284861001731045)
          ·
            refine ⟨25636818825053411437824571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136729700400284861001731045 25636818825053411437824571)
            ·
              refine ⟨38455228237580117156736857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25636818825053411437824571 38455228237580117156736857)
              ·
                refine ⟨28841421178185087867552643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38455228237580117156736857 28841421178185087867552643)
                ·
                  refine ⟨43262131767277631801328965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28841421178185087867552643 43262131767277631801328965)
                  ·
                    refine ⟨8111649706364555962749181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43262131767277631801328965 8111649706364555962749181)
                    ·
                      refine ⟨3041868639886708486030943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8111649706364555962749181 3041868639886708486030943)
                      ·
                        rfl

theorem cell23_5924018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_5924018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924018 prefixEnd_5924018 := by exact prefixLift 5924018
  have htrace : WordTrace (prefixWord ++ tailWord_5924018) baseStart_5924018 baseEnd_5924018 := by
    simpa [prefixWord, tailWord_5924018, baseEnd_5924018] using wordTrace_append hprefix tailTrace_5924018
  have hstable : (prefixWord ++ tailWord_5924018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924018).length < 2 ^ (prefixWord ++ tailWord_5924018).sum := by decide
  have hdescent : baseEnd_5924018 < baseStart_5924018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924042 : List Nat := [3, 1, 2, 1, 3, 2, 3, 3, 1, 4]
def baseStart_5924042 : Nat := 118140960795 + 5924042 * 2 ^ 59
def prefixEnd_5924042 : Nat := 4983230072969 + 3 ^ 40 * 5924042 * 2
def baseEnd_5924042 : Nat := 1013960321140805464043611

theorem tailTrace_5924042 : CollatzResearch.WordTrace tailWord_5924042 prefixEnd_5924042 1013960321140805464043611 := by
  unfold tailWord_5924042
  simp only [CollatzResearch.WordTrace]
  refine ⟨54016890601053763667377595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144045041602810036446340253 54016890601053763667377595)
  ·
    refine ⟨81025335901580645501066393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54016890601053763667377595 81025335901580645501066393)
    ·
      refine ⟨60769001926185484125799795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81025335901580645501066393 60769001926185484125799795)
      ·
        refine ⟨91153502889278226188699693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60769001926185484125799795 91153502889278226188699693)
        ·
          refine ⟨34182563583479334820762385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91153502889278226188699693 34182563583479334820762385)
          ·
            refine ⟨25636922687609501115571789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34182563583479334820762385 25636922687609501115571789)
            ·
              refine ⟨9613846007853562918339421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25636922687609501115571789 9613846007853562918339421)
              ·
                refine ⟨3605192252945086094377283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9613846007853562918339421 3605192252945086094377283)
                ·
                  refine ⟨5407788379417629141565925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3605192252945086094377283 5407788379417629141565925)
                  ·
                    refine ⟨1013960321140805464043611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5407788379417629141565925 1013960321140805464043611)
                    ·
                      rfl

theorem cell23_5924042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_5924042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924042 prefixEnd_5924042 := by exact prefixLift 5924042
  have htrace : WordTrace (prefixWord ++ tailWord_5924042) baseStart_5924042 baseEnd_5924042 := by
    simpa [prefixWord, tailWord_5924042, baseEnd_5924042] using wordTrace_append hprefix tailTrace_5924042
  have hstable : (prefixWord ++ tailWord_5924042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924042).length < 2 ^ (prefixWord ++ tailWord_5924042).sum := by decide
  have hdescent : baseEnd_5924042 < baseStart_5924042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924091 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 5]
def baseStart_5924091 : Nat := 118140960795 + 5924091 * 2 ^ 59
def prefixEnd_5924091 : Nat := 4983230072969 + 3 ^ 40 * 5924091 * 2
def baseEnd_5924091 : Nat := 3041906123974486700418107

theorem tailTrace_5924091 : CollatzResearch.WordTrace tailWord_5924091 prefixEnd_5924091 3041906123974486700418107 := by
  unfold tailWord_5924091
  simp only [CollatzResearch.WordTrace]
  refine ⟨216069349581037536038044127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144046233054025024025362751 216069349581037536038044127)
  ·
    refine ⟨324104024371556304057066191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216069349581037536038044127 324104024371556304057066191)
    ·
      refine ⟨486156036557334456085599287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324104024371556304057066191 486156036557334456085599287)
      ·
        refine ⟨729234054836001684128398931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486156036557334456085599287 729234054836001684128398931)
        ·
          refine ⟨1093851082254002526192598397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729234054836001684128398931 1093851082254002526192598397)
          ·
            refine ⟨410194155845250947322224399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1093851082254002526192598397 410194155845250947322224399)
            ·
              refine ⟨615291233767876420983336599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410194155845250947322224399 615291233767876420983336599)
              ·
                refine ⟨922936850651814631475004899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615291233767876420983336599 922936850651814631475004899)
                ·
                  refine ⟨1384405275977721947212507349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 922936850651814631475004899 1384405275977721947212507349)
                  ·
                    refine ⟨32446998655727858137793141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1384405275977721947212507349 32446998655727858137793141)
                    ·
                      refine ⟨3041906123974486700418107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32446998655727858137793141 3041906123974486700418107)
                      ·
                        rfl

theorem cell23_5924091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 5].length) (baseStart_5924091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924091 prefixEnd_5924091 := by exact prefixLift 5924091
  have htrace : WordTrace (prefixWord ++ tailWord_5924091) baseStart_5924091 baseEnd_5924091 := by
    simpa [prefixWord, tailWord_5924091, baseEnd_5924091] using wordTrace_append hprefix tailTrace_5924091
  have hstable : (prefixWord ++ tailWord_5924091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924091).length < 2 ^ (prefixWord ++ tailWord_5924091).sum := by decide
  have hdescent : baseEnd_5924091 < baseStart_5924091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924145 : List Nat := [1, 2, 2, 3, 3, 2, 3, 7]
def baseStart_5924145 : Nat := 118140960795 + 5924145 * 2 ^ 59
def prefixEnd_5924145 : Nat := 4983230072969 + 3 ^ 40 * 5924145 * 2
def baseEnd_5924145 : Nat := 112664216738141832931217

theorem tailTrace_5924145 : CollatzResearch.WordTrace tailWord_5924145 prefixEnd_5924145 112664216738141832931217 := by
  unfold tailWord_5924145
  simp only [CollatzResearch.WordTrace]
  refine ⟨216071319122841903260509889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144047546081894602173673259 216071319122841903260509889)
  ·
    refine ⟨162053489342131427445382417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216071319122841903260509889 162053489342131427445382417)
    ·
      refine ⟨121540117006598570584036813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162053489342131427445382417 121540117006598570584036813)
      ·
        refine ⟨45577543877474463969013805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121540117006598570584036813 45577543877474463969013805)
        ·
          refine ⟨17091578954052923988380177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45577543877474463969013805 17091578954052923988380177)
          ·
            refine ⟨12818684215539692991285133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17091578954052923988380177 12818684215539692991285133)
            ·
              refine ⟨4807006580827384871731925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12818684215539692991285133 4807006580827384871731925)
              ·
                refine ⟨112664216738141832931217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4807006580827384871731925 112664216738141832931217)
                ·
                  rfl

theorem cell23_5924145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 7].length) (baseStart_5924145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924145 prefixEnd_5924145 := by exact prefixLift 5924145
  have htrace : WordTrace (prefixWord ++ tailWord_5924145) baseStart_5924145 baseEnd_5924145 := by
    simpa [prefixWord, tailWord_5924145, baseEnd_5924145] using wordTrace_append hprefix tailTrace_5924145
  have hstable : (prefixWord ++ tailWord_5924145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924145).length < 2 ^ (prefixWord ++ tailWord_5924145).sum := by decide
  have hdescent : baseEnd_5924145 < baseStart_5924145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924156 : List Nat := [2, 2, 2, 2, 1, 4, 2, 3, 1, 2, 2]
def baseStart_5924156 : Nat := 118140960795 + 5924156 * 2 ^ 59
def prefixEnd_5924156 : Nat := 4983230072969 + 3 ^ 40 * 5924156 * 2
def baseEnd_5924156 : Nat := 3041939500217028946105309

theorem tailTrace_5924156 : CollatzResearch.WordTrace tailWord_5924156 prefixEnd_5924156 3041939500217028946105309 := by
  unfold tailWord_5924156
  simp only [CollatzResearch.WordTrace]
  refine ⟨108035860162901026069580161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144047813550534701426106881 108035860162901026069580161)
  ·
    refine ⟨81026895122175769552185121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108035860162901026069580161 81026895122175769552185121)
    ·
      refine ⟨60770171341631827164138841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81026895122175769552185121 60770171341631827164138841)
      ·
        refine ⟨45577628506223870373104131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60770171341631827164138841 45577628506223870373104131)
        ·
          refine ⟨68366442759335805559656197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45577628506223870373104131 68366442759335805559656197)
          ·
            refine ⟨12818708017375463542435537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68366442759335805559656197 12818708017375463542435537)
            ·
              refine ⟨9614031013031597656826653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12818708017375463542435537 9614031013031597656826653)
              ·
                refine ⟨3605261629886849121309995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9614031013031597656826653 3605261629886849121309995)
                ·
                  refine ⟨5407892444830273681964993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3605261629886849121309995 5407892444830273681964993)
                  ·
                    refine ⟨4055919333622705261473745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5407892444830273681964993 4055919333622705261473745)
                    ·
                      refine ⟨3041939500217028946105309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055919333622705261473745 3041939500217028946105309)
                      ·
                        rfl

theorem cell23_5924156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_5924156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924156 prefixEnd_5924156 := by exact prefixLift 5924156
  have htrace : WordTrace (prefixWord ++ tailWord_5924156) baseStart_5924156 baseEnd_5924156 := by
    simpa [prefixWord, tailWord_5924156, baseEnd_5924156] using wordTrace_append hprefix tailTrace_5924156
  have hstable : (prefixWord ++ tailWord_5924156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924156).length < 2 ^ (prefixWord ++ tailWord_5924156).sum := by decide
  have hdescent : baseEnd_5924156 < baseStart_5924156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924159 : List Nat := [1, 1, 2, 2, 4, 4, 2, 1, 1, 2, 3]
def baseStart_5924159 : Nat := 118140960795 + 5924159 * 2 ^ 59
def prefixEnd_5924159 : Nat := 4983230072969 + 3 ^ 40 * 5924159 * 2
def baseEnd_5924159 : Nat := 3041941040658992434367795

theorem tailTrace_5924159 : CollatzResearch.WordTrace tailWord_5924159 prefixEnd_5924159 3041941040658992434367795 := by
  unfold tailWord_5924159
  simp only [CollatzResearch.WordTrace]
  refine ⟨216071829744791183651519531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144047886496527455767679687 216071829744791183651519531)
  ·
    refine ⟨324107744617186775477279297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216071829744791183651519531 324107744617186775477279297)
    ·
      refine ⟨243080808462890081607959473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324107744617186775477279297 243080808462890081607959473)
      ·
        refine ⟨182310606347167561205969605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243080808462890081607959473 182310606347167561205969605)
        ·
          refine ⟨34183238690093917726119301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182310606347167561205969605 34183238690093917726119301)
          ·
            refine ⟨6409357254392609573647369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34183238690093917726119301 6409357254392609573647369)
            ·
              refine ⟨4807017940794457180235527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6409357254392609573647369 4807017940794457180235527)
              ·
                refine ⟨7210526911191685770353291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4807017940794457180235527 7210526911191685770353291)
                ·
                  refine ⟨10815790366787528655529937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7210526911191685770353291 10815790366787528655529937)
                  ·
                    refine ⟨8111842775090646491647453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10815790366787528655529937 8111842775090646491647453)
                    ·
                      refine ⟨3041941040658992434367795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8111842775090646491647453 3041941040658992434367795)
                      ·
                        rfl

theorem cell23_5924159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 1, 2, 3].length) (baseStart_5924159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924159 prefixEnd_5924159 := by exact prefixLift 5924159
  have htrace : WordTrace (prefixWord ++ tailWord_5924159) baseStart_5924159 baseEnd_5924159 := by
    simpa [prefixWord, tailWord_5924159, baseEnd_5924159] using wordTrace_append hprefix tailTrace_5924159
  have hstable : (prefixWord ++ tailWord_5924159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924159).length < 2 ^ (prefixWord ++ tailWord_5924159).sum := by decide
  have hdescent : baseEnd_5924159 < baseStart_5924159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924166 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_5924166 : Nat := 118140960795 + 5924166 * 2 ^ 59
def prefixEnd_5924166 : Nat := 4983230072969 + 3 ^ 40 * 5924166 * 2
def baseEnd_5924166 : Nat := 1013981545007857968993421

theorem tailTrace_5924166 : CollatzResearch.WordTrace tailWord_5924166 prefixEnd_5924166 1013981545007857968993421 := by
  unfold tailWord_5924166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6752252657992681995219511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 144048056703843882564682901 6752252657992681995219511)
  ·
    refine ⟨10128378986989022992829267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6752252657992681995219511 10128378986989022992829267)
    ·
      refine ⟨15192568480483534489243901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10128378986989022992829267 15192568480483534489243901)
      ·
        refine ⟨5697213180181325433466463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15192568480483534489243901 5697213180181325433466463)
        ·
          refine ⟨8545819770271988150199695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5697213180181325433466463 8545819770271988150199695)
          ·
            refine ⟨12818729655407982225299543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8545819770271988150199695 12818729655407982225299543)
            ·
              refine ⟨19228094483111973337949315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12818729655407982225299543 19228094483111973337949315)
              ·
                refine ⟨28842141724667960006923973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19228094483111973337949315 28842141724667960006923973)
                ·
                  refine ⟨5407901573375242501298245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28842141724667960006923973 5407901573375242501298245)
                  ·
                    refine ⟨1013981545007857968993421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5407901573375242501298245 1013981545007857968993421)
                    ·
                      rfl

theorem cell23_5924166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_5924166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924166 prefixEnd_5924166 := by exact prefixLift 5924166
  have htrace : WordTrace (prefixWord ++ tailWord_5924166) baseStart_5924166 baseEnd_5924166 := by
    simpa [prefixWord, tailWord_5924166, baseEnd_5924166] using wordTrace_append hprefix tailTrace_5924166
  have hstable : (prefixWord ++ tailWord_5924166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924166).length < 2 ^ (prefixWord ++ tailWord_5924166).sum := by decide
  have hdescent : baseEnd_5924166 < baseStart_5924166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924172 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 4, 1, 3]
def baseStart_5924172 : Nat := 118140960795 + 5924172 * 2 ^ 59
def prefixEnd_5924172 : Nat := 4983230072969 + 3 ^ 40 * 5924172 * 2
def baseEnd_5924172 : Nat := 3041947715907500883505235

theorem tailTrace_5924172 : CollatzResearch.WordTrace tailWord_5924172 prefixEnd_5924172 3041947715907500883505235 := by
  unfold tailWord_5924172
  simp only [CollatzResearch.WordTrace]
  refine ⟨108036151946872043435871385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144048202595829391247828513 108036151946872043435871385)
  ·
    refine ⟨81027113960154032576903539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108036151946872043435871385 81027113960154032576903539)
    ·
      refine ⟨121540670940231048865355309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81027113960154032576903539 121540670940231048865355309)
      ·
        refine ⟨45577751602586643324508241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121540670940231048865355309 45577751602586643324508241)
        ·
          refine ⟨34183313701939982493381181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45577751602586643324508241 34183313701939982493381181)
          ·
            refine ⟨12818742638227493435017943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34183313701939982493381181 12818742638227493435017943)
            ·
              refine ⟨19228113957341240152526915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12818742638227493435017943 19228113957341240152526915)
              ·
                refine ⟨28842170936011860228790373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19228113957341240152526915 28842170936011860228790373)
                ·
                  refine ⟨5407907050502223792898195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28842170936011860228790373 5407907050502223792898195)
                  ·
                    refine ⟨8111860575753335689347293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5407907050502223792898195 8111860575753335689347293)
                    ·
                      refine ⟨3041947715907500883505235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8111860575753335689347293 3041947715907500883505235)
                      ·
                        rfl

theorem cell23_5924172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_5924172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924172 prefixEnd_5924172 := by exact prefixLift 5924172
  have htrace : WordTrace (prefixWord ++ tailWord_5924172) baseStart_5924172 baseEnd_5924172 := by
    simpa [prefixWord, tailWord_5924172, baseEnd_5924172] using wordTrace_append hprefix tailTrace_5924172
  have hstable : (prefixWord ++ tailWord_5924172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924172).length < 2 ^ (prefixWord ++ tailWord_5924172).sum := by decide
  have hdescent : baseEnd_5924172 < baseStart_5924172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924173 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_5924173 : Nat := 118140960795 + 5924173 * 2 ^ 59
def prefixEnd_5924173 : Nat := 4983230072969 + 3 ^ 40 * 5924173 * 2
def baseEnd_5924173 : Nat := 3041948229388155379592731

theorem tailTrace_5924173 : CollatzResearch.WordTrace tailWord_5924173 prefixEnd_5924173 3041948229388155379592731 := by
  unfold tailWord_5924173
  simp only [CollatzResearch.WordTrace]
  refine ⟨216072340366740464042529173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144048226911160309361686115 216072340366740464042529173)
  ·
    refine ⟨10128390954690959251993555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 216072340366740464042529173 10128390954690959251993555)
    ·
      refine ⟨15192586432036438877990333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10128390954690959251993555 15192586432036438877990333)
      ·
        refine ⟨5697219912013664579246375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15192586432036438877990333 5697219912013664579246375)
        ·
          refine ⟨8545829868020496868869563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5697219912013664579246375 8545829868020496868869563)
          ·
            refine ⟨12818744802030745303304345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8545829868020496868869563 12818744802030745303304345)
            ·
              refine ⟨9614058601523058977478259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12818744802030745303304345 9614058601523058977478259)
              ·
                refine ⟨14421087902284588466217389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9614058601523058977478259 14421087902284588466217389)
                ·
                  refine ⟨5407907963356720674831521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14421087902284588466217389 5407907963356720674831521)
                  ·
                    refine ⟨4055930972517540506123641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5407907963356720674831521 4055930972517540506123641)
                    ·
                      refine ⟨3041948229388155379592731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4055930972517540506123641 3041948229388155379592731)
                      ·
                        rfl

theorem cell23_5924173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_5924173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924173 prefixEnd_5924173 := by exact prefixLift 5924173
  have htrace : WordTrace (prefixWord ++ tailWord_5924173) baseStart_5924173 baseEnd_5924173 := by
    simpa [prefixWord, tailWord_5924173, baseEnd_5924173] using wordTrace_append hprefix tailTrace_5924173
  have hstable : (prefixWord ++ tailWord_5924173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924173).length < 2 ^ (prefixWord ++ tailWord_5924173).sum := by decide
  have hdescent : baseEnd_5924173 < baseStart_5924173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924245 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_5924245 : Nat := 118140960795 + 5924245 * 2 ^ 59
def prefixEnd_5924245 : Nat := 4983230072969 + 3 ^ 40 * 5924245 * 2
def baseEnd_5924245 : Nat := 3041985199995279097892399

theorem tailTrace_5924245 : CollatzResearch.WordTrace tailWord_5924245 prefixEnd_5924245 3041985199995279097892399 := by
  unfold tailWord_5924245
  simp only [CollatzResearch.WordTrace]
  refine ⟨216074966422479620339150189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144049977614986413559433459 216074966422479620339150189)
  ·
    refine ⟨81028112408429857627181321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216074966422479620339150189 81028112408429857627181321)
    ·
      refine ⟨60771084306322393220385991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81028112408429857627181321 60771084306322393220385991)
      ·
        refine ⟨91156626459483589830578987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60771084306322393220385991 91156626459483589830578987)
        ·
          refine ⟨136734939689225384745868481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91156626459483589830578987 136734939689225384745868481)
          ·
            refine ⟨102551204766919038559401361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136734939689225384745868481 102551204766919038559401361)
            ·
              refine ⟨76913403575189278919551021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102551204766919038559401361 76913403575189278919551021)
              ·
                refine ⟨28842526340695979594831633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76913403575189278919551021 28842526340695979594831633)
                ·
                  refine ⟨21631894755521984696123725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28842526340695979594831633 21631894755521984696123725)
                  ·
                    refine ⟨8111960533320744261046397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21631894755521984696123725 8111960533320744261046397)
                    ·
                      refine ⟨3041985199995279097892399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8111960533320744261046397 3041985199995279097892399)
                      ·
                        rfl

theorem cell23_5924245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_5924245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924245 prefixEnd_5924245 := by exact prefixLift 5924245
  have htrace : WordTrace (prefixWord ++ tailWord_5924245) baseStart_5924245 baseEnd_5924245 := by
    simpa [prefixWord, tailWord_5924245, baseEnd_5924245] using wordTrace_append hprefix tailTrace_5924245
  have hstable : (prefixWord ++ tailWord_5924245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924245).length < 2 ^ (prefixWord ++ tailWord_5924245).sum := by decide
  have hdescent : baseEnd_5924245 < baseStart_5924245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924292 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_5924292 : Nat := 118140960795 + 5924292 * 2 ^ 59
def prefixEnd_5924292 : Nat := 4983230072969 + 3 ^ 40 * 5924292 * 2
def baseEnd_5924292 : Nat := 3042009333586040414004683

theorem tailTrace_5924292 : CollatzResearch.WordTrace tailWord_5924292 prefixEnd_5924292 3042009333586040414004683 := by
  unfold tailWord_5924292
  simp only [CollatzResearch.WordTrace]
  refine ⟨108038340326654673683055565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144051120435539564910740753 108038340326654673683055565)
  ·
    refine ⟨40514377622495502631145837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108038340326654673683055565 40514377622495502631145837)
    ·
      refine ⟨15192891608435813486679689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40514377622495502631145837 15192891608435813486679689)
      ·
        refine ⟨11394668706326860115009767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15192891608435813486679689 11394668706326860115009767)
        ·
          refine ⟨17092003059490290172514651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11394668706326860115009767 17092003059490290172514651)
          ·
            refine ⟨25638004589235435258771977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17092003059490290172514651 25638004589235435258771977)
            ·
              refine ⟨19228503441926576444078983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25638004589235435258771977 19228503441926576444078983)
              ·
                refine ⟨28842755162889864666118475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19228503441926576444078983 28842755162889864666118475)
                ·
                  refine ⟨43264132744334796999177713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28842755162889864666118475 43264132744334796999177713)
                  ·
                    refine ⟨32448099558251097749383285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43264132744334796999177713 32448099558251097749383285)
                    ·
                      refine ⟨3042009333586040414004683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32448099558251097749383285 3042009333586040414004683)
                      ·
                        rfl

theorem cell23_5924292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_5924292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924292 prefixEnd_5924292 := by exact prefixLift 5924292
  have htrace : WordTrace (prefixWord ++ tailWord_5924292) baseStart_5924292 baseEnd_5924292 := by
    simpa [prefixWord, tailWord_5924292, baseEnd_5924292] using wordTrace_append hprefix tailTrace_5924292
  have hstable : (prefixWord ++ tailWord_5924292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924292).length < 2 ^ (prefixWord ++ tailWord_5924292).sum := by decide
  have hdescent : baseEnd_5924292 < baseStart_5924292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924302 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2]
def baseStart_5924302 : Nat := 118140960795 + 5924302 * 2 ^ 59
def prefixEnd_5924302 : Nat := 4983230072969 + 3 ^ 40 * 5924302 * 2
def baseEnd_5924302 : Nat := 3042014468392585374879637

theorem tailTrace_5924302 : CollatzResearch.WordTrace tailWord_5924302 prefixEnd_5924302 3042014468392585374879637 := by
  unfold tailWord_5924302
  simp only [CollatzResearch.WordTrace]
  refine ⟨27009630672909139884246895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144051363588848746049316773 27009630672909139884246895)
  ·
    refine ⟨40514446009363709826370343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27009630672909139884246895 40514446009363709826370343)
    ·
      refine ⟨60771669014045564739555515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40514446009363709826370343 60771669014045564739555515)
      ·
        refine ⟨91157503521068347109333273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60771669014045564739555515 91157503521068347109333273)
        ·
          refine ⟨68368127640801260331999955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91157503521068347109333273 68368127640801260331999955)
          ·
            refine ⟨102552191461201890497999933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68368127640801260331999955 102552191461201890497999933)
            ·
              refine ⟨38457071797950708936749975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102552191461201890497999933 38457071797950708936749975)
              ·
                refine ⟨57685607696926063405124963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38457071797950708936749975 57685607696926063405124963)
                ·
                  refine ⟨86528411545389095107687445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57685607696926063405124963 86528411545389095107687445)
                  ·
                    refine ⟨4056019291190113833172849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86528411545389095107687445 4056019291190113833172849)
                    ·
                      refine ⟨3042014468392585374879637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4056019291190113833172849 3042014468392585374879637)
                      ·
                        rfl

theorem cell23_5924302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_5924302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924302 prefixEnd_5924302 := by exact prefixLift 5924302
  have htrace : WordTrace (prefixWord ++ tailWord_5924302) baseStart_5924302 baseEnd_5924302 := by
    simpa [prefixWord, tailWord_5924302, baseEnd_5924302] using wordTrace_append hprefix tailTrace_5924302
  have hstable : (prefixWord ++ tailWord_5924302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924302).length < 2 ^ (prefixWord ++ tailWord_5924302).sum := by decide
  have hdescent : baseEnd_5924302 < baseStart_5924302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924342 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_5924342 : Nat := 118140960795 + 5924342 * 2 ^ 59
def prefixEnd_5924342 : Nat := 4983230072969 + 3 ^ 40 * 5924342 * 2
def baseEnd_5924342 : Nat := 338003889735418357597717

theorem tailTrace_5924342 : CollatzResearch.WordTrace tailWord_5924342 prefixEnd_5924342 338003889735418357597717 := by
  unfold tailWord_5924342
  simp only [CollatzResearch.WordTrace]
  refine ⟨13504906518945512869089455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144052336202085470603620853 13504906518945512869089455)
  ·
    refine ⟨20257359778418269303634183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13504906518945512869089455 20257359778418269303634183)
    ·
      refine ⟨30386039667627403955451275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20257359778418269303634183 30386039667627403955451275)
      ·
        refine ⟨45579059501441105933176913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30386039667627403955451275 45579059501441105933176913)
        ·
          refine ⟨34184294626080829449882685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45579059501441105933176913 34184294626080829449882685)
          ·
            refine ⟨12819110484780311043706007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34184294626080829449882685 12819110484780311043706007)
            ·
              refine ⟨19228665727170466565559011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12819110484780311043706007 19228665727170466565559011)
              ·
                refine ⟨28842998590755699848338517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19228665727170466565559011 28842998590755699848338517)
                ·
                  refine ⟨338003889735418357597717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28842998590755699848338517 338003889735418357597717)
                  ·
                    rfl

theorem cell23_5924342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_5924342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924342 prefixEnd_5924342 := by exact prefixLift 5924342
  have htrace : WordTrace (prefixWord ++ tailWord_5924342) baseStart_5924342 baseEnd_5924342 := by
    simpa [prefixWord, tailWord_5924342, baseEnd_5924342] using wordTrace_append hprefix tailTrace_5924342
  have hstable : (prefixWord ++ tailWord_5924342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924342).length < 2 ^ (prefixWord ++ tailWord_5924342).sum := by decide
  have hdescent : baseEnd_5924342 < baseStart_5924342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924355 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 3, 5]
def baseStart_5924355 : Nat := 118140960795 + 5924355 * 2 ^ 59
def prefixEnd_5924355 : Nat := 4983230072969 + 3 ^ 40 * 5924355 * 2
def baseEnd_5924355 : Nat := 1014013894289091222505631

theorem tailTrace_5924355 : CollatzResearch.WordTrace tailWord_5924355 prefixEnd_5924355 1014013894289091222505631 := by
  unfold tailWord_5924355
  simp only [CollatzResearch.WordTrace]
  refine ⟨216078978452081109125654519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144052652301387406083769679 216078978452081109125654519)
  ·
    refine ⟨324118467678121663688481779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216078978452081109125654519 324118467678121663688481779)
    ·
      refine ⟨486177701517182495532722669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324118467678121663688481779 486177701517182495532722669)
      ·
        refine ⟨182316638068943435824771001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 486177701517182495532722669 182316638068943435824771001)
        ·
          refine ⟨136737478551707576868578251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182316638068943435824771001 136737478551707576868578251)
          ·
            refine ⟨205106217827561365302867377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136737478551707576868578251 205106217827561365302867377)
            ·
              refine ⟨153829663370671023977150533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205106217827561365302867377 153829663370671023977150533)
              ·
                refine ⟨28843061882000816995715725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153829663370671023977150533 28843061882000816995715725)
                ·
                  refine ⟨10816148205750306373393397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28843061882000816995715725 10816148205750306373393397)
                  ·
                    refine ⟨1014013894289091222505631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10816148205750306373393397 1014013894289091222505631)
                    ·
                      rfl

theorem cell23_5924355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 5].length) (baseStart_5924355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924355 prefixEnd_5924355 := by exact prefixLift 5924355
  have htrace : WordTrace (prefixWord ++ tailWord_5924355) baseStart_5924355 baseEnd_5924355 := by
    simpa [prefixWord, tailWord_5924355, baseEnd_5924355] using wordTrace_append hprefix tailTrace_5924355
  have hstable : (prefixWord ++ tailWord_5924355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924355).length < 2 ^ (prefixWord ++ tailWord_5924355).sum := by decide
  have hdescent : baseEnd_5924355 < baseStart_5924355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924359 : List Nat := [1, 1, 4, 3, 2, 2, 3, 1, 6]
def baseStart_5924359 : Nat := 118140960795 + 5924359 * 2 ^ 59
def prefixEnd_5924359 : Nat := 4983230072969 + 3 ^ 40 * 5924359 * 2
def baseEnd_5924359 : Nat := 338004859643321294651875

theorem tailTrace_5924359 : CollatzResearch.WordTrace tailWord_5924359 prefixEnd_5924359 338004859643321294651875 := by
  unfold tailWord_5924359
  simp only [CollatzResearch.WordTrace]
  refine ⟨216079124344066617808800131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144052749562711078539200087 216079124344066617808800131)
  ·
    refine ⟨324118686516099926713200197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216079124344066617808800131 324118686516099926713200197)
    ·
      refine ⟨60772253721768736258725037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 324118686516099926713200197 60772253721768736258725037)
      ·
        refine ⟨22789595145663276097021889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60772253721768736258725037 22789595145663276097021889)
        ·
          refine ⟨17092196359247457072766417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22789595145663276097021889 17092196359247457072766417)
          ·
            refine ⟨12819147269435592804574813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17092196359247457072766417 12819147269435592804574813)
            ·
              refine ⟨4807180226038347301715555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12819147269435592804574813 4807180226038347301715555)
              ·
                refine ⟨7210770339057520952573333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4807180226038347301715555 7210770339057520952573333)
                ·
                  refine ⟨338004859643321294651875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7210770339057520952573333 338004859643321294651875)
                  ·
                    rfl

theorem cell23_5924359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 6].length) (baseStart_5924359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924359 prefixEnd_5924359 := by exact prefixLift 5924359
  have htrace : WordTrace (prefixWord ++ tailWord_5924359) baseStart_5924359 baseEnd_5924359 := by
    simpa [prefixWord, tailWord_5924359, baseEnd_5924359] using wordTrace_append hprefix tailTrace_5924359
  have hstable : (prefixWord ++ tailWord_5924359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924359).length < 2 ^ (prefixWord ++ tailWord_5924359).sum := by decide
  have hdescent : baseEnd_5924359 < baseStart_5924359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924403 : List Nat := [1, 1, 1, 2, 4, 4, 3, 2, 1, 1, 3]
def baseStart_5924403 : Nat := 118140960795 + 5924403 * 2 ^ 59
def prefixEnd_5924403 : Nat := 4983230072969 + 3 ^ 40 * 5924403 * 2
def baseEnd_5924403 : Nat := 3042066329938689479716673

theorem tailTrace_5924403 : CollatzResearch.WordTrace tailWord_5924403 prefixEnd_5924403 3042066329938689479716673 := by
  unfold tailWord_5924403
  simp only [CollatzResearch.WordTrace]
  refine ⟨216080729155907213323401863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144053819437271475548934575 216080729155907213323401863)
  ·
    refine ⟨324121093733860819985102795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216080729155907213323401863 324121093733860819985102795)
    ·
      refine ⟨486181640600791229977654193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324121093733860819985102795 486181640600791229977654193)
      ·
        refine ⟨364636230450593422483240645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486181640600791229977654193 364636230450593422483240645)
        ·
          refine ⟨68369293209486266715607621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 364636230450593422483240645 68369293209486266715607621)
          ·
            refine ⟨12819242476778675009176429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68369293209486266715607621 12819242476778675009176429)
            ·
              refine ⟨4807215928792003128441161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12819242476778675009176429 4807215928792003128441161)
              ·
                refine ⟨3605411946594002346330871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807215928792003128441161 3605411946594002346330871)
                ·
                  refine ⟨5408117919891003519496307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3605411946594002346330871 5408117919891003519496307)
                  ·
                    refine ⟨8112176879836505279244461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5408117919891003519496307 8112176879836505279244461)
                    ·
                      refine ⟨3042066329938689479716673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8112176879836505279244461 3042066329938689479716673)
                      ·
                        rfl

theorem cell23_5924403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 1, 1, 3].length) (baseStart_5924403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924403 prefixEnd_5924403 := by exact prefixLift 5924403
  have htrace : WordTrace (prefixWord ++ tailWord_5924403) baseStart_5924403 baseEnd_5924403 := by
    simpa [prefixWord, tailWord_5924403, baseEnd_5924403] using wordTrace_append hprefix tailTrace_5924403
  have hstable : (prefixWord ++ tailWord_5924403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924403).length < 2 ^ (prefixWord ++ tailWord_5924403).sum := by decide
  have hdescent : baseEnd_5924403 < baseStart_5924403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924415 : List Nat := [1, 1, 2, 2, 3, 3, 1, 10]
def baseStart_5924415 : Nat := 118140960795 + 5924415 * 2 ^ 59
def prefixEnd_5924415 : Nat := 4983230072969 + 3 ^ 40 * 5924415 * 2
def baseEnd_5924415 : Nat := 112669351544686793806171

theorem tailTrace_5924415 : CollatzResearch.WordTrace tailWord_5924415 prefixEnd_5924415 112669351544686793806171 := by
  unfold tailWord_5924415
  simp only [CollatzResearch.WordTrace]
  refine ⟨216081166831863739372838699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144054111221242492915225799 216081166831863739372838699)
  ·
    refine ⟨324121750247795609059258049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216081166831863739372838699 324121750247795609059258049)
    ·
      refine ⟨243091312685846706794443537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324121750247795609059258049 243091312685846706794443537)
      ·
        refine ⟨182318484514385030095832653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243091312685846706794443537 182318484514385030095832653)
        ·
          refine ⟨68369431692894386285937245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182318484514385030095832653 68369431692894386285937245)
          ·
            refine ⟨25638536884835394857226467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68369431692894386285937245 25638536884835394857226467)
            ·
              refine ⟨38457805327253092285839701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25638536884835394857226467 38457805327253092285839701)
              ·
                refine ⟨112669351544686793806171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38457805327253092285839701 112669351544686793806171)
                ·
                  rfl

theorem cell23_5924415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 10].length) (baseStart_5924415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924415 prefixEnd_5924415 := by exact prefixLift 5924415
  have htrace : WordTrace (prefixWord ++ tailWord_5924415) baseStart_5924415 baseEnd_5924415 := by
    simpa [prefixWord, tailWord_5924415, baseEnd_5924415] using wordTrace_append hprefix tailTrace_5924415
  have hstable : (prefixWord ++ tailWord_5924415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924415).length < 2 ^ (prefixWord ++ tailWord_5924415).sum := by decide
  have hdescent : baseEnd_5924415 < baseStart_5924415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924503 : List Nat := [1, 1, 3, 3, 2, 2, 4, 1, 1, 3, 2]
def baseStart_5924503 : Nat := 118140960795 + 5924503 * 2 ^ 59
def prefixEnd_5924503 : Nat := 4983230072969 + 3 ^ 40 * 5924503 * 2
def baseEnd_5924503 : Nat := 3042117678004139088466213

theorem tailTrace_5924503 : CollatzResearch.WordTrace tailWord_5924503 prefixEnd_5924503 3042117678004139088466213 := by
  unfold tailWord_5924503
  simp only [CollatzResearch.WordTrace]
  refine ⟨216084376455544930402042163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144056250970363286934694775 216084376455544930402042163)
  ·
    refine ⟨324126564683317395603063245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216084376455544930402042163 324126564683317395603063245)
    ·
      refine ⟨121547461756244023351148717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324126564683317395603063245 121547461756244023351148717)
      ·
        refine ⟨45580298158591508756680769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121547461756244023351148717 45580298158591508756680769)
        ·
          refine ⟨34185223618943631567510577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45580298158591508756680769 34185223618943631567510577)
          ·
            refine ⟨25638917714207723675632933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34185223618943631567510577 25638917714207723675632933)
            ·
              refine ⟨4807297071413948189181175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25638917714207723675632933 4807297071413948189181175)
              ·
                refine ⟨7210945607120922283771763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4807297071413948189181175 7210945607120922283771763)
                ·
                  refine ⟨10816418410681383425657645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7210945607120922283771763 10816418410681383425657645)
                  ·
                    refine ⟨4056156904005518784621617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10816418410681383425657645 4056156904005518784621617)
                    ·
                      refine ⟨3042117678004139088466213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4056156904005518784621617 3042117678004139088466213)
                      ·
                        rfl

theorem cell23_5924503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_5924503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924503 prefixEnd_5924503 := by exact prefixLift 5924503
  have htrace : WordTrace (prefixWord ++ tailWord_5924503) baseStart_5924503 baseEnd_5924503 := by
    simpa [prefixWord, tailWord_5924503, baseEnd_5924503] using wordTrace_append hprefix tailTrace_5924503
  have hstable : (prefixWord ++ tailWord_5924503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924503).length < 2 ^ (prefixWord ++ tailWord_5924503).sum := by decide
  have hdescent : baseEnd_5924503 < baseStart_5924503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924510 : List Nat := [4, 3, 1, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_5924510 : Nat := 118140960795 + 5924510 * 2 ^ 59
def prefixEnd_5924510 : Nat := 4983230072969 + 3 ^ 40 * 5924510 * 2
def baseEnd_5924510 : Nat := 3042121272368720561078681

theorem tailTrace_5924510 : CollatzResearch.WordTrace tailWord_5924510 prefixEnd_5924510 3042121272368720561078681 := by
  unfold tailWord_5924510
  simp only [CollatzResearch.WordTrace]
  refine ⟨27010578970814946324693373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144056421177679713731697989 27010578970814946324693373)
  ·
    refine ⟨10128967114055604871760015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27010578970814946324693373 10128967114055604871760015)
    ·
      refine ⟨15193450671083407307640023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10128967114055604871760015 15193450671083407307640023)
      ·
        refine ⟨22790176006625110961460035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15193450671083407307640023 22790176006625110961460035)
        ·
          refine ⟨34185264009937666442190053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22790176006625110961460035 34185264009937666442190053)
          ·
            refine ⟨6409737001863312457910635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34185264009937666442190053 6409737001863312457910635)
            ·
              refine ⟨9614605502794968686865953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6409737001863312457910635 9614605502794968686865953)
              ·
                refine ⟨7210954127096226515149465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9614605502794968686865953 7210954127096226515149465)
                ·
                  refine ⟨5408215595322169886362099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7210954127096226515149465 5408215595322169886362099)
                  ·
                    refine ⟨8112323392983254829543149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5408215595322169886362099 8112323392983254829543149)
                    ·
                      refine ⟨3042121272368720561078681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8112323392983254829543149 3042121272368720561078681)
                      ·
                        rfl

theorem cell23_5924510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_5924510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924510 prefixEnd_5924510 := by exact prefixLift 5924510
  have htrace : WordTrace (prefixWord ++ tailWord_5924510) baseStart_5924510 baseEnd_5924510 := by
    simpa [prefixWord, tailWord_5924510, baseEnd_5924510] using wordTrace_append hprefix tailTrace_5924510
  have hstable : (prefixWord ++ tailWord_5924510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924510).length < 2 ^ (prefixWord ++ tailWord_5924510).sum := by decide
  have hdescent : baseEnd_5924510 < baseStart_5924510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924552 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 1, 7]
def baseStart_5924552 : Nat := 118140960795 + 5924552 * 2 ^ 59
def prefixEnd_5924552 : Nat := 4983230072969 + 3 ^ 40 * 5924552 * 2
def baseEnd_5924552 : Nat := 1014047612852069798917829

theorem tailTrace_5924552 : CollatzResearch.WordTrace tailWord_5924552 prefixEnd_5924552 1014047612852069798917829 := by
  unfold tailWord_5924552
  simp only [CollatzResearch.WordTrace]
  refine ⟨108043081816183705885287955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144057442421578274513717273 108043081816183705885287955)
  ·
    refine ⟨162064622724275558827931933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108043081816183705885287955 162064622724275558827931933)
    ·
      refine ⟨60774233521603334560474475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162064622724275558827931933 60774233521603334560474475)
      ·
        refine ⟨91161350282405001840711713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60774233521603334560474475 91161350282405001840711713)
        ·
          refine ⟨68371012711803751380533785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91161350282405001840711713 68371012711803751380533785)
          ·
            refine ⟨51278259533852813535400339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68371012711803751380533785 51278259533852813535400339)
            ·
              refine ⟨76917389300779220303100509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51278259533852813535400339 76917389300779220303100509)
              ·
                refine ⟨28844020987792207613662691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76917389300779220303100509 28844020987792207613662691)
                ·
                  refine ⟨43266031481688311420494037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28844020987792207613662691 43266031481688311420494037)
                  ·
                    refine ⟨1014047612852069798917829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43266031481688311420494037 1014047612852069798917829)
                    ·
                      rfl

theorem cell23_5924552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_5924552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924552 prefixEnd_5924552 := by exact prefixLift 5924552
  have htrace : WordTrace (prefixWord ++ tailWord_5924552) baseStart_5924552 baseEnd_5924552 := by
    simpa [prefixWord, tailWord_5924552, baseEnd_5924552] using wordTrace_append hprefix tailTrace_5924552
  have hstable : (prefixWord ++ tailWord_5924552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924552).length < 2 ^ (prefixWord ++ tailWord_5924552).sum := by decide
  have hdescent : baseEnd_5924552 < baseStart_5924552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924569 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 2, 5]
def baseStart_5924569 : Nat := 118140960795 + 5924569 * 2 ^ 59
def prefixEnd_5924569 : Nat := 4983230072969 + 3 ^ 40 * 5924569 * 2
def baseEnd_5924569 : Nat := 1014050522575778610080303

theorem tailTrace_5924569 : CollatzResearch.WordTrace tailWord_5924569 prefixEnd_5924569 1014050522575778610080303 := by
  unfold tailWord_5924569
  simp only [CollatzResearch.WordTrace]
  refine ⟨216086783673305823673944761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144057855782203882449296507 216086783673305823673944761)
  ·
    refine ⟨162065087754979367755458571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216086783673305823673944761 162065087754979367755458571)
    ·
      refine ⟨243097631632469051633187857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162065087754979367755458571 243097631632469051633187857)
      ·
        refine ⟨182323223724351788724890893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243097631632469051633187857 182323223724351788724890893)
        ·
          refine ⟨68371208896631920771834085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182323223724351788724890893 68371208896631920771834085)
          ·
            refine ⟨12819601668118485144718891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68371208896631920771834085 12819601668118485144718891)
            ·
              refine ⟨19229402502177727717078337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12819601668118485144718891 19229402502177727717078337)
              ·
                refine ⟨14422051876633295787808753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19229402502177727717078337 14422051876633295787808753)
                ·
                  refine ⟨10816538907474971840856565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14422051876633295787808753 10816538907474971840856565)
                  ·
                    refine ⟨1014050522575778610080303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10816538907474971840856565 1014050522575778610080303)
                    ·
                      rfl

theorem cell23_5924569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 5].length) (baseStart_5924569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924569 prefixEnd_5924569 := by exact prefixLift 5924569
  have htrace : WordTrace (prefixWord ++ tailWord_5924569) baseStart_5924569 baseEnd_5924569 := by
    simpa [prefixWord, tailWord_5924569, baseEnd_5924569] using wordTrace_append hprefix tailTrace_5924569
  have hstable : (prefixWord ++ tailWord_5924569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924569).length < 2 ^ (prefixWord ++ tailWord_5924569).sum := by decide
  have hdescent : baseEnd_5924569 < baseStart_5924569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924573 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 7]
def baseStart_5924573 : Nat := 118140960795 + 5924573 * 2 ^ 59
def prefixEnd_5924573 : Nat := 4983230072969 + 3 ^ 40 * 5924573 * 2
def baseEnd_5924573 : Nat := 338017069072217090510099

theorem tailTrace_5924573 : CollatzResearch.WordTrace tailWord_5924573 prefixEnd_5924573 338017069072217090510099 := by
  unfold tailWord_5924573
  simp only [CollatzResearch.WordTrace]
  refine ⟨216086929565291332357090373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144057953043527554904726915 216086929565291332357090373)
  ·
    refine ⟨40516299293492124816954445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216086929565291332357090373 40516299293492124816954445)
    ·
      refine ⟨15193612235059546806357917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40516299293492124816954445 15193612235059546806357917)
      ·
        refine ⟨5697604588147330052384219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15193612235059546806357917 5697604588147330052384219)
        ·
          refine ⟨8546406882220995078576329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5697604588147330052384219 8546406882220995078576329)
          ·
            refine ⟨6409805161665746308932247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8546406882220995078576329 6409805161665746308932247)
            ·
              refine ⟨9614707742498619463398371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6409805161665746308932247 9614707742498619463398371)
              ·
                refine ⟨14422061613747929195097557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9614707742498619463398371 14422061613747929195097557)
                ·
                  refine ⟨338017069072217090510099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14422061613747929195097557 338017069072217090510099)
                  ·
                    rfl

theorem cell23_5924573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_5924573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924573 prefixEnd_5924573 := by exact prefixLift 5924573
  have htrace : WordTrace (prefixWord ++ tailWord_5924573) baseStart_5924573 baseEnd_5924573 := by
    simpa [prefixWord, tailWord_5924573, baseEnd_5924573] using wordTrace_append hprefix tailTrace_5924573
  have hstable : (prefixWord ++ tailWord_5924573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924573).length < 2 ^ (prefixWord ++ tailWord_5924573).sum := by decide
  have hdescent : baseEnd_5924573 < baseStart_5924573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924599 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 3, 4]
def baseStart_5924599 : Nat := 118140960795 + 5924599 * 2 ^ 59
def prefixEnd_5924599 : Nat := 4983230072969 + 3 ^ 40 * 5924599 * 2
def baseEnd_5924599 : Nat := 1014055657382323570955257

theorem tailTrace_5924599 : CollatzResearch.WordTrace tailWord_5924599 prefixEnd_5924599 1014055657382323570955257 := by
  unfold tailWord_5924599
  simp only [CollatzResearch.WordTrace]
  refine ⟨216087877863197138797536851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144058585242131425865024567 216087877863197138797536851)
  ·
    refine ⟨324131816794795708196305277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216087877863197138797536851 324131816794795708196305277)
    ·
      refine ⟨121549431298048390573614479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324131816794795708196305277 121549431298048390573614479)
      ·
        refine ⟨182324146947072585860421719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121549431298048390573614479 182324146947072585860421719)
        ·
          refine ⟨273486220420608878790632579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182324146947072585860421719 273486220420608878790632579)
          ·
            refine ⟨410229330630913318185948869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273486220420608878790632579 410229330630913318185948869)
            ·
              refine ⟨76917999493296247159865413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 410229330630913318185948869 76917999493296247159865413)
              ·
                refine ⟨14422124904993046342474765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76917999493296247159865413 14422124904993046342474765)
                ·
                  refine ⟨5408296839372392378428037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14422124904993046342474765 5408296839372392378428037)
                  ·
                    refine ⟨1014055657382323570955257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5408296839372392378428037 1014055657382323570955257)
                    ·
                      rfl

theorem cell23_5924599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_5924599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924599 prefixEnd_5924599 := by exact prefixLift 5924599
  have htrace : WordTrace (prefixWord ++ tailWord_5924599) baseStart_5924599 baseEnd_5924599 := by
    simpa [prefixWord, tailWord_5924599, baseEnd_5924599] using wordTrace_append hprefix tailTrace_5924599
  have hstable : (prefixWord ++ tailWord_5924599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924599).length < 2 ^ (prefixWord ++ tailWord_5924599).sum := by decide
  have hdescent : baseEnd_5924599 < baseStart_5924599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924602 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_5924602 : Nat := 118140960795 + 5924602 * 2 ^ 59
def prefixEnd_5924602 : Nat := 4983230072969 + 3 ^ 40 * 5924602 * 2
def baseEnd_5924602 : Nat := 3042168512588934201128257

theorem tailTrace_5924602 : CollatzResearch.WordTrace tailWord_5924602 prefixEnd_5924602 3042168512588934201128257 := by
  unfold tailWord_5924602
  simp only [CollatzResearch.WordTrace]
  refine ⟨54021996820546567577474015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144058658188124180206597373 54021996820546567577474015)
  ·
    refine ⟨81032995230819851366211023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54021996820546567577474015 81032995230819851366211023)
    ·
      refine ⟨121549492846229777049316535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81032995230819851366211023 121549492846229777049316535)
      ·
        refine ⟨182324239269344665573974803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121549492846229777049316535 182324239269344665573974803)
        ·
          refine ⟨273486358904016998360962205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182324239269344665573974803 273486358904016998360962205)
          ·
            refine ⟨102557384589006374385360827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273486358904016998360962205 102557384589006374385360827)
            ·
              refine ⟨153836076883509561578041241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102557384589006374385360827 153836076883509561578041241)
              ·
                refine ⟨115377057662632171183530931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153836076883509561578041241 115377057662632171183530931)
                ·
                  refine ⟨173065586493948256775296397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115377057662632171183530931 173065586493948256775296397)
                  ·
                    refine ⟨64899594935230596290736149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173065586493948256775296397 64899594935230596290736149)
                    ·
                      refine ⟨3042168512588934201128257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64899594935230596290736149 3042168512588934201128257)
                      ·
                        rfl

theorem cell23_5924602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_5924602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924602 prefixEnd_5924602 := by exact prefixLift 5924602
  have htrace : WordTrace (prefixWord ++ tailWord_5924602) baseStart_5924602 baseEnd_5924602 := by
    simpa [prefixWord, tailWord_5924602, baseEnd_5924602] using wordTrace_append hprefix tailTrace_5924602
  have hstable : (prefixWord ++ tailWord_5924602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924602).length < 2 ^ (prefixWord ++ tailWord_5924602).sum := by decide
  have hdescent : baseEnd_5924602 < baseStart_5924602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924609 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_5924609 : Nat := 118140960795 + 5924609 * 2 ^ 59
def prefixEnd_5924609 : Nat := 4983230072969 + 3 ^ 40 * 5924609 * 2
def baseEnd_5924609 : Nat := 3042172106953515673740725

theorem tailTrace_5924609 : CollatzResearch.WordTrace tailWord_5924609 prefixEnd_5924609 3042172106953515673740725 := by
  unfold tailWord_5924609
  simp only [CollatzResearch.WordTrace]
  refine ⟨216088242593160910505400881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144058828395440607003600587 216088242593160910505400881)
  ·
    refine ⟨162066181944870682879050661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216088242593160910505400881 162066181944870682879050661)
    ·
      refine ⟨30387409114663253039821999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162066181944870682879050661 30387409114663253039821999)
      ·
        refine ⟨45581113671994879559732999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30387409114663253039821999 45581113671994879559732999)
        ·
          refine ⟨68371670507992319339599499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45581113671994879559732999 68371670507992319339599499)
          ·
            refine ⟨102557505761988479009399249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68371670507992319339599499 102557505761988479009399249)
            ·
              refine ⟨76918129321491359257049437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102557505761988479009399249 76918129321491359257049437)
              ·
                refine ⟨28844298495559259721393539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76918129321491359257049437 28844298495559259721393539)
                ·
                  refine ⟨43266447743338889582090309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28844298495559259721393539 43266447743338889582090309)
                  ·
                    refine ⟨8112458951876041796641933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43266447743338889582090309 8112458951876041796641933)
                    ·
                      refine ⟨3042172106953515673740725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8112458951876041796641933 3042172106953515673740725)
                      ·
                        rfl

theorem cell23_5924609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_5924609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924609 prefixEnd_5924609 := by exact prefixLift 5924609
  have htrace : WordTrace (prefixWord ++ tailWord_5924609) baseStart_5924609 baseEnd_5924609 := by
    simpa [prefixWord, tailWord_5924609, baseEnd_5924609] using wordTrace_append hprefix tailTrace_5924609
  have hstable : (prefixWord ++ tailWord_5924609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924609).length < 2 ^ (prefixWord ++ tailWord_5924609).sum := by decide
  have hdescent : baseEnd_5924609 < baseStart_5924609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924629 : List Nat := [1, 3, 2, 1, 2, 3, 1, 4, 6]
def baseStart_5924629 : Nat := 118140960795 + 5924629 * 2 ^ 59
def prefixEnd_5924629 : Nat := 4983230072969 + 3 ^ 40 * 5924629 * 2
def baseEnd_5924629 : Nat := 338020264062956177276737

theorem tailTrace_5924629 : CollatzResearch.WordTrace tailWord_5924629 prefixEnd_5924629 338020264062956177276737 := by
  unfold tailWord_5924629
  simp only [CollatzResearch.WordTrace]
  refine ⟨216088972053088453921128941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144059314702058969280752627 216088972053088453921128941)
  ·
    refine ⟨81033364519908170220423353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216088972053088453921128941 81033364519908170220423353)
    ·
      refine ⟨60775023389931127665317515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81033364519908170220423353 60775023389931127665317515)
      ·
        refine ⟨91162535084896691497976273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60775023389931127665317515 91162535084896691497976273)
        ·
          refine ⟨68371901313672518623482205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91162535084896691497976273 68371901313672518623482205)
          ·
            refine ⟨25639462992627194483805827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68371901313672518623482205 25639462992627194483805827)
            ·
              refine ⟨38459194488940791725708741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25639462992627194483805827 38459194488940791725708741)
              ·
                refine ⟨7211098966676398448570389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38459194488940791725708741 7211098966676398448570389)
                ·
                  refine ⟨338020264062956177276737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7211098966676398448570389 338020264062956177276737)
                  ·
                    rfl

theorem cell23_5924629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_5924629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924629 prefixEnd_5924629 := by exact prefixLift 5924629
  have htrace : WordTrace (prefixWord ++ tailWord_5924629) baseStart_5924629 baseEnd_5924629 := by
    simpa [prefixWord, tailWord_5924629, baseEnd_5924629] using wordTrace_append hprefix tailTrace_5924629
  have hstable : (prefixWord ++ tailWord_5924629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924629).length < 2 ^ (prefixWord ++ tailWord_5924629).sum := by decide
  have hdescent : baseEnd_5924629 < baseStart_5924629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924660 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_5924660 : Nat := 118140960795 + 5924660 * 2 ^ 59
def prefixEnd_5924660 : Nat := 4983230072969 + 3 ^ 40 * 5924660 * 2
def baseEnd_5924660 : Nat := 3042198294466894974202991

theorem tailTrace_5924660 : CollatzResearch.WordTrace tailWord_5924660 prefixEnd_5924660 3042198294466894974202991 := by
  unfold tailWord_5924660
  simp only [CollatzResearch.WordTrace]
  refine ⟨108045051357988073107753717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144060068477317430810338289 108045051357988073107753717)
  ·
    refine ⟨10129223564811381853851911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108045051357988073107753717 10129223564811381853851911)
    ·
      refine ⟨15193835347217072780777867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10129223564811381853851911 15193835347217072780777867)
      ·
        refine ⟨22790753020825609171166801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15193835347217072780777867 22790753020825609171166801)
        ·
          refine ⟨17093064765619206878375101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22790753020825609171166801 17093064765619206878375101)
          ·
            refine ⟨6409899287107202579390663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17093064765619206878375101 6409899287107202579390663)
            ·
              refine ⟨9614848930660803869085995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6409899287107202579390663 9614848930660803869085995)
              ·
                refine ⟨14422273395991205803628993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9614848930660803869085995 14422273395991205803628993)
                ·
                  refine ⟨10816705046993404352721745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14422273395991205803628993 10816705046993404352721745)
                  ·
                    refine ⟨8112528785245053264541309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10816705046993404352721745 8112528785245053264541309)
                    ·
                      refine ⟨3042198294466894974202991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8112528785245053264541309 3042198294466894974202991)
                      ·
                        rfl

theorem cell23_5924660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_5924660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924660 prefixEnd_5924660 := by exact prefixLift 5924660
  have htrace : WordTrace (prefixWord ++ tailWord_5924660) baseStart_5924660 baseEnd_5924660 := by
    simpa [prefixWord, tailWord_5924660, baseEnd_5924660] using wordTrace_append hprefix tailTrace_5924660
  have hstable : (prefixWord ++ tailWord_5924660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924660).length < 2 ^ (prefixWord ++ tailWord_5924660).sum := by decide
  have hdescent : baseEnd_5924660 < baseStart_5924660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924690 : List Nat := [3, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_5924690 : Nat := 118140960795 + 5924690 * 2 ^ 59
def prefixEnd_5924690 : Nat := 4983230072969 + 3 ^ 40 * 5924690 * 2
def baseEnd_5924690 : Nat := 3042213698886529856827853

theorem tailTrace_5924690 : CollatzResearch.WordTrace tailWord_5924690 prefixEnd_5924690 3042213698886529856827853 := by
  unfold tailWord_5924690
  simp only [CollatzResearch.WordTrace]
  refine ⟨54022799226466865334774881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144060797937244974226066349 54022799226466865334774881)
  ·
    refine ⟨40517099419850149001081161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54022799226466865334774881 40517099419850149001081161)
    ·
      refine ⟨30387824564887611750810871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40517099419850149001081161 30387824564887611750810871)
      ·
        refine ⟨45581736847331417626216307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30387824564887611750810871 45581736847331417626216307)
        ·
          refine ⟨68372605270997126439324461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45581736847331417626216307 68372605270997126439324461)
          ·
            refine ⟨25639726976623922414746673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68372605270997126439324461 25639726976623922414746673)
            ·
              refine ⟨19229795232467941811060005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25639726976623922414746673 19229795232467941811060005)
              ·
                refine ⟨3605586606087739089573751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19229795232467941811060005 3605586606087739089573751)
                ·
                  refine ⟨5408379909131608634360627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3605586606087739089573751 5408379909131608634360627)
                  ·
                    refine ⟨8112569863697412951540941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5408379909131608634360627 8112569863697412951540941)
                    ·
                      refine ⟨3042213698886529856827853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8112569863697412951540941 3042213698886529856827853)
                      ·
                        rfl

theorem cell23_5924690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_5924690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924690 prefixEnd_5924690 := by exact prefixLift 5924690
  have htrace : WordTrace (prefixWord ++ tailWord_5924690) baseStart_5924690 baseEnd_5924690 := by
    simpa [prefixWord, tailWord_5924690, baseEnd_5924690] using wordTrace_append hprefix tailTrace_5924690
  have hstable : (prefixWord ++ tailWord_5924690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924690).length < 2 ^ (prefixWord ++ tailWord_5924690).sum := by decide
  have hdescent : baseEnd_5924690 < baseStart_5924690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924767 : List Nat := [1, 1, 2, 5, 4, 1, 1, 2, 1, 2, 3]
def baseStart_5924767 : Nat := 118140960795 + 5924767 * 2 ^ 59
def prefixEnd_5924767 : Nat := 4983230072969 + 3 ^ 40 * 5924767 * 2
def baseEnd_5924767 : Nat := 3042253236896926055564999

theorem tailTrace_5924767 : CollatzResearch.WordTrace tailWord_5924767 prefixEnd_5924767 3042253236896926055564999 := by
  unfold tailWord_5924767
  simp only [CollatzResearch.WordTrace]
  refine ⟨216094005326588503489652555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144062670217725668993101703 216094005326588503489652555)
  ·
    refine ⟨324141007989882755234478833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216094005326588503489652555 324141007989882755234478833)
    ·
      refine ⟨243105755992412066425859125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324141007989882755234478833 243105755992412066425859125)
      ·
        refine ⟨22791164624288631227424293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 243105755992412066425859125 22791164624288631227424293)
        ·
          refine ⟨4273343367054118355142055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22791164624288631227424293 4273343367054118355142055)
          ·
            refine ⟨6410015050581177532713083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273343367054118355142055 6410015050581177532713083)
            ·
              refine ⟨9615022575871766299069625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6410015050581177532713083 9615022575871766299069625)
              ·
                refine ⟨7211266931903824724302219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9615022575871766299069625 7211266931903824724302219)
                ·
                  refine ⟨10816900397855737086453329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7211266931903824724302219 10816900397855737086453329)
                  ·
                    refine ⟨8112675298391802814839997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10816900397855737086453329 8112675298391802814839997)
                    ·
                      refine ⟨3042253236896926055564999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8112675298391802814839997 3042253236896926055564999)
                      ·
                        rfl

theorem cell23_5924767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_5924767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924767 prefixEnd_5924767 := by exact prefixLift 5924767
  have htrace : WordTrace (prefixWord ++ tailWord_5924767) baseStart_5924767 baseEnd_5924767 := by
    simpa [prefixWord, tailWord_5924767, baseEnd_5924767] using wordTrace_append hprefix tailTrace_5924767
  have hstable : (prefixWord ++ tailWord_5924767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924767).length < 2 ^ (prefixWord ++ tailWord_5924767).sum := by decide
  have hdescent : baseEnd_5924767 < baseStart_5924767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924820 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_5924820 : Nat := 118140960795 + 5924820 * 2 ^ 59
def prefixEnd_5924820 : Nat := 4983230072969 + 3 ^ 40 * 5924820 * 2
def baseEnd_5924820 : Nat := 3042280451371614348202255

theorem tailTrace_5924820 : CollatzResearch.WordTrace tailWord_5924820 prefixEnd_5924820 3042280451371614348202255 := by
  unfold tailWord_5924820
  simp only [CollatzResearch.WordTrace]
  refine ⟨108047969197698246770665957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144063958930264329027554609 108047969197698246770665957)
  ·
    refine ⟨20258994224568421269499867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108047969197698246770665957 20258994224568421269499867)
    ·
      refine ⟨30388491336852631904249801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20258994224568421269499867 30388491336852631904249801)
      ·
        refine ⟨22791368502639473928187351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30388491336852631904249801 22791368502639473928187351)
        ·
          refine ⟨34187052753959210892281027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22791368502639473928187351 34187052753959210892281027)
          ·
            refine ⟨51280579130938816338421541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34187052753959210892281027 51280579130938816338421541)
            ·
              refine ⟨9615108587051028063454039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51280579130938816338421541 9615108587051028063454039)
              ·
                refine ⟨14422662880576542095181059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9615108587051028063454039 14422662880576542095181059)
                ·
                  refine ⟨21633994320864813142771589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14422662880576542095181059 21633994320864813142771589)
                  ·
                    refine ⟨4056373935162152464269673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21633994320864813142771589 4056373935162152464269673)
                    ·
                      refine ⟨3042280451371614348202255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4056373935162152464269673 3042280451371614348202255)
                      ·
                        rfl

theorem cell23_5924820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_5924820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924820 prefixEnd_5924820 := by exact prefixLift 5924820
  have htrace : WordTrace (prefixWord ++ tailWord_5924820) baseStart_5924820 baseEnd_5924820 := by
    simpa [prefixWord, tailWord_5924820, baseEnd_5924820] using wordTrace_append hprefix tailTrace_5924820
  have hstable : (prefixWord ++ tailWord_5924820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924820).length < 2 ^ (prefixWord ++ tailWord_5924820).sum := by decide
  have hdescent : baseEnd_5924820 < baseStart_5924820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924836 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_5924836 : Nat := 118140960795 + 5924836 * 2 ^ 59
def prefixEnd_5924836 : Nat := 4983230072969 + 3 ^ 40 * 5924836 * 2
def baseEnd_5924836 : Nat := 3042288667062086285602181

theorem tailTrace_5924836 : CollatzResearch.WordTrace tailWord_5924836 prefixEnd_5924836 3042288667062086285602181 := by
  unfold tailWord_5924836
  simp only [CollatzResearch.WordTrace]
  refine ⟨108048260981669264136957181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144064347975559018849276241 108048260981669264136957181)
  ·
    refine ⟨40518097868125974051358943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108048260981669264136957181 40518097868125974051358943)
    ·
      refine ⟨60777146802188961077038415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40518097868125974051358943 60777146802188961077038415)
      ·
        refine ⟨91165720203283441615557623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60777146802188961077038415 91165720203283441615557623)
        ·
          refine ⟨136748580304925162423336435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91165720203283441615557623 136748580304925162423336435)
          ·
            refine ⟨205122870457387743635004653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136748580304925162423336435 205122870457387743635004653)
            ·
              refine ⟨76921076421520403863126745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205122870457387743635004653 76921076421520403863126745)
              ·
                refine ⟨57690807316140302897345059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76921076421520403863126745 57690807316140302897345059)
                ·
                  refine ⟨86536210974210454346017589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57690807316140302897345059 86536210974210454346017589)
                  ·
                    refine ⟨8112769778832230094939149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86536210974210454346017589 8112769778832230094939149)
                    ·
                      refine ⟨3042288667062086285602181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8112769778832230094939149 3042288667062086285602181)
                      ·
                        rfl

theorem cell23_5924836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_5924836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924836 prefixEnd_5924836 := by exact prefixLift 5924836
  have htrace : WordTrace (prefixWord ++ tailWord_5924836) baseStart_5924836 baseEnd_5924836 := by
    simpa [prefixWord, tailWord_5924836, baseEnd_5924836] using wordTrace_append hprefix tailTrace_5924836
  have hstable : (prefixWord ++ tailWord_5924836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924836).length < 2 ^ (prefixWord ++ tailWord_5924836).sum := by decide
  have hdescent : baseEnd_5924836 < baseStart_5924836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924856 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 2, 5]
def baseStart_5924856 : Nat := 118140960795 + 5924856 * 2 ^ 59
def prefixEnd_5924856 : Nat := 4983230072969 + 3 ^ 40 * 5924856 * 2
def baseEnd_5924856 : Nat := 1014099645558392069117363

theorem tailTrace_5924856 : CollatzResearch.WordTrace tailWord_5924856 prefixEnd_5924856 1014099645558392069117363 := by
  unfold tailWord_5924856
  simp only [CollatzResearch.WordTrace]
  refine ⟨108048625711633035844821211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144064834282177381126428281 108048625711633035844821211)
  ·
    refine ⟨162072938567449553767231817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108048625711633035844821211 162072938567449553767231817)
    ·
      refine ⟨121554703925587165325423863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162072938567449553767231817 121554703925587165325423863)
      ·
        refine ⟨182332055888380747988135795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121554703925587165325423863 182332055888380747988135795)
        ·
          refine ⟨273498083832571121982203693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182332055888380747988135795 273498083832571121982203693)
          ·
            refine ⟨102561781437214170743326385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273498083832571121982203693 102561781437214170743326385)
            ·
              refine ⟨76921336077910628057494789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102561781437214170743326385 76921336077910628057494789)
              ·
                refine ⟨14422750514608242760780273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76921336077910628057494789 14422750514608242760780273)
                ·
                  refine ⟨10817062885956182070585205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14422750514608242760780273 10817062885956182070585205)
                  ·
                    refine ⟨1014099645558392069117363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10817062885956182070585205 1014099645558392069117363)
                    ·
                      rfl

theorem cell23_5924856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_5924856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924856 prefixEnd_5924856 := by exact prefixLift 5924856
  have htrace : WordTrace (prefixWord ++ tailWord_5924856) baseStart_5924856 baseEnd_5924856 := by
    simpa [prefixWord, tailWord_5924856, baseEnd_5924856] using wordTrace_append hprefix tailTrace_5924856
  have hstable : (prefixWord ++ tailWord_5924856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924856).length < 2 ^ (prefixWord ++ tailWord_5924856).sum := by decide
  have hdescent : baseEnd_5924856 < baseStart_5924856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924876 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_5924876 : Nat := 118140960795 + 5924876 * 2 ^ 59
def prefixEnd_5924876 : Nat := 4983230072969 + 3 ^ 40 * 5924876 * 2
def baseEnd_5924876 : Nat := 3042309206288266129101997

theorem tailTrace_5924876 : CollatzResearch.WordTrace tailWord_5924876 prefixEnd_5924876 3042309206288266129101997 := by
  unfold tailWord_5924876
  simp only [CollatzResearch.WordTrace]
  refine ⟨108048990441596807552685241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144065320588795743403580321 108048990441596807552685241)
  ·
    refine ⟨81036742831197605664513931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108048990441596807552685241 81036742831197605664513931)
    ·
      refine ⟨121555114246796408496770897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81036742831197605664513931 121555114246796408496770897)
      ·
        refine ⟨91166335685097306372578173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121555114246796408496770897 91166335685097306372578173)
        ·
          refine ⟨34187375881911489889716815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91166335685097306372578173 34187375881911489889716815)
          ·
            refine ⟨51281063822867234834575223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34187375881911489889716815 51281063822867234834575223)
            ·
              refine ⟨76921595734300852251862835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51281063822867234834575223 76921595734300852251862835)
              ·
                refine ⟨115382393601451278377794253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76921595734300852251862835 115382393601451278377794253)
                ·
                  refine ⟨43268397600544229391672845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115382393601451278377794253 43268397600544229391672845)
                  ·
                    refine ⟨16225649100204086021877317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43268397600544229391672845 16225649100204086021877317)
                    ·
                      refine ⟨3042309206288266129101997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16225649100204086021877317 3042309206288266129101997)
                      ·
                        rfl

theorem cell23_5924876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_5924876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924876 prefixEnd_5924876 := by exact prefixLift 5924876
  have htrace : WordTrace (prefixWord ++ tailWord_5924876) baseStart_5924876 baseEnd_5924876 := by
    simpa [prefixWord, tailWord_5924876, baseEnd_5924876] using wordTrace_append hprefix tailTrace_5924876
  have hstable : (prefixWord ++ tailWord_5924876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924876).length < 2 ^ (prefixWord ++ tailWord_5924876).sum := by decide
  have hdescent : baseEnd_5924876 < baseStart_5924876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924893 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_5924893 : Nat := 118140960795 + 5924893 * 2 ^ 59
def prefixEnd_5924893 : Nat := 4983230072969 + 3 ^ 40 * 5924893 * 2
def baseEnd_5924893 : Nat := 3042317935459392562589419

theorem tailTrace_5924893 : CollatzResearch.WordTrace tailWord_5924893 prefixEnd_5924893 3042317935459392562589419 := by
  unfold tailWord_5924893
  simp only [CollatzResearch.WordTrace]
  refine ⟨216098600924132027008739333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144065733949421351339159555 216098600924132027008739333)
  ·
    refine ⟨40518487673274755064138625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216098600924132027008739333 40518487673274755064138625)
    ·
      refine ⟨30388865754956066298103969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40518487673274755064138625 30388865754956066298103969)
      ·
        refine ⟨22791649316217049723577977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30388865754956066298103969 22791649316217049723577977)
        ·
          refine ⟨17093736987162787292683483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22791649316217049723577977 17093736987162787292683483)
          ·
            refine ⟨25640605480744180939025225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17093736987162787292683483 25640605480744180939025225)
            ·
              refine ⟨19230454110558135704268919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25640605480744180939025225 19230454110558135704268919)
              ·
                refine ⟨28845681165837203556403379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19230454110558135704268919 28845681165837203556403379)
                ·
                  refine ⟨43268521748755805334605069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28845681165837203556403379 43268521748755805334605069)
                  ·
                    refine ⟨16225695655783427000476901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43268521748755805334605069 16225695655783427000476901)
                    ·
                      refine ⟨3042317935459392562589419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16225695655783427000476901 3042317935459392562589419)
                      ·
                        rfl

theorem cell23_5924893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_5924893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924893 prefixEnd_5924893 := by exact prefixLift 5924893
  have htrace : WordTrace (prefixWord ++ tailWord_5924893) baseStart_5924893 baseEnd_5924893 := by
    simpa [prefixWord, tailWord_5924893, baseEnd_5924893] using wordTrace_append hprefix tailTrace_5924893
  have hstable : (prefixWord ++ tailWord_5924893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924893).length < 2 ^ (prefixWord ++ tailWord_5924893).sum := by decide
  have hdescent : baseEnd_5924893 < baseStart_5924893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924910 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_5924910 : Nat := 118140960795 + 5924910 * 2 ^ 59
def prefixEnd_5924910 : Nat := 4983230072969 + 3 ^ 40 * 5924910 * 2
def baseEnd_5924910 : Nat := 3042326664630518996076841

theorem tailTrace_5924910 : CollatzResearch.WordTrace tailWord_5924910 prefixEnd_5924910 3042326664630518996076841 := by
  unfold tailWord_5924910
  simp only [CollatzResearch.WordTrace]
  refine ⟨27012402620633804864013523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144066147310046959274738789 27012402620633804864013523)
  ·
    refine ⟨40518603930950707296020285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27012402620633804864013523 40518603930950707296020285)
    ·
      refine ⟨15194476474106515236007607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40518603930950707296020285 15194476474106515236007607)
      ·
        refine ⟨22791714711159772854011411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15194476474106515236007607 22791714711159772854011411)
        ·
          refine ⟨34187572066739659281017117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22791714711159772854011411 34187572066739659281017117)
          ·
            refine ⟨12820339525027372230381419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34187572066739659281017117 12820339525027372230381419)
            ·
              refine ⟨19230509287541058345572129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12820339525027372230381419 19230509287541058345572129)
              ·
                refine ⟨14422881965655793759179097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19230509287541058345572129 14422881965655793759179097)
                ·
                  refine ⟨10817161474241845319384323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14422881965655793759179097 10817161474241845319384323)
                  ·
                    refine ⟨16225742211362767979076485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10817161474241845319384323 16225742211362767979076485)
                    ·
                      refine ⟨3042326664630518996076841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16225742211362767979076485 3042326664630518996076841)
                      ·
                        rfl

theorem cell23_5924910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_5924910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924910 prefixEnd_5924910 := by exact prefixLift 5924910
  have htrace : WordTrace (prefixWord ++ tailWord_5924910) baseStart_5924910 baseEnd_5924910 := by
    simpa [prefixWord, tailWord_5924910, baseEnd_5924910] using wordTrace_append hprefix tailTrace_5924910
  have hstable : (prefixWord ++ tailWord_5924910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924910).length < 2 ^ (prefixWord ++ tailWord_5924910).sum := by decide
  have hdescent : baseEnd_5924910 < baseStart_5924910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924913 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 4, 2, 3]
def baseStart_5924913 : Nat := 118140960795 + 5924913 * 2 ^ 59
def prefixEnd_5924913 : Nat := 4983230072969 + 3 ^ 40 * 5924913 * 2
def baseEnd_5924913 : Nat := 3042328205072482484339327

theorem tailTrace_5924913 : CollatzResearch.WordTrace tailWord_5924913 prefixEnd_5924913 3042328205072482484339327 := by
  unfold tailWord_5924913
  simp only [CollatzResearch.WordTrace]
  refine ⟨216099330384059570424467393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144066220256039713616311595 216099330384059570424467393)
  ·
    refine ⟨162074497788044677818350545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216099330384059570424467393 162074497788044677818350545)
    ·
      refine ⟨121555873341033508363762909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162074497788044677818350545 121555873341033508363762909)
      ·
        refine ⟨45583452502887565636411091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121555873341033508363762909 45583452502887565636411091)
        ·
          refine ⟨68375178754331348454616637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45583452502887565636411091 68375178754331348454616637)
          ·
            refine ⟨25640692032874255670481239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68375178754331348454616637 25640692032874255670481239)
            ·
              refine ⟨38461038049311383505721859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25640692032874255670481239 38461038049311383505721859)
              ·
                refine ⟨57691557073967075258582789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38461038049311383505721859 57691557073967075258582789)
                ·
                  refine ⟨10817166951368826610984273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57691557073967075258582789 10817166951368826610984273)
                  ·
                    refine ⟨8112875213526619958238205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10817166951368826610984273 8112875213526619958238205)
                    ·
                      refine ⟨3042328205072482484339327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8112875213526619958238205 3042328205072482484339327)
                      ·
                        rfl

theorem cell23_5924913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_5924913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924913 prefixEnd_5924913 := by exact prefixLift 5924913
  have htrace : WordTrace (prefixWord ++ tailWord_5924913) baseStart_5924913 baseEnd_5924913 := by
    simpa [prefixWord, tailWord_5924913, baseEnd_5924913] using wordTrace_append hprefix tailTrace_5924913
  have hstable : (prefixWord ++ tailWord_5924913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924913).length < 2 ^ (prefixWord ++ tailWord_5924913).sum := by decide
  have hdescent : baseEnd_5924913 < baseStart_5924913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924963 : List Nat := [1, 1, 1, 5, 1, 1, 2, 5, 1, 5]
def baseStart_5924963 : Nat := 118140960795 + 5924963 * 2 ^ 59
def prefixEnd_5924963 : Nat := 4983230072969 + 3 ^ 40 * 5924963 * 2
def baseEnd_5924963 : Nat := 1014117959701735762904699

theorem tailTrace_5924963 : CollatzResearch.WordTrace tailWord_5924963 prefixEnd_5924963 1014117959701735762904699 := by
  unfold tailWord_5924963
  simp only [CollatzResearch.WordTrace]
  refine ⟨216101154033878428963787543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144067436022585619309191695 216101154033878428963787543)
  ·
    refine ⟨324151731050817643445681315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216101154033878428963787543 324151731050817643445681315)
    ·
      refine ⟨486227596576226465168521973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324151731050817643445681315 486227596576226465168521973)
      ·
        refine ⟨45583837179021231109548935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 486227596576226465168521973 45583837179021231109548935)
        ·
          refine ⟨68375755768531846664323403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45583837179021231109548935 68375755768531846664323403)
          ·
            refine ⟨102563633652797769996485105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68375755768531846664323403 102563633652797769996485105)
            ·
              refine ⟨76922725239598327497363829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102563633652797769996485105 76922725239598327497363829)
              ·
                refine ⟨7211505491212343202877859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76922725239598327497363829 7211505491212343202877859)
                ·
                  refine ⟨10817258236818514804316789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7211505491212343202877859 10817258236818514804316789)
                  ·
                    refine ⟨1014117959701735762904699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10817258236818514804316789 1014117959701735762904699)
                    ·
                      rfl

theorem cell23_5924963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 5].length) (baseStart_5924963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924963 prefixEnd_5924963 := by exact prefixLift 5924963
  have htrace : WordTrace (prefixWord ++ tailWord_5924963) baseStart_5924963 baseEnd_5924963 := by
    simpa [prefixWord, tailWord_5924963, baseEnd_5924963] using wordTrace_append hprefix tailTrace_5924963
  have hstable : (prefixWord ++ tailWord_5924963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924963).length < 2 ^ (prefixWord ++ tailWord_5924963).sum := by decide
  have hdescent : baseEnd_5924963 < baseStart_5924963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924977 : List Nat := [1, 2, 2, 2, 1, 1, 5, 4, 1, 1, 3]
def baseStart_5924977 : Nat := 118140960795 + 5924977 * 2 ^ 59
def prefixEnd_5924977 : Nat := 4983230072969 + 3 ^ 40 * 5924977 * 2
def baseEnd_5924977 : Nat := 3042361067834370233939033

theorem tailTrace_5924977 : CollatzResearch.WordTrace tailWord_5924977 prefixEnd_5924977 3042361067834370233939033 := by
  unfold tailWord_5924977
  simp only [CollatzResearch.WordTrace]
  refine ⟨216101664655827709354797185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144067776437218472903198123 216101664655827709354797185)
  ·
    refine ⟨162076248491870782016097889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216101664655827709354797185 162076248491870782016097889)
    ·
      refine ⟨121557186368903086512073417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162076248491870782016097889 121557186368903086512073417)
      ·
        refine ⟨91167889776677314884055063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121557186368903086512073417 91167889776677314884055063)
        ·
          refine ⟨136751834665015972326082595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91167889776677314884055063 136751834665015972326082595)
          ·
            refine ⟨205127751997523958489123893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136751834665015972326082595 205127751997523958489123893)
            ·
              refine ⟨19230726749767871108355365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205127751997523958489123893 19230726749767871108355365)
              ·
                refine ⟨3605761265581475832816631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19230726749767871108355365 3605761265581475832816631)
                ·
                  refine ⟨5408641898372213749224947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3605761265581475832816631 5408641898372213749224947)
                  ·
                    refine ⟨8112962847558320623837421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5408641898372213749224947 8112962847558320623837421)
                    ·
                      refine ⟨3042361067834370233939033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8112962847558320623837421 3042361067834370233939033)
                      ·
                        rfl

theorem cell23_5924977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_5924977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924977 prefixEnd_5924977 := by exact prefixLift 5924977
  have htrace : WordTrace (prefixWord ++ tailWord_5924977) baseStart_5924977 baseEnd_5924977 := by
    simpa [prefixWord, tailWord_5924977, baseEnd_5924977] using wordTrace_append hprefix tailTrace_5924977
  have hstable : (prefixWord ++ tailWord_5924977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924977).length < 2 ^ (prefixWord ++ tailWord_5924977).sum := by decide
  have hdescent : baseEnd_5924977 < baseStart_5924977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5924983 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_5924983 : Nat := 118140960795 + 5924983 * 2 ^ 59
def prefixEnd_5924983 : Nat := 4983230072969 + 3 ^ 40 * 5924983 * 2
def baseEnd_5924983 : Nat := 3042364148718297210464005

theorem tailTrace_5924983 : CollatzResearch.WordTrace tailWord_5924983 prefixEnd_5924983 3042364148718297210464005 := by
  unfold tailWord_5924983
  simp only [CollatzResearch.WordTrace]
  refine ⟨216101883493805972379515603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144067922329203981586343735 216101883493805972379515603)
  ·
    refine ⟨324152825240708958569273405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216101883493805972379515603 324152825240708958569273405)
    ·
      refine ⟨121557309465265859463477527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324152825240708958569273405 121557309465265859463477527)
      ·
        refine ⟨182335964197898789195216291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121557309465265859463477527 182335964197898789195216291)
        ·
          refine ⟨273503946296848183792824437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182335964197898789195216291 273503946296848183792824437)
          ·
            refine ⟨25640994965329517230577291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 273503946296848183792824437 25640994965329517230577291)
            ·
              refine ⟨38461492447994275845865937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25640994965329517230577291 38461492447994275845865937)
              ·
                refine ⟨28846119335995706884399453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38461492447994275845865937 28846119335995706884399453)
                ·
                  refine ⟨10817294750998390081649795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28846119335995706884399453 10817294750998390081649795)
                  ·
                    refine ⟨16225942126497585122474693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10817294750998390081649795 16225942126497585122474693)
                    ·
                      refine ⟨3042364148718297210464005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16225942126497585122474693 3042364148718297210464005)
                      ·
                        rfl

theorem cell23_5924983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_5924983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5924983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5924983 prefixEnd_5924983 := by exact prefixLift 5924983
  have htrace : WordTrace (prefixWord ++ tailWord_5924983) baseStart_5924983 baseEnd_5924983 := by
    simpa [prefixWord, tailWord_5924983, baseEnd_5924983] using wordTrace_append hprefix tailTrace_5924983
  have hstable : (prefixWord ++ tailWord_5924983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5924983).length < 2 ^ (prefixWord ++ tailWord_5924983).sum := by decide
  have hdescent : baseEnd_5924983 < baseStart_5924983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5924983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925000 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5925000 : Nat := 118140960795 + 5925000 * 2 ^ 59
def prefixEnd_5925000 : Nat := 4983230072969 + 3 ^ 40 * 5925000 * 2
def baseEnd_5925000 : Nat := 3042372877889423643951427

theorem tailTrace_5925000 : CollatzResearch.WordTrace tailWord_5925000 prefixEnd_5925000 3042372877889423643951427 := by
  unfold tailWord_5925000
  simp only [CollatzResearch.WordTrace]
  refine ⟨108051251767372192141442227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144068335689829589521922969 108051251767372192141442227)
  ·
    refine ⟨162076877651058288212163341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108051251767372192141442227 162076877651058288212163341)
    ·
      refine ⟨60778829119146858079561253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162076877651058288212163341 60778829119146858079561253)
      ·
        refine ⟨11396030459840035889917735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60778829119146858079561253 11396030459840035889917735)
        ·
          refine ⟨17094045689760053834876603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11396030459840035889917735 17094045689760053834876603)
          ·
            refine ⟨25641068534640080752314905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17094045689760053834876603 25641068534640080752314905)
            ·
              refine ⟨19230801400980060564236179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25641068534640080752314905 19230801400980060564236179)
              ·
                refine ⟨28846202101470090846354269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19230801400980060564236179 28846202101470090846354269)
                ·
                  refine ⟨10817325788051284067382851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28846202101470090846354269 10817325788051284067382851)
                  ·
                    refine ⟨16225988682076926101074277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10817325788051284067382851 16225988682076926101074277)
                    ·
                      refine ⟨3042372877889423643951427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16225988682076926101074277 3042372877889423643951427)
                      ·
                        rfl

theorem cell23_5925000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5925000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925000 prefixEnd_5925000 := by exact prefixLift 5925000
  have htrace : WordTrace (prefixWord ++ tailWord_5925000) baseStart_5925000 baseEnd_5925000 := by
    simpa [prefixWord, tailWord_5925000, baseEnd_5925000] using wordTrace_append hprefix tailTrace_5925000
  have hstable : (prefixWord ++ tailWord_5925000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925000).length < 2 ^ (prefixWord ++ tailWord_5925000).sum := by decide
  have hdescent : baseEnd_5925000 < baseStart_5925000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925010 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_5925010 : Nat := 118140960795 + 5925010 * 2 ^ 59
def prefixEnd_5925010 : Nat := 4983230072969 + 3 ^ 40 * 5925010 * 2
def baseEnd_5925010 : Nat := 1014126004231989534942127

theorem tailTrace_5925010 : CollatzResearch.WordTrace tailWord_5925010 prefixEnd_5925010 1014126004231989534942127 := by
  unfold tailWord_5925010
  simp only [CollatzResearch.WordTrace]
  refine ⟨54025717066177038997687121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144068578843138770660498989 54025717066177038997687121)
  ·
    refine ⟨40519287799632779248265341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54025717066177038997687121 40519287799632779248265341)
    ·
      refine ⟨15194732924862292218099503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40519287799632779248265341 15194732924862292218099503)
      ·
        refine ⟨22792099387293438327149255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15194732924862292218099503 22792099387293438327149255)
        ·
          refine ⟨34188149080940157490723883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22792099387293438327149255 34188149080940157490723883)
          ·
            refine ⟨51282223621410236236085825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34188149080940157490723883 51282223621410236236085825)
            ·
              refine ⟨38461667716057677177064369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51282223621410236236085825 38461667716057677177064369)
              ·
                refine ⟨28846250787043257882798277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38461667716057677177064369 28846250787043257882798277)
                ·
                  refine ⟨5408672022570610853024677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28846250787043257882798277 5408672022570610853024677)
                  ·
                    refine ⟨1014126004231989534942127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5408672022570610853024677 1014126004231989534942127)
                    ·
                      rfl

theorem cell23_5925010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_5925010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925010 prefixEnd_5925010 := by exact prefixLift 5925010
  have htrace : WordTrace (prefixWord ++ tailWord_5925010) baseStart_5925010 baseEnd_5925010 := by
    simpa [prefixWord, tailWord_5925010, baseEnd_5925010] using wordTrace_append hprefix tailTrace_5925010
  have hstable : (prefixWord ++ tailWord_5925010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925010).length < 2 ^ (prefixWord ++ tailWord_5925010).sum := by decide
  have hdescent : baseEnd_5925010 < baseStart_5925010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925013 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_5925013 : Nat := 118140960795 + 5925013 * 2 ^ 59
def prefixEnd_5925013 : Nat := 4983230072969 + 3 ^ 40 * 5925013 * 2
def baseEnd_5925013 : Nat := 3042379553137932093088867

theorem tailTrace_5925013 : CollatzResearch.WordTrace tailWord_5925013 prefixEnd_5925013 3042379553137932093088867 := by
  unfold tailWord_5925013
  simp only [CollatzResearch.WordTrace]
  refine ⟨216102977683697287503107693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144068651789131525002071795 216102977683697287503107693)
  ·
    refine ⟨81038616631386482813665385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216102977683697287503107693 81038616631386482813665385)
    ·
      refine ⟨60778962473539862110249039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81038616631386482813665385 60778962473539862110249039)
      ·
        refine ⟨91168443710309793165373559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60778962473539862110249039 91168443710309793165373559)
        ·
          refine ⟨136752665565464689748060339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91168443710309793165373559 136752665565464689748060339)
          ·
            refine ⟨205128998348197034622090509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136752665565464689748060339 205128998348197034622090509)
            ·
              refine ⟨76923374380573887983283941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205128998348197034622090509 76923374380573887983283941)
              ·
                refine ⟨14423132696357603996865739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76923374380573887983283941 14423132696357603996865739)
                ·
                  refine ⟨21634699044536405995298609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14423132696357603996865739 21634699044536405995298609)
                  ·
                    refine ⟨16226024283402304496473957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21634699044536405995298609 16226024283402304496473957)
                    ·
                      refine ⟨3042379553137932093088867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16226024283402304496473957 3042379553137932093088867)
                      ·
                        rfl

theorem cell23_5925013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_5925013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925013 prefixEnd_5925013 := by exact prefixLift 5925013
  have htrace : WordTrace (prefixWord ++ tailWord_5925013) baseStart_5925013 baseEnd_5925013 := by
    simpa [prefixWord, tailWord_5925013, baseEnd_5925013] using wordTrace_append hprefix tailTrace_5925013
  have hstable : (prefixWord ++ tailWord_5925013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925013).length < 2 ^ (prefixWord ++ tailWord_5925013).sum := by decide
  have hdescent : baseEnd_5925013 < baseStart_5925013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925023 : List Nat := [1, 1, 2, 6, 1, 2, 10]
def baseStart_5925023 : Nat := 118140960795 + 5925023 * 2 ^ 59
def prefixEnd_5925023 : Nat := 4983230072969 + 3 ^ 40 * 5925023 * 2
def baseEnd_5925023 : Nat := 37560304789437988320541

theorem tailTrace_5925023 : CollatzResearch.WordTrace tailWord_5925023 prefixEnd_5925023 37560304789437988320541 := by
  unfold tailWord_5925023
  simp only [CollatzResearch.WordTrace]
  refine ⟨216103342413661059210971723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144068894942440706140647815 216103342413661059210971723)
  ·
    refine ⟨324155013620491588816457585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216103342413661059210971723 324155013620491588816457585)
    ·
      refine ⟨243116260215368691612343189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324155013620491588816457585 243116260215368691612343189)
      ·
        refine ⟨11396074697595407419328587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 243116260215368691612343189 11396074697595407419328587)
        ·
          refine ⟨17094112046393111128992881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11396074697595407419328587 17094112046393111128992881)
          ·
            refine ⟨12820584034794833346744661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17094112046393111128992881 12820584034794833346744661)
            ·
              refine ⟨37560304789437988320541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12820584034794833346744661 37560304789437988320541)
              ·
                rfl

theorem cell23_5925023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 10].length) (baseStart_5925023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925023 prefixEnd_5925023 := by exact prefixLift 5925023
  have htrace : WordTrace (prefixWord ++ tailWord_5925023) baseStart_5925023 baseEnd_5925023 := by
    simpa [prefixWord, tailWord_5925023, baseEnd_5925023] using wordTrace_append hprefix tailTrace_5925023
  have hstable : (prefixWord ++ tailWord_5925023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925023).length < 2 ^ (prefixWord ++ tailWord_5925023).sum := by decide
  have hdescent : baseEnd_5925023 < baseStart_5925023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925050 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3]
def baseStart_5925050 : Nat := 118140960795 + 5925050 * 2 ^ 59
def prefixEnd_5925050 : Nat := 4983230072969 + 3 ^ 40 * 5925050 * 2
def baseEnd_5925050 : Nat := 3042398551922148448326197

theorem tailTrace_5925050 : CollatzResearch.WordTrace tailWord_5925050 prefixEnd_5925050 3042398551922148448326197 := by
  unfold tailWord_5925050
  simp only [CollatzResearch.WordTrace]
  refine ⟨54026081796140810705551151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144069551456375495214803069 54026081796140810705551151)
  ·
    refine ⟨81039122694211216058326727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54026081796140810705551151 81039122694211216058326727)
    ·
      refine ⟨121558684041316824087490091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81039122694211216058326727 121558684041316824087490091)
      ·
        refine ⟨182338026061975236131235137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121558684041316824087490091 182338026061975236131235137)
        ·
          refine ⟨136753519546481427098426353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182338026061975236131235137 136753519546481427098426353)
          ·
            refine ⟨102565139659861070323819765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136753519546481427098426353 102565139659861070323819765)
            ·
              refine ⟨9615481843111975342858103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102565139659861070323819765 9615481843111975342858103)
              ·
                refine ⟨14423222764667963014287155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9615481843111975342858103 14423222764667963014287155)
                ·
                  refine ⟨21634834147001944521430733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14423222764667963014287155 21634834147001944521430733)
                  ·
                    refine ⟨8113062805125729195536525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21634834147001944521430733 8113062805125729195536525)
                    ·
                      refine ⟨3042398551922148448326197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8113062805125729195536525 3042398551922148448326197)
                      ·
                        rfl

theorem cell23_5925050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_5925050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925050 prefixEnd_5925050 := by exact prefixLift 5925050
  have htrace : WordTrace (prefixWord ++ tailWord_5925050) baseStart_5925050 baseEnd_5925050 := by
    simpa [prefixWord, tailWord_5925050, baseEnd_5925050] using wordTrace_append hprefix tailTrace_5925050
  have hstable : (prefixWord ++ tailWord_5925050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925050).length < 2 ^ (prefixWord ++ tailWord_5925050).sum := by decide
  have hdescent : baseEnd_5925050 < baseStart_5925050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925054 : List Nat := [4, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_5925054 : Nat := 118140960795 + 5925054 * 2 ^ 59
def prefixEnd_5925054 : Nat := 4983230072969 + 3 ^ 40 * 5925054 * 2
def baseEnd_5925054 : Nat := 3042400605844766432676179

theorem tailTrace_5925054 : CollatzResearch.WordTrace tailWord_5925054 prefixEnd_5925054 3042400605844766432676179 := by
  unfold tailWord_5925054
  simp only [CollatzResearch.WordTrace]
  refine ⟨27013059134568593938168777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144069648717699167670233477 27013059134568593938168777)
  ·
    refine ⟨20259794350926445453626583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27013059134568593938168777 20259794350926445453626583)
    ·
      refine ⟨30389691526389668180439875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20259794350926445453626583 30389691526389668180439875)
      ·
        refine ⟨45584537289584502270659813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30389691526389668180439875 45584537289584502270659813)
        ·
          refine ⟨8547100741797094175748715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45584537289584502270659813 8547100741797094175748715)
          ·
            refine ⟨12820651112695641263623073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8547100741797094175748715 12820651112695641263623073)
            ·
              refine ⟨9615488334521730947717305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12820651112695641263623073 9615488334521730947717305)
              ·
                refine ⟨7211616250891298210787979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9615488334521730947717305 7211616250891298210787979)
                ·
                  refine ⟨10817424376336947316181969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7211616250891298210787979 10817424376336947316181969)
                  ·
                    refine ⟨8113068282252710487136477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10817424376336947316181969 8113068282252710487136477)
                    ·
                      refine ⟨3042400605844766432676179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8113068282252710487136477 3042400605844766432676179)
                      ·
                        rfl

theorem cell23_5925054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_5925054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925054 prefixEnd_5925054 := by exact prefixLift 5925054
  have htrace : WordTrace (prefixWord ++ tailWord_5925054) baseStart_5925054 baseEnd_5925054 := by
    simpa [prefixWord, tailWord_5925054, baseEnd_5925054] using wordTrace_append hprefix tailTrace_5925054
  have hstable : (prefixWord ++ tailWord_5925054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925054).length < 2 ^ (prefixWord ++ tailWord_5925054).sum := by decide
  have hdescent : baseEnd_5925054 < baseStart_5925054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925110 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_5925110 : Nat := 118140960795 + 5925110 * 2 ^ 59
def prefixEnd_5925110 : Nat := 4983230072969 + 3 ^ 40 * 5925110 * 2
def baseEnd_5925110 : Nat := 3042429360761418213575921

theorem tailTrace_5925110 : CollatzResearch.WordTrace tailWord_5925110 prefixEnd_5925110 3042429360761418213575921 := by
  unfold tailWord_5925110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13506657222771617066836799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144071010376230582046259189 13506657222771617066836799)
  ·
    refine ⟨20259985834157425600255199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13506657222771617066836799 20259985834157425600255199)
    ·
      refine ⟨30389978751236138400382799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20259985834157425600255199 30389978751236138400382799)
      ·
        refine ⟨45584968126854207600574199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30389978751236138400382799 45584968126854207600574199)
        ·
          refine ⟨68377452190281311400861299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45584968126854207600574199 68377452190281311400861299)
          ·
            refine ⟨102566178285421967101291949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68377452190281311400861299 102566178285421967101291949)
            ·
              refine ⟨38462316857033237662984481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102566178285421967101291949 38462316857033237662984481)
              ·
                refine ⟨28846737642774928247238361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38462316857033237662984481 28846737642774928247238361)
                ·
                  refine ⟨21635053232081196185428771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28846737642774928247238361 21635053232081196185428771)
                  ·
                    refine ⟨32452579848121794278143157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21635053232081196185428771 32452579848121794278143157)
                    ·
                      refine ⟨3042429360761418213575921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32452579848121794278143157 3042429360761418213575921)
                      ·
                        rfl

theorem cell23_5925110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_5925110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925110 prefixEnd_5925110 := by exact prefixLift 5925110
  have htrace : WordTrace (prefixWord ++ tailWord_5925110) baseStart_5925110 baseEnd_5925110 := by
    simpa [prefixWord, tailWord_5925110, baseEnd_5925110] using wordTrace_append hprefix tailTrace_5925110
  have hstable : (prefixWord ++ tailWord_5925110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925110).length < 2 ^ (prefixWord ++ tailWord_5925110).sum := by decide
  have hdescent : baseEnd_5925110 < baseStart_5925110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925124 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_5925124 : Nat := 118140960795 + 5925124 * 2 ^ 59
def prefixEnd_5925124 : Nat := 4983230072969 + 3 ^ 40 * 5925124 * 2
def baseEnd_5925124 : Nat := 3042436549490581158800857

theorem tailTrace_5925124 : CollatzResearch.WordTrace tailWord_5925124 prefixEnd_5925124 3042436549490581158800857 := by
  unfold tailWord_5925124
  simp only [CollatzResearch.WordTrace]
  refine ⟨108053513093147576730199213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144071350790863435640265617 108053513093147576730199213)
  ·
    refine ⟨40520067409930341273824705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108053513093147576730199213 40520067409930341273824705)
    ·
      refine ⟨30390050557447755955368529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40520067409930341273824705 30390050557447755955368529)
      ·
        refine ⟨22792537918085816966526397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30390050557447755955368529 22792537918085816966526397)
        ·
          refine ⟨8547201719282181362447399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22792537918085816966526397 8547201719282181362447399)
          ·
            refine ⟨12820802578923272043671099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8547201719282181362447399 12820802578923272043671099)
            ·
              refine ⟨19231203868384908065506649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12820802578923272043671099 19231203868384908065506649)
              ·
                refine ⟨14423402901288681049129987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19231203868384908065506649 14423402901288681049129987)
                ·
                  refine ⟨21635104351933021573694981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14423402901288681049129987 21635104351933021573694981)
                  ·
                    refine ⟨4056582065987441545067809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21635104351933021573694981 4056582065987441545067809)
                    ·
                      refine ⟨3042436549490581158800857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4056582065987441545067809 3042436549490581158800857)
                      ·
                        rfl

theorem cell23_5925124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_5925124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925124 prefixEnd_5925124 := by exact prefixLift 5925124
  have htrace : WordTrace (prefixWord ++ tailWord_5925124) baseStart_5925124 baseEnd_5925124 := by
    simpa [prefixWord, tailWord_5925124, baseEnd_5925124] using wordTrace_append hprefix tailTrace_5925124
  have hstable : (prefixWord ++ tailWord_5925124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925124).length < 2 ^ (prefixWord ++ tailWord_5925124).sum := by decide
  have hdescent : baseEnd_5925124 < baseStart_5925124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925147 : List Nat := [1, 1, 1, 1, 1, 1, 10, 2, 5]
def baseStart_5925147 : Nat := 118140960795 + 5925147 * 2 ^ 59
def prefixEnd_5925147 : Nat := 4983230072969 + 3 ^ 40 * 5925147 * 2
def baseEnd_5925147 : Nat := 338049817727292729868139

theorem tailTrace_5925147 : CollatzResearch.WordTrace tailWord_5925147 prefixEnd_5925147 338049817727292729868139 := by
  unfold tailWord_5925147
  simp only [CollatzResearch.WordTrace]
  refine ⟨216107865065211828388485695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144071910043474552258990463 216107865065211828388485695)
  ·
    refine ⟨324161797597817742582728543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216107865065211828388485695 324161797597817742582728543)
    ·
      refine ⟨486242696396726613874092815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324161797597817742582728543 486242696396726613874092815)
      ·
        refine ⟨729364044595089920811139223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486242696396726613874092815 729364044595089920811139223)
        ·
          refine ⟨1094046066892634881216708835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729364044595089920811139223 1094046066892634881216708835)
          ·
            refine ⟨1641069100338952321825063253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094046066892634881216708835 1641069100338952321825063253)
            ·
              refine ⟨4807819629899274380346865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1641069100338952321825063253 4807819629899274380346865)
              ·
                refine ⟨3605864722424455785260149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807819629899274380346865 3605864722424455785260149)
                ·
                  refine ⟨338049817727292729868139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3605864722424455785260149 338049817727292729868139)
                  ·
                    rfl

theorem cell23_5925147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 5].length) (baseStart_5925147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925147 prefixEnd_5925147 := by exact prefixLift 5925147
  have htrace : WordTrace (prefixWord ++ tailWord_5925147) baseStart_5925147 baseEnd_5925147 := by
    simpa [prefixWord, tailWord_5925147, baseEnd_5925147] using wordTrace_append hprefix tailTrace_5925147
  have hstable : (prefixWord ++ tailWord_5925147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925147).length < 2 ^ (prefixWord ++ tailWord_5925147).sum := by decide
  have hdescent : baseEnd_5925147 < baseStart_5925147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925157 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 2, 3, 3]
def baseStart_5925157 : Nat := 118140960795 + 5925157 * 2 ^ 59
def prefixEnd_5925157 : Nat := 4983230072969 + 3 ^ 40 * 5925157 * 2
def baseEnd_5925157 : Nat := 3042453494352179529688205

theorem tailTrace_5925157 : CollatzResearch.WordTrace tailWord_5925157 prefixEnd_5925157 3042453494352179529688205 := by
  unfold tailWord_5925157
  simp only [CollatzResearch.WordTrace]
  refine ⟨216108229795175600096349725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144072153196783733397566483 216108229795175600096349725)
  ·
    refine ⟨81040586173190850036131147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216108229795175600096349725 81040586173190850036131147)
    ·
      refine ⟨121560879259786275054196721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81040586173190850036131147 121560879259786275054196721)
      ·
        refine ⟨91170659444839706290647541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121560879259786275054196721 91170659444839706290647541)
        ·
          refine ⟨8547249322953722464748207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91170659444839706290647541 8547249322953722464748207)
          ·
            refine ⟨12820873984430583697122311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8547249322953722464748207 12820873984430583697122311)
            ·
              refine ⟨19231310976645875545683467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12820873984430583697122311 19231310976645875545683467)
              ·
                refine ⟨28846966464968813318525201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19231310976645875545683467 28846966464968813318525201)
                ·
                  refine ⟨21635224848726609988893901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28846966464968813318525201 21635224848726609988893901)
                  ·
                    refine ⟨8113209318272478745835213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21635224848726609988893901 8113209318272478745835213)
                    ·
                      refine ⟨3042453494352179529688205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8113209318272478745835213 3042453494352179529688205)
                      ·
                        rfl

theorem cell23_5925157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_5925157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925157 prefixEnd_5925157 := by exact prefixLift 5925157
  have htrace : WordTrace (prefixWord ++ tailWord_5925157) baseStart_5925157 baseEnd_5925157 := by
    simpa [prefixWord, tailWord_5925157, baseEnd_5925157] using wordTrace_append hprefix tailTrace_5925157
  have hstable : (prefixWord ++ tailWord_5925157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925157).length < 2 ^ (prefixWord ++ tailWord_5925157).sum := by decide
  have hdescent : baseEnd_5925157 < baseStart_5925157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925177 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 2, 5]
def baseStart_5925177 : Nat := 118140960795 + 5925177 * 2 ^ 59
def prefixEnd_5925177 : Nat := 4983230072969 + 3 ^ 40 * 5925177 * 2
def baseEnd_5925177 : Nat := 1014154587988423150479371

theorem tailTrace_5925177 : CollatzResearch.WordTrace tailWord_5925177 prefixEnd_5925177 1014154587988423150479371 := by
  unfold tailWord_5925177
  simp only [CollatzResearch.WordTrace]
  refine ⟨216108959255103143512077785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144072639503402095674718523 216108959255103143512077785)
  ·
    refine ⟨162081719441327357634058339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216108959255103143512077785 162081719441327357634058339)
    ·
      refine ⟨243122579161991036451087509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162081719441327357634058339 243122579161991036451087509)
      ·
        refine ⟨11396370898218329833644727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 243122579161991036451087509 11396370898218329833644727)
        ·
          refine ⟨17094556347327494750467091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11396370898218329833644727 17094556347327494750467091)
          ·
            refine ⟨25641834520991242125700637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17094556347327494750467091 25641834520991242125700637)
            ·
              refine ⟨9615687945371715797137739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25641834520991242125700637 9615687945371715797137739)
              ·
                refine ⟨14423531918057573695706609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9615687945371715797137739 14423531918057573695706609)
                ·
                  refine ⟨10817648938543180271779957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14423531918057573695706609 10817648938543180271779957)
                  ·
                    refine ⟨1014154587988423150479371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10817648938543180271779957 1014154587988423150479371)
                    ·
                      rfl

theorem cell23_5925177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 5].length) (baseStart_5925177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925177 prefixEnd_5925177 := by exact prefixLift 5925177
  have htrace : WordTrace (prefixWord ++ tailWord_5925177) baseStart_5925177 baseEnd_5925177 := by
    simpa [prefixWord, tailWord_5925177, baseEnd_5925177] using wordTrace_append hprefix tailTrace_5925177
  have hstable : (prefixWord ++ tailWord_5925177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925177).length < 2 ^ (prefixWord ++ tailWord_5925177).sum := by decide
  have hdescent : baseEnd_5925177 < baseStart_5925177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925180 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_5925180 : Nat := 118140960795 + 5925180 * 2 ^ 59
def prefixEnd_5925180 : Nat := 4983230072969 + 3 ^ 40 * 5925180 * 2
def baseEnd_5925180 : Nat := 3042465304407232939700599

theorem tailTrace_5925180 : CollatzResearch.WordTrace tailWord_5925180 prefixEnd_5925180 3042465304407232939700599 := by
  unfold tailWord_5925180
  simp only [CollatzResearch.WordTrace]
  refine ⟨108054534337046137512218497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144072712449394850016291329 108054534337046137512218497)
  ·
    refine ⟨81040900752784603134163873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108054534337046137512218497 81040900752784603134163873)
    ·
      refine ⟨60780675564588452350622905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81040900752784603134163873 60780675564588452350622905)
      ·
        refine ⟨45585506673441339262967179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60780675564588452350622905 45585506673441339262967179)
        ·
          refine ⟨68378260010162008894450769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45585506673441339262967179 68378260010162008894450769)
          ·
            refine ⟨51283695007621506670838077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68378260010162008894450769 51283695007621506670838077)
            ·
              refine ⟨19231385627858065001564279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51283695007621506670838077 19231385627858065001564279)
              ·
                refine ⟨28847078441787097502346419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19231385627858065001564279 28847078441787097502346419)
                ·
                  refine ⟨43270617662680646253519629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28847078441787097502346419 43270617662680646253519629)
                  ·
                    refine ⟨16226481623505242345069861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43270617662680646253519629 16226481623505242345069861)
                    ·
                      refine ⟨3042465304407232939700599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16226481623505242345069861 3042465304407232939700599)
                      ·
                        rfl

theorem cell23_5925180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_5925180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925180 prefixEnd_5925180 := by exact prefixLift 5925180
  have htrace : WordTrace (prefixWord ++ tailWord_5925180) baseStart_5925180 baseEnd_5925180 := by
    simpa [prefixWord, tailWord_5925180, baseEnd_5925180] using wordTrace_append hprefix tailTrace_5925180
  have hstable : (prefixWord ++ tailWord_5925180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925180).length < 2 ^ (prefixWord ++ tailWord_5925180).sum := by decide
  have hdescent : baseEnd_5925180 < baseStart_5925180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925207 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 3, 4]
def baseStart_5925207 : Nat := 118140960795 + 5925207 * 2 ^ 59
def prefixEnd_5925207 : Nat := 4983230072969 + 3 ^ 40 * 5925207 * 2
def baseEnd_5925207 : Nat := 1014159722794968111354325

theorem tailTrace_5925207 : CollatzResearch.WordTrace tailWord_5925207 prefixEnd_5925207 1014159722794968111354325 := by
  unfold tailWord_5925207
  simp only [CollatzResearch.WordTrace]
  refine ⟨216110053444994458635669875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144073368963329639090446583 216110053444994458635669875)
  ·
    refine ⟨324165080167491687953504813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216110053444994458635669875 324165080167491687953504813)
    ·
      refine ⟨121561905062809382982564305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324165080167491687953504813 121561905062809382982564305)
      ·
        refine ⟨91171428797107037236923229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121561905062809382982564305 91171428797107037236923229)
        ·
          refine ⟨34189285798915138963846211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91171428797107037236923229 34189285798915138963846211)
          ·
            refine ⟨51283928698372708445769317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34189285798915138963846211 51283928698372708445769317)
            ·
              refine ⟨9615736630944882833581747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51283928698372708445769317 9615736630944882833581747)
              ·
                refine ⟨14423604946417324250372621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9615736630944882833581747 14423604946417324250372621)
                ·
                  refine ⟨5408851854906496593889733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14423604946417324250372621 5408851854906496593889733)
                  ·
                    refine ⟨1014159722794968111354325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5408851854906496593889733 1014159722794968111354325)
                    ·
                      rfl

theorem cell23_5925207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_5925207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925207 prefixEnd_5925207 := by exact prefixLift 5925207
  have htrace : WordTrace (prefixWord ++ tailWord_5925207) baseStart_5925207 baseEnd_5925207 := by
    simpa [prefixWord, tailWord_5925207, baseEnd_5925207] using wordTrace_append hprefix tailTrace_5925207
  have hstable : (prefixWord ++ tailWord_5925207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925207).length < 2 ^ (prefixWord ++ tailWord_5925207).sum := by decide
  have hdescent : baseEnd_5925207 < baseStart_5925207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925258 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 3, 4]
def baseStart_5925258 : Nat := 118140960795 + 5925258 * 2 ^ 59
def prefixEnd_5925258 : Nat := 4983230072969 + 3 ^ 40 * 5925258 * 2
def baseEnd_5925258 : Nat := 1014168451966094544841747

theorem tailTrace_5925258 : CollatzResearch.WordTrace tailWord_5925258 prefixEnd_5925258 1014168451966094544841747 := by
  unfold tailWord_5925258
  simp only [CollatzResearch.WordTrace]
  refine ⟨54027978391952423586444107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144074609045206462897184285 54027978391952423586444107)
  ·
    refine ⟨81041967587928635379666161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54027978391952423586444107 81041967587928635379666161)
    ·
      refine ⟨60781475690946476534749621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81041967587928635379666161 60781475690946476534749621)
      ·
        refine ⟨5698263346026232175132777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60781475690946476534749621 5698263346026232175132777)
        ·
          refine ⟨4273697509519674131349583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5698263346026232175132777 4273697509519674131349583)
          ·
            refine ⟨6410546264279511197024375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273697509519674131349583 6410546264279511197024375)
            ·
              refine ⟨9615819396419266795536563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6410546264279511197024375 9615819396419266795536563)
              ·
                refine ⟨14423729094628900193304845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9615819396419266795536563 14423729094628900193304845)
                ·
                  refine ⟨5408898410485837572489317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14423729094628900193304845 5408898410485837572489317)
                  ·
                    refine ⟨1014168451966094544841747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5408898410485837572489317 1014168451966094544841747)
                    ·
                      rfl

theorem cell23_5925258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_5925258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925258 prefixEnd_5925258 := by exact prefixLift 5925258
  have htrace : WordTrace (prefixWord ++ tailWord_5925258) baseStart_5925258 baseEnd_5925258 := by
    simpa [prefixWord, tailWord_5925258, baseEnd_5925258] using wordTrace_append hprefix tailTrace_5925258
  have hstable : (prefixWord ++ tailWord_5925258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925258).length < 2 ^ (prefixWord ++ tailWord_5925258).sum := by decide
  have hdescent : baseEnd_5925258 < baseStart_5925258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925297 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 1, 6]
def baseStart_5925297 : Nat := 118140960795 + 5925297 * 2 ^ 59
def prefixEnd_5925297 : Nat := 4983230072969 + 3 ^ 40 * 5925297 * 2
def baseEnd_5925297 : Nat := 1014175127214602993979187

theorem tailTrace_5925297 : CollatzResearch.WordTrace tailWord_5925297 prefixEnd_5925297 1014175127214602993979187 := by
  unfold tailWord_5925297
  simp only [CollatzResearch.WordTrace]
  refine ⟨216113336014668404006446145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144075557343112269337630763 216113336014668404006446145)
  ·
    refine ⟨162085002011001303004834609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216113336014668404006446145 162085002011001303004834609)
    ·
      refine ⟨121563751508250977253625957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162085002011001303004834609 121563751508250977253625957)
      ·
        refine ⟨22793203407797058235054867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121563751508250977253625957 22793203407797058235054867)
        ·
          refine ⟨34189805111695587352582301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22793203407797058235054867 34189805111695587352582301)
          ·
            refine ⟨12821176916885845257218363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34189805111695587352582301 12821176916885845257218363)
            ·
              refine ⟨19231765375328767885827545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12821176916885845257218363 19231765375328767885827545)
              ·
                refine ⟨14423824031496575914370659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19231765375328767885827545 14423824031496575914370659)
                ·
                  refine ⟨21635736047244863871555989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14423824031496575914370659 21635736047244863871555989)
                  ·
                    refine ⟨1014175127214602993979187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21635736047244863871555989 1014175127214602993979187)
                    ·
                      rfl

theorem cell23_5925297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_5925297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925297 prefixEnd_5925297 := by exact prefixLift 5925297
  have htrace : WordTrace (prefixWord ++ tailWord_5925297) baseStart_5925297 baseEnd_5925297 := by
    simpa [prefixWord, tailWord_5925297, baseEnd_5925297] using wordTrace_append hprefix tailTrace_5925297
  have hstable : (prefixWord ++ tailWord_5925297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925297).length < 2 ^ (prefixWord ++ tailWord_5925297).sum := by decide
  have hdescent : baseEnd_5925297 < baseStart_5925297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925301 : List Nat := [1, 3, 3, 2, 3, 1, 3, 1, 1, 5]
def baseStart_5925301 : Nat := 118140960795 + 5925301 * 2 ^ 59
def prefixEnd_5925301 : Nat := 4983230072969 + 3 ^ 40 * 5925301 * 2
def baseEnd_5925301 : Nat := 1014175811855475655429181

theorem tailTrace_5925301 : CollatzResearch.WordTrace tailWord_5925301 prefixEnd_5925301 1014175811855475655429181 := by
  unfold tailWord_5925301
  simp only [CollatzResearch.WordTrace]
  refine ⟨216113481906653912689591757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144075654604435941793061171 216113481906653912689591757)
  ·
    refine ⟨81042555714995217258596909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216113481906653912689591757 81042555714995217258596909)
    ·
      refine ⟨30390958393123206471973841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81042555714995217258596909 30390958393123206471973841)
      ·
        refine ⟨22793218794842404853980381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30390958393123206471973841 22793218794842404853980381)
        ·
          refine ⟨8547457048065901820242643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22793218794842404853980381 8547457048065901820242643)
          ·
            refine ⟨12821185572098852730363965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8547457048065901820242643 12821185572098852730363965)
            ·
              refine ⟨4807944589537069773886487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12821185572098852730363965 4807944589537069773886487)
              ·
                refine ⟨7211916884305604660829731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4807944589537069773886487 7211916884305604660829731)
                ·
                  refine ⟨10817875326458406991244597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7211916884305604660829731 10817875326458406991244597)
                  ·
                    refine ⟨1014175811855475655429181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10817875326458406991244597 1014175811855475655429181)
                    ·
                      rfl

theorem cell23_5925301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_5925301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925301 prefixEnd_5925301 := by exact prefixLift 5925301
  have htrace : WordTrace (prefixWord ++ tailWord_5925301) baseStart_5925301 baseEnd_5925301 := by
    simpa [prefixWord, tailWord_5925301, baseEnd_5925301] using wordTrace_append hprefix tailTrace_5925301
  have hstable : (prefixWord ++ tailWord_5925301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925301).length < 2 ^ (prefixWord ++ tailWord_5925301).sum := by decide
  have hdescent : baseEnd_5925301 < baseStart_5925301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925354 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_5925354 : Nat := 118140960795 + 5925354 * 2 ^ 59
def prefixEnd_5925354 : Nat := 4983230072969 + 3 ^ 40 * 5925354 * 2
def baseEnd_5925354 : Nat := 3042554650041115258924799

theorem tailTrace_5925354 : CollatzResearch.WordTrace tailWord_5925354 prefixEnd_5925354 3042554650041115258924799 := by
  unfold tailWord_5925354
  simp only [CollatzResearch.WordTrace]
  refine ⟨54028853743865475685317779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144076943316974601827514077 54028853743865475685317779)
  ·
    refine ⟨81043280615798213527976669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54028853743865475685317779 81043280615798213527976669)
    ·
      refine ⟨30391230230924330072991251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81043280615798213527976669 30391230230924330072991251)
      ·
        refine ⟨45586845346386495109486877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30391230230924330072991251 45586845346386495109486877)
        ·
          refine ⟨17095067004894935666057579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45586845346386495109486877 17095067004894935666057579)
          ·
            refine ⟨25642600507342403499086369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17095067004894935666057579 25642600507342403499086369)
            ·
              refine ⟨19231950380506802624314777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25642600507342403499086369 19231950380506802624314777)
              ·
                refine ⟨14423962785380101968236083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19231950380506802624314777 14423962785380101968236083)
                ·
                  refine ⟨21635944178070152952354125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14423962785380101968236083 21635944178070152952354125)
                  ·
                    refine ⟨8113479066776307357132797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21635944178070152952354125 8113479066776307357132797)
                    ·
                      refine ⟨3042554650041115258924799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8113479066776307357132797 3042554650041115258924799)
                      ·
                        rfl

theorem cell23_5925354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_5925354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925354 prefixEnd_5925354 := by exact prefixLift 5925354
  have htrace : WordTrace (prefixWord ++ tailWord_5925354) baseStart_5925354 baseEnd_5925354 := by
    simpa [prefixWord, tailWord_5925354, baseEnd_5925354] using wordTrace_append hprefix tailTrace_5925354
  have hstable : (prefixWord ++ tailWord_5925354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925354).length < 2 ^ (prefixWord ++ tailWord_5925354).sum := by decide
  have hdescent : baseEnd_5925354 < baseStart_5925354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925358 : List Nat := [4, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_5925358 : Nat := 118140960795 + 5925358 * 2 ^ 59
def prefixEnd_5925358 : Nat := 4983230072969 + 3 ^ 40 * 5925358 * 2
def baseEnd_5925358 : Nat := 3042556703963733243274781

theorem tailTrace_5925358 : CollatzResearch.WordTrace tailWord_5925358 prefixEnd_5925358 3042556703963733243274781 := by
  unfold tailWord_5925358
  simp only [CollatzResearch.WordTrace]
  refine ⟨27014445108430926428052091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144077040578298274282944485 27014445108430926428052091)
  ·
    refine ⟨40521667662646389642078137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27014445108430926428052091 40521667662646389642078137)
    ·
      refine ⟨30391250746984792231558603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40521667662646389642078137 30391250746984792231558603)
      ·
        refine ⟨45586876120477188347337905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30391250746984792231558603 45586876120477188347337905)
        ·
          refine ⟨34190157090357891260503429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45586876120477188347337905 34190157090357891260503429)
          ·
            refine ⟨6410654454442104611344393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34190157090357891260503429 6410654454442104611344393)
            ·
              refine ⟨4807990840831578458508295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6410654454442104611344393 4807990840831578458508295)
              ·
                refine ⟨7211986261247367687762443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4807990840831578458508295 7211986261247367687762443)
                ·
                  refine ⟨10817979391871051531643665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7211986261247367687762443 10817979391871051531643665)
                  ·
                    refine ⟨8113484543903288648732749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10817979391871051531643665 8113484543903288648732749)
                    ·
                      refine ⟨3042556703963733243274781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8113484543903288648732749 3042556703963733243274781)
                      ·
                        rfl

theorem cell23_5925358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_5925358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925358 prefixEnd_5925358 := by exact prefixLift 5925358
  have htrace : WordTrace (prefixWord ++ tailWord_5925358) baseStart_5925358 baseEnd_5925358 := by
    simpa [prefixWord, tailWord_5925358, baseEnd_5925358] using wordTrace_append hprefix tailTrace_5925358
  have hstable : (prefixWord ++ tailWord_5925358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925358).length < 2 ^ (prefixWord ++ tailWord_5925358).sum := by decide
  have hdescent : baseEnd_5925358 < baseStart_5925358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925365 : List Nat := [1, 3, 5, 1, 3, 1, 1, 2, 2, 4]
def baseStart_5925365 : Nat := 118140960795 + 5925365 * 2 ^ 59
def prefixEnd_5925365 : Nat := 4983230072969 + 3 ^ 40 * 5925365 * 2
def baseEnd_5925365 : Nat := 1014186766109438238629083

theorem tailTrace_5925365 : CollatzResearch.WordTrace tailWord_5925365 prefixEnd_5925365 1014186766109438238629083 := by
  unfold tailWord_5925365
  simp only [CollatzResearch.WordTrace]
  refine ⟨216115816178422051619921549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144077210785614701079947699 216115816178422051619921549)
  ·
    refine ⟨81043431066908269357470581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216115816178422051619921549 81043431066908269357470581)
    ·
      refine ⟨7597821662522650252262867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81043431066908269357470581 7597821662522650252262867)
      ·
        refine ⟨11396732493783975378394301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7597821662522650252262867 11396732493783975378394301)
        ·
          refine ⟨4273774685168990766897863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11396732493783975378394301 4273774685168990766897863)
          ·
            refine ⟨6410662027753486150346795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273774685168990766897863 6410662027753486150346795)
            ·
              refine ⟨9615993041630229225520193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6410662027753486150346795 9615993041630229225520193)
              ·
                refine ⟨7211994781222671919140145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9615993041630229225520193 7211994781222671919140145)
                ·
                  refine ⟨5408996085917003939355109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7211994781222671919140145 5408996085917003939355109)
                  ·
                    refine ⟨1014186766109438238629083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5408996085917003939355109 1014186766109438238629083)
                    ·
                      rfl

theorem cell23_5925365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_5925365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925365 prefixEnd_5925365 := by exact prefixLift 5925365
  have htrace : WordTrace (prefixWord ++ tailWord_5925365) baseStart_5925365 baseEnd_5925365 := by
    simpa [prefixWord, tailWord_5925365, baseEnd_5925365] using wordTrace_append hprefix tailTrace_5925365
  have hstable : (prefixWord ++ tailWord_5925365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925365).length < 2 ^ (prefixWord ++ tailWord_5925365).sum := by decide
  have hdescent : baseEnd_5925365 < baseStart_5925365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925382 : List Nat := [6, 2, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_5925382 : Nat := 118140960795 + 5925382 * 2 ^ 59
def prefixEnd_5925382 : Nat := 4983230072969 + 3 ^ 40 * 5925382 * 2
def baseEnd_5925382 : Nat := 1014189675833147049791557

theorem tailTrace_5925382 : CollatzResearch.WordTrace tailWord_5925382 prefixEnd_5925382 1014189675833147049791557 := by
  unfold tailWord_5925382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6753638631855014485102825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 144077624146240309015526933 6753638631855014485102825)
  ·
    refine ⟨5065228973891260863827119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6753638631855014485102825 5065228973891260863827119)
    ·
      refine ⟨7597843460836891295740679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5065228973891260863827119 7597843460836891295740679)
      ·
        refine ⟨11396765191255336943611019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7597843460836891295740679 11396765191255336943611019)
        ·
          refine ⟨17095147786883005415416529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11396765191255336943611019 17095147786883005415416529)
          ·
            refine ⟨12821360840162254061562397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17095147786883005415416529 12821360840162254061562397)
            ·
              refine ⟨4808010315060845273085899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12821360840162254061562397 4808010315060845273085899)
              ·
                refine ⟨7212015472591267909628849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4808010315060845273085899 7212015472591267909628849)
                ·
                  refine ⟨5409011604443450932221637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7212015472591267909628849 5409011604443450932221637)
                  ·
                    refine ⟨1014189675833147049791557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5409011604443450932221637 1014189675833147049791557)
                    ·
                      rfl

theorem cell23_5925382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_5925382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925382 prefixEnd_5925382 := by exact prefixLift 5925382
  have htrace : WordTrace (prefixWord ++ tailWord_5925382) baseStart_5925382 baseEnd_5925382 := by
    simpa [prefixWord, tailWord_5925382, baseEnd_5925382] using wordTrace_append hprefix tailTrace_5925382
  have hstable : (prefixWord ++ tailWord_5925382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925382).length < 2 ^ (prefixWord ++ tailWord_5925382).sum := by decide
  have hdescent : baseEnd_5925382 < baseStart_5925382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925387 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 2, 6]
def baseStart_5925387 : Nat := 118140960795 + 5925387 * 2 ^ 59
def prefixEnd_5925387 : Nat := 4983230072969 + 3 ^ 40 * 5925387 * 2
def baseEnd_5925387 : Nat := 1014190531634237876604049

theorem tailTrace_5925387 : CollatzResearch.WordTrace tailWord_5925387 prefixEnd_5925387 1014190531634237876604049 := by
  unfold tailWord_5925387
  simp only [CollatzResearch.WordTrace]
  refine ⟨216116618584342349377222415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144077745722894899584814943 216116618584342349377222415)
  ·
    refine ⟨324174927876513524065833623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216116618584342349377222415 324174927876513524065833623)
    ·
      refine ⟨486262391814770286098750435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324174927876513524065833623 486262391814770286098750435)
      ·
        refine ⟨729393587722155429148125653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486262391814770286098750435 729393587722155429148125653)
        ·
          refine ⟨17095162212238017870659195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 729393587722155429148125653 17095162212238017870659195)
          ·
            refine ⟨25642743318357026805988793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17095162212238017870659195 25642743318357026805988793)
            ·
              refine ⟨19232057488767770104491595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25642743318357026805988793 19232057488767770104491595)
              ·
                refine ⟨28848086233151655156737393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19232057488767770104491595 28848086233151655156737393)
                ·
                  refine ⟨21636064674863741367553045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28848086233151655156737393 21636064674863741367553045)
                  ·
                    refine ⟨1014190531634237876604049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21636064674863741367553045 1014190531634237876604049)
                    ·
                      rfl

theorem cell23_5925387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 6].length) (baseStart_5925387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925387 prefixEnd_5925387 := by exact prefixLift 5925387
  have htrace : WordTrace (prefixWord ++ tailWord_5925387) baseStart_5925387 baseEnd_5925387 := by
    simpa [prefixWord, tailWord_5925387, baseEnd_5925387] using wordTrace_append hprefix tailTrace_5925387
  have hstable : (prefixWord ++ tailWord_5925387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925387).length < 2 ^ (prefixWord ++ tailWord_5925387).sum := by decide
  have hdescent : baseEnd_5925387 < baseStart_5925387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925388 : List Nat := [2, 2, 1, 2, 4, 2, 3, 1, 2, 1, 3]
def baseStart_5925388 : Nat := 118140960795 + 5925388 * 2 ^ 59
def prefixEnd_5925388 : Nat := 4983230072969 + 3 ^ 40 * 5925388 * 2
def baseEnd_5925388 : Nat := 3042572108383368125899643

theorem tailTrace_5925388 : CollatzResearch.WordTrace tailWord_5925388 prefixEnd_5925388 3042572108383368125899643 := by
  unfold tailWord_5925388
  simp only [CollatzResearch.WordTrace]
  refine ⟨108058327528669363274004409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144077770038225817698672545 108058327528669363274004409)
  ·
    refine ⟨81043745646502022455503307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108058327528669363274004409 81043745646502022455503307)
    ·
      refine ⟨121565618469753033683254961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81043745646502022455503307 121565618469753033683254961)
      ·
        refine ⟨91174213852314775262441221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121565618469753033683254961 91174213852314775262441221)
        ·
          refine ⟨17095165097309020361707729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91174213852314775262441221 17095165097309020361707729)
          ·
            refine ⟨12821373822981765271280797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17095165097309020361707729 12821373822981765271280797)
            ·
              refine ⟨4808015183618161976730299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12821373822981765271280797 4808015183618161976730299)
              ·
                refine ⟨7212022775427242965095449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4808015183618161976730299 7212022775427242965095449)
                ·
                  refine ⟨5409017081570432223821587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7212022775427242965095449 5409017081570432223821587)
                  ·
                    refine ⟨8113525622355648335732381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5409017081570432223821587 8113525622355648335732381)
                    ·
                      refine ⟨3042572108383368125899643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8113525622355648335732381 3042572108383368125899643)
                      ·
                        rfl

theorem cell23_5925388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_5925388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925388 prefixEnd_5925388 := by exact prefixLift 5925388
  have htrace : WordTrace (prefixWord ++ tailWord_5925388) baseStart_5925388 baseEnd_5925388 := by
    simpa [prefixWord, tailWord_5925388, baseEnd_5925388] using wordTrace_append hprefix tailTrace_5925388
  have hstable : (prefixWord ++ tailWord_5925388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925388).length < 2 ^ (prefixWord ++ tailWord_5925388).sum := by decide
  have hdescent : baseEnd_5925388 < baseStart_5925388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925397 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_5925397 : Nat := 118140960795 + 5925397 * 2 ^ 59
def prefixEnd_5925397 : Nat := 4983230072969 + 3 ^ 40 * 5925397 * 2
def baseEnd_5925397 : Nat := 3042576729709258590687101

theorem tailTrace_5925397 : CollatzResearch.WordTrace tailWord_5925397 prefixEnd_5925397 3042576729709258590687101 := by
  unfold tailWord_5925397
  simp only [CollatzResearch.WordTrace]
  refine ⟨216116983314306121085086445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144077988876204080723390963 216116983314306121085086445)
  ·
    refine ⟨81043868742864795406907417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216116983314306121085086445 81043868742864795406907417)
    ·
      refine ⟨60782901557148596555180563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81043868742864795406907417 60782901557148596555180563)
      ·
        refine ⟨91174352335722894832770845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60782901557148596555180563 91174352335722894832770845)
        ·
          refine ⟨34190382125896085562289067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91174352335722894832770845 34190382125896085562289067)
          ·
            refine ⟨51285573188844128343433601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34190382125896085562289067 51285573188844128343433601)
            ·
              refine ⟨38464179891633096257575201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51285573188844128343433601 38464179891633096257575201)
              ·
                refine ⟨28848134918724822193181401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38464179891633096257575201 28848134918724822193181401)
                ·
                  refine ⟨21636101189043616644886051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28848134918724822193181401 21636101189043616644886051)
                  ·
                    refine ⟨32454151783565424967329077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21636101189043616644886051 32454151783565424967329077)
                    ·
                      refine ⟨3042576729709258590687101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32454151783565424967329077 3042576729709258590687101)
                      ·
                        rfl

theorem cell23_5925397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_5925397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925397 prefixEnd_5925397 := by exact prefixLift 5925397
  have htrace : WordTrace (prefixWord ++ tailWord_5925397) baseStart_5925397 baseEnd_5925397 := by
    simpa [prefixWord, tailWord_5925397, baseEnd_5925397] using wordTrace_append hprefix tailTrace_5925397
  have hstable : (prefixWord ++ tailWord_5925397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925397).length < 2 ^ (prefixWord ++ tailWord_5925397).sum := by decide
  have hdescent : baseEnd_5925397 < baseStart_5925397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925411 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 4, 2, 2]
def baseStart_5925411 : Nat := 118140960795 + 5925411 * 2 ^ 59
def prefixEnd_5925411 : Nat := 4983230072969 + 3 ^ 40 * 5925411 * 2
def baseEnd_5925411 : Nat := 3042583918438421535912037

theorem tailTrace_5925411 : CollatzResearch.WordTrace tailWord_5925411 prefixEnd_5925411 3042583918438421535912037 := by
  unfold tailWord_5925411
  simp only [CollatzResearch.WordTrace]
  refine ⟨216117493936255401476096087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144078329290836934317397391 216117493936255401476096087)
  ·
    refine ⟨324176240904383102214144131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216117493936255401476096087 324176240904383102214144131)
    ·
      refine ⟨486264361356574653321216197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324176240904383102214144131 486264361356574653321216197)
      ·
        refine ⟨91174567754357747497728037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 486264361356574653321216197 91174567754357747497728037)
        ·
          refine ⟨17095231453942077655824007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91174567754357747497728037 17095231453942077655824007)
          ·
            refine ⟨25642847180913116483736011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17095231453942077655824007 25642847180913116483736011)
            ·
              refine ⟨38464270771369674725604017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25642847180913116483736011 38464270771369674725604017)
              ·
                refine ⟨28848203078527256044203013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38464270771369674725604017 28848203078527256044203013)
                ·
                  refine ⟨5409038077223860508288065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28848203078527256044203013 5409038077223860508288065)
                  ·
                    refine ⟨4056778557917895381216049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5409038077223860508288065 4056778557917895381216049)
                    ·
                      refine ⟨3042583918438421535912037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4056778557917895381216049 3042583918438421535912037)
                      ·
                        rfl

theorem cell23_5925411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_5925411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925411 prefixEnd_5925411 := by exact prefixLift 5925411
  have htrace : WordTrace (prefixWord ++ tailWord_5925411) baseStart_5925411 baseEnd_5925411 := by
    simpa [prefixWord, tailWord_5925411, baseEnd_5925411] using wordTrace_append hprefix tailTrace_5925411
  have hstable : (prefixWord ++ tailWord_5925411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925411).length < 2 ^ (prefixWord ++ tailWord_5925411).sum := by decide
  have hdescent : baseEnd_5925411 < baseStart_5925411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925434 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 7]
def baseStart_5925434 : Nat := 118140960795 + 5925434 * 2 ^ 59
def prefixEnd_5925434 : Nat := 4983230072969 + 3 ^ 40 * 5925434 * 2
def baseEnd_5925434 : Nat := 338066192054830549547159

theorem tailTrace_5925434 : CollatzResearch.WordTrace tailWord_5925434 prefixEnd_5925434 338066192054830549547159 := by
  unfold tailWord_5925434
  simp only [CollatzResearch.WordTrace]
  refine ⟨54029583203793019101045839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144078888543448050936122237 54029583203793019101045839)
  ·
    refine ⟨81044374805689528651568759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54029583203793019101045839 81044374805689528651568759)
    ·
      refine ⟨121566562208534292977353139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81044374805689528651568759 121566562208534292977353139)
      ·
        refine ⟨182349843312801439466029709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121566562208534292977353139 182349843312801439466029709)
        ·
          refine ⟨68381191242300539799761141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182349843312801439466029709 68381191242300539799761141)
          ·
            refine ⟨6410736678965675606227607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68381191242300539799761141 6410736678965675606227607)
            ·
              refine ⟨9616105018448513409341411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6410736678965675606227607 9616105018448513409341411)
              ·
                refine ⟨14424157527672770114012117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9616105018448513409341411 14424157527672770114012117)
                ·
                  refine ⟨338066192054830549547159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14424157527672770114012117 338066192054830549547159)
                  ·
                    rfl

theorem cell23_5925434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_5925434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925434 prefixEnd_5925434 := by exact prefixLift 5925434
  have htrace : WordTrace (prefixWord ++ tailWord_5925434) baseStart_5925434 baseEnd_5925434 := by
    simpa [prefixWord, tailWord_5925434, baseEnd_5925434] using wordTrace_append hprefix tailTrace_5925434
  have hstable : (prefixWord ++ tailWord_5925434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925434).length < 2 ^ (prefixWord ++ tailWord_5925434).sum := by decide
  have hdescent : baseEnd_5925434 < baseStart_5925434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925445 : List Nat := [1, 3, 1, 1, 1, 7, 2, 1, 2, 2, 2]
def baseStart_5925445 : Nat := 118140960795 + 5925445 * 2 ^ 59
def prefixEnd_5925445 : Nat := 4983230072969 + 3 ^ 40 * 5925445 * 2
def baseEnd_5925445 : Nat := 3042601376780674402886881

theorem tailTrace_5925445 : CollatzResearch.WordTrace tailWord_5925445 prefixEnd_5925445 3042601376780674402886881 := by
  unfold tailWord_5925445
  simp only [CollatzResearch.WordTrace]
  refine ⟨216118734018132225282833789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144079156012088150188555859 216118734018132225282833789)
  ·
    refine ⟨81044525256799584481062671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216118734018132225282833789 81044525256799584481062671)
    ·
      refine ⟨121566787885199376721594007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81044525256799584481062671 121566787885199376721594007)
      ·
        refine ⟨182350181827799065082391011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121566787885199376721594007 182350181827799065082391011)
        ·
          refine ⟨273525272741698597623586517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182350181827799065082391011 273525272741698597623586517)
          ·
            refine ⟨6410748579883560881802809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 273525272741698597623586517 6410748579883560881802809)
            ·
              refine ⟨4808061434912670661352107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6410748579883560881802809 4808061434912670661352107)
              ·
                refine ⟨7212092152369005992028161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4808061434912670661352107 7212092152369005992028161)
                ·
                  refine ⟨5409069114276754494021121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7212092152369005992028161 5409069114276754494021121)
                  ·
                    refine ⟨4056801835707565870515841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5409069114276754494021121 4056801835707565870515841)
                    ·
                      refine ⟨3042601376780674402886881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4056801835707565870515841 3042601376780674402886881)
                      ·
                        rfl

theorem cell23_5925445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 2, 2, 2].length) (baseStart_5925445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925445 prefixEnd_5925445 := by exact prefixLift 5925445
  have htrace : WordTrace (prefixWord ++ tailWord_5925445) baseStart_5925445 baseEnd_5925445 := by
    simpa [prefixWord, tailWord_5925445, baseEnd_5925445] using wordTrace_append hprefix tailTrace_5925445
  have hstable : (prefixWord ++ tailWord_5925445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925445).length < 2 ^ (prefixWord ++ tailWord_5925445).sum := by decide
  have hdescent : baseEnd_5925445 < baseStart_5925445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925484 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_5925484 : Nat := 118140960795 + 5925484 * 2 ^ 59
def prefixEnd_5925484 : Nat := 4983230072969 + 3 ^ 40 * 5925484 * 2
def baseEnd_5925484 : Nat := 3042621402526199750299201

theorem tailTrace_5925484 : CollatzResearch.WordTrace tailWord_5925484 prefixEnd_5925484 3042621402526199750299201 := by
  unfold tailWord_5925484
  simp only [CollatzResearch.WordTrace]
  refine ⟨108060078232495467471751753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144080104309993956629002337 108060078232495467471751753)
  ·
    refine ⟨81045058674371600603813815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108060078232495467471751753 81045058674371600603813815)
    ·
      refine ⟨121567588011557400905720723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81045058674371600603813815 121567588011557400905720723)
      ·
        refine ⟨182351382017336101358581085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121567588011557400905720723 182351382017336101358581085)
        ·
          refine ⟨68381768256501038009467907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182351382017336101358581085 68381768256501038009467907)
          ·
            refine ⟨102572652384751557014201861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68381768256501038009467907 102572652384751557014201861)
            ·
              refine ⟨19232372322140916940162849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102572652384751557014201861 19232372322140916940162849)
              ·
                refine ⟨14424279241605687705122137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19232372322140916940162849 14424279241605687705122137)
                ·
                  refine ⟨10818209431204265778841603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14424279241605687705122137 10818209431204265778841603)
                  ·
                    refine ⟨16227314146806398668262405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10818209431204265778841603 16227314146806398668262405)
                    ·
                      refine ⟨3042621402526199750299201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16227314146806398668262405 3042621402526199750299201)
                      ·
                        rfl

theorem cell23_5925484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_5925484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925484 prefixEnd_5925484 := by exact prefixLift 5925484
  have htrace : WordTrace (prefixWord ++ tailWord_5925484) baseStart_5925484 baseEnd_5925484 := by
    simpa [prefixWord, tailWord_5925484, baseEnd_5925484] using wordTrace_append hprefix tailTrace_5925484
  have hstable : (prefixWord ++ tailWord_5925484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925484).length < 2 ^ (prefixWord ++ tailWord_5925484).sum := by decide
  have hdescent : baseEnd_5925484 < baseStart_5925484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925528 : List Nat := [2, 1, 2, 4, 1, 1, 4, 3, 1, 4]
def baseStart_5925528 : Nat := 118140960795 + 5925528 * 2 ^ 59
def prefixEnd_5925528 : Nat := 4983230072969 + 3 ^ 40 * 5925528 * 2
def baseEnd_5925528 : Nat := 1014214665224999192716333

theorem tailTrace_5925528 : CollatzResearch.WordTrace tailWord_5925528 prefixEnd_5925528 1014214665224999192716333 := by
  unfold tailWord_5925528
  simp only [CollatzResearch.WordTrace]
  refine ⟨108060880638415765229052619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144081174184554353638736825 108060880638415765229052619)
  ·
    refine ⟨162091320957623647843578929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108060880638415765229052619 162091320957623647843578929)
    ·
      refine ⟨121568490718217735882684197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162091320957623647843578929 121568490718217735882684197)
      ·
        refine ⟨22794092009665825478003287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121568490718217735882684197 22794092009665825478003287)
        ·
          refine ⟨34191138014498738217004931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22794092009665825478003287 34191138014498738217004931)
          ·
            refine ⟨51286707021748107325507397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34191138014498738217004931 51286707021748107325507397)
            ·
              refine ⟨9616257566577770123532637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51286707021748107325507397 9616257566577770123532637)
              ·
                refine ⟨3606096587466663796324739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9616257566577770123532637 3606096587466663796324739)
                ·
                  refine ⟨5409144881199995694487109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3606096587466663796324739 5409144881199995694487109)
                  ·
                    refine ⟨1014214665224999192716333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5409144881199995694487109 1014214665224999192716333)
                    ·
                      rfl

theorem cell23_5925528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_5925528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925528 prefixEnd_5925528 := by exact prefixLift 5925528
  have htrace : WordTrace (prefixWord ++ tailWord_5925528) baseStart_5925528 baseEnd_5925528 := by
    simpa [prefixWord, tailWord_5925528, baseEnd_5925528] using wordTrace_append hprefix tailTrace_5925528
  have hstable : (prefixWord ++ tailWord_5925528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925528).length < 2 ^ (prefixWord ++ tailWord_5925528).sum := by decide
  have hdescent : baseEnd_5925528 < baseStart_5925528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925551 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 3, 1, 3]
def baseStart_5925551 : Nat := 118140960795 + 5925551 * 2 ^ 59
def prefixEnd_5925551 : Nat := 4983230072969 + 3 ^ 40 * 5925551 * 2
def baseEnd_5925551 : Nat := 3042655805730050988161393

theorem tailTrace_5925551 : CollatzResearch.WordTrace tailWord_5925551 prefixEnd_5925551 3042655805730050988161393 := by
  unfold tailWord_5925551
  simp only [CollatzResearch.WordTrace]
  refine ⟨216122600155748205386192507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144081733437165470257461671 216122600155748205386192507)
  ·
    refine ⟨324183900233622308079288761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216122600155748205386192507 324183900233622308079288761)
    ·
      refine ⟨243137925175216731059466571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324183900233622308079288761 243137925175216731059466571)
      ·
        refine ⟨364706887762825096589199857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243137925175216731059466571 364706887762825096589199857)
        ·
          refine ⟨273530165822118822441899893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364706887762825096589199857 273530165822118822441899893)
          ·
            refine ⟨25643453045823639603928115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 273530165822118822441899893 25643453045823639603928115)
            ·
              refine ⟨38465179568735459405892173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25643453045823639603928115 38465179568735459405892173)
              ·
                refine ⟨14424442338275797277209565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38465179568735459405892173 14424442338275797277209565)
                ·
                  refine ⟨5409165876853423978953587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14424442338275797277209565 5409165876853423978953587)
                  ·
                    refine ⟨8113748815280135968430381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5409165876853423978953587 8113748815280135968430381)
                    ·
                      refine ⟨3042655805730050988161393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8113748815280135968430381 3042655805730050988161393)
                      ·
                        rfl

theorem cell23_5925551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 1, 3].length) (baseStart_5925551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925551 prefixEnd_5925551 := by exact prefixLift 5925551
  have htrace : WordTrace (prefixWord ++ tailWord_5925551) baseStart_5925551 baseEnd_5925551 := by
    simpa [prefixWord, tailWord_5925551, baseEnd_5925551] using wordTrace_append hprefix tailTrace_5925551
  have hstable : (prefixWord ++ tailWord_5925551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925551).length < 2 ^ (prefixWord ++ tailWord_5925551).sum := by decide
  have hdescent : baseEnd_5925551 < baseStart_5925551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925591 : List Nat := [1, 1, 3, 2, 1, 4, 2, 3, 1, 1, 4]
def baseStart_5925591 : Nat := 118140960795 + 5925591 * 2 ^ 59
def prefixEnd_5925591 : Nat := 4983230072969 + 3 ^ 40 * 5925591 * 2
def baseEnd_5925591 : Nat := 3042676344956230831661209

theorem tailTrace_5925591 : CollatzResearch.WordTrace tailWord_5925591 prefixEnd_5925591 3042676344956230831661209 := by
  unfold tailWord_5925591
  simp only [CollatzResearch.WordTrace]
  refine ⟨216124059075603292217648627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144082706050402194811765751 216124059075603292217648627)
  ·
    refine ⟨324186088613404938326472941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216124059075603292217648627 324186088613404938326472941)
    ·
      refine ⟨121569783230026851872427353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324186088613404938326472941 121569783230026851872427353)
      ·
        refine ⟨91177337422520138904320515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121569783230026851872427353 91177337422520138904320515)
        ·
          refine ⟨136766006133780208356480773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91177337422520138904320515 136766006133780208356480773)
          ·
            refine ⟨25643626150083789066840145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136766006133780208356480773 25643626150083789066840145)
            ·
              refine ⟨19232719612562841800130109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25643626150083789066840145 19232719612562841800130109)
              ·
                refine ⟨7212269854711065675048791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19232719612562841800130109 7212269854711065675048791)
                ·
                  refine ⟨10818404782066598512573187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7212269854711065675048791 10818404782066598512573187)
                  ·
                    refine ⟨16227607173099897768859781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10818404782066598512573187 16227607173099897768859781)
                    ·
                      refine ⟨3042676344956230831661209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16227607173099897768859781 3042676344956230831661209)
                      ·
                        rfl

theorem cell23_5925591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_5925591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925591 prefixEnd_5925591 := by exact prefixLift 5925591
  have htrace : WordTrace (prefixWord ++ tailWord_5925591) baseStart_5925591 baseEnd_5925591 := by
    simpa [prefixWord, tailWord_5925591, baseEnd_5925591] using wordTrace_append hprefix tailTrace_5925591
  have hstable : (prefixWord ++ tailWord_5925591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925591).length < 2 ^ (prefixWord ++ tailWord_5925591).sum := by decide
  have hdescent : baseEnd_5925591 < baseStart_5925591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925601 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 4, 4]
def baseStart_5925601 : Nat := 118140960795 + 5925601 * 2 ^ 59
def prefixEnd_5925601 : Nat := 4983230072969 + 3 ^ 40 * 5925601 * 2
def baseEnd_5925601 : Nat := 1014227159920925264178721

theorem tailTrace_5925601 : CollatzResearch.WordTrace tailWord_5925601 prefixEnd_5925601 1014227159920925264178721 := by
  unfold tailWord_5925601
  simp only [CollatzResearch.WordTrace]
  refine ⟨216124423805567063925512657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144082949203711375950341771 216124423805567063925512657)
  ·
    refine ⟨162093317854175297944134493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216124423805567063925512657 162093317854175297944134493)
    ·
      refine ⟨60784994195315736729050435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162093317854175297944134493 60784994195315736729050435)
      ·
        refine ⟨91177491292973605093575653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60784994195315736729050435 91177491292973605093575653)
        ·
          refine ⟨17095779617432550955045435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91177491292973605093575653 17095779617432550955045435)
          ·
            refine ⟨25643669426148826432568153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17095779617432550955045435 25643669426148826432568153)
            ·
              refine ⟨19232752069611619824426115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25643669426148826432568153 19232752069611619824426115)
              ·
                refine ⟨28849128104417429736639173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19232752069611619824426115 28849128104417429736639173)
                ·
                  refine ⟨5409211519578268075619845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28849128104417429736639173 5409211519578268075619845)
                  ·
                    refine ⟨1014227159920925264178721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5409211519578268075619845 1014227159920925264178721)
                    ·
                      rfl

theorem cell23_5925601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_5925601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925601 prefixEnd_5925601 := by exact prefixLift 5925601
  have htrace : WordTrace (prefixWord ++ tailWord_5925601) baseStart_5925601 baseEnd_5925601 := by
    simpa [prefixWord, tailWord_5925601, baseEnd_5925601] using wordTrace_append hprefix tailTrace_5925601
  have hstable : (prefixWord ++ tailWord_5925601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925601).length < 2 ^ (prefixWord ++ tailWord_5925601).sum := by decide
  have hdescent : baseEnd_5925601 < baseStart_5925601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925604 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_5925604 : Nat := 118140960795 + 5925604 * 2 ^ 59
def prefixEnd_5925604 : Nat := 4983230072969 + 3 ^ 40 * 5925604 * 2
def baseEnd_5925604 : Nat := 3042683020204739280798649

theorem tailTrace_5925604 : CollatzResearch.WordTrace tailWord_5925604 prefixEnd_5925604 3042683020204739280798649 := by
  unfold tailWord_5925604
  simp only [CollatzResearch.WordTrace]
  refine ⟨108062266612278097718935933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144083022149704130291914577 108062266612278097718935933)
  ·
    refine ⟨40523349979604286644600975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108062266612278097718935933 40523349979604286644600975)
    ·
      refine ⟨60785024969406429966901463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40523349979604286644600975 60785024969406429966901463)
      ·
        refine ⟨91177537454109644950352195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60785024969406429966901463 91177537454109644950352195)
        ·
          refine ⟨136766306181164467425528293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91177537454109644950352195 136766306181164467425528293)
          ·
            refine ⟨25643682408968337642286555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136766306181164467425528293 25643682408968337642286555)
            ·
              refine ⟨38465523613452506463429833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25643682408968337642286555 38465523613452506463429833)
              ·
                refine ⟨28849142710089379847572375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38465523613452506463429833 28849142710089379847572375)
                ·
                  refine ⟨43273714065134069771358563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28849142710089379847572375 43273714065134069771358563)
                  ·
                    refine ⟨64910571097701104657037845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43273714065134069771358563 64910571097701104657037845)
                    ·
                      refine ⟨3042683020204739280798649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64910571097701104657037845 3042683020204739280798649)
                      ·
                        rfl

theorem cell23_5925604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_5925604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925604 prefixEnd_5925604 := by exact prefixLift 5925604
  have htrace : WordTrace (prefixWord ++ tailWord_5925604) baseStart_5925604 baseEnd_5925604 := by
    simpa [prefixWord, tailWord_5925604, baseEnd_5925604] using wordTrace_append hprefix tailTrace_5925604
  have hstable : (prefixWord ++ tailWord_5925604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925604).length < 2 ^ (prefixWord ++ tailWord_5925604).sum := by decide
  have hdescent : baseEnd_5925604 < baseStart_5925604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925614 : List Nat := [4, 1, 2, 1, 1, 3, 1, 10]
def baseStart_5925614 : Nat := 118140960795 + 5925614 * 2 ^ 59
def prefixEnd_5925614 : Nat := 4983230072969 + 3 ^ 40 * 5925614 * 2
def baseEnd_5925614 : Nat := 112692153889306823765689

theorem tailTrace_5925614 : CollatzResearch.WordTrace tailWord_5925614 prefixEnd_5925614 112692153889306823765689 := by
  unfold tailWord_5925614
  simp only [CollatzResearch.WordTrace]
  refine ⟨27015612244314995893216987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144083265303013311430490597 27015612244314995893216987)
  ·
    refine ⟨40523418366472493839825481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27015612244314995893216987 40523418366472493839825481)
    ·
      refine ⟨30392563774854370379869111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40523418366472493839825481 30392563774854370379869111)
      ·
        refine ⟨45588845662281555569803667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30392563774854370379869111 45588845662281555569803667)
        ·
          refine ⟨68383268493422333354705501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45588845662281555569803667 68383268493422333354705501)
          ·
            refine ⟨25643725685033375008014563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68383268493422333354705501 25643725685033375008014563)
            ·
              refine ⟨38465588527550062512021845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25643725685033375008014563 38465588527550062512021845)
              ·
                refine ⟨112692153889306823765689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38465588527550062512021845 112692153889306823765689)
                ·
                  rfl

theorem cell23_5925614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_5925614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925614 prefixEnd_5925614 := by exact prefixLift 5925614
  have htrace : WordTrace (prefixWord ++ tailWord_5925614) baseStart_5925614 baseEnd_5925614 := by
    simpa [prefixWord, tailWord_5925614, baseEnd_5925614] using wordTrace_append hprefix tailTrace_5925614
  have hstable : (prefixWord ++ tailWord_5925614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925614).length < 2 ^ (prefixWord ++ tailWord_5925614).sum := by decide
  have hdescent : baseEnd_5925614 < baseStart_5925614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925618 : List Nat := [3, 2, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_5925618 : Nat := 118140960795 + 5925618 * 2 ^ 59
def prefixEnd_5925618 : Nat := 4983230072969 + 3 ^ 40 * 5925618 * 2
def baseEnd_5925618 : Nat := 1014230069644634075341195

theorem tailTrace_5925618 : CollatzResearch.WordTrace tailWord_5925618 prefixEnd_5925618 1014230069644634075341195 := by
  unfold tailWord_5925618
  simp only [CollatzResearch.WordTrace]
  refine ⟨54031260961626368957220377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144083362564336983885921005 54031260961626368957220377)
  ·
    refine ⟨40523445721219776717915283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54031260961626368957220377 40523445721219776717915283)
    ·
      refine ⟨60785168581829665076872925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40523445721219776717915283 60785168581829665076872925)
      ·
        refine ⟨22794438218186124403827347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60785168581829665076872925 22794438218186124403827347)
        ·
          refine ⟨34191657327279186605741021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22794438218186124403827347 34191657327279186605741021)
          ·
            refine ⟨12821871497729694977152883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34191657327279186605741021 12821871497729694977152883)
            ·
              refine ⟨19232807246594542465729325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12821871497729694977152883 19232807246594542465729325)
              ·
                refine ⟨7212302717472953424648497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19232807246594542465729325 7212302717472953424648497)
                ·
                  refine ⟨5409227038104715068486373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7212302717472953424648497 5409227038104715068486373)
                  ·
                    refine ⟨1014230069644634075341195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5409227038104715068486373 1014230069644634075341195)
                    ·
                      rfl

theorem cell23_5925618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_5925618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925618 prefixEnd_5925618 := by exact prefixLift 5925618
  have htrace : WordTrace (prefixWord ++ tailWord_5925618) baseStart_5925618 baseEnd_5925618 := by
    simpa [prefixWord, tailWord_5925618, baseEnd_5925618] using wordTrace_append hprefix tailTrace_5925618
  have hstable : (prefixWord ++ tailWord_5925618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925618).length < 2 ^ (prefixWord ++ tailWord_5925618).sum := by decide
  have hdescent : baseEnd_5925618 < baseStart_5925618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925628 : List Nat := [2, 2, 2, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_5925628 : Nat := 118140960795 + 5925628 * 2 ^ 59
def prefixEnd_5925628 : Nat := 4983230072969 + 3 ^ 40 * 5925628 * 2
def baseEnd_5925628 : Nat := 3042695343740447186898539

theorem tailTrace_5925628 : CollatzResearch.WordTrace tailWord_5925628 prefixEnd_5925628 3042695343740447186898539 := by
  unfold tailWord_5925628
  simp only [CollatzResearch.WordTrace]
  refine ⟨108062704288234623768372769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144083605717646165024497025 108062704288234623768372769)
  ·
    refine ⟨81047028216175967826279577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108062704288234623768372769 81047028216175967826279577)
    ·
      refine ⟨60785271162131975869709683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81047028216175967826279577 60785271162131975869709683)
      ·
        refine ⟨91177906743197963804564525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60785271162131975869709683 91177906743197963804564525)
        ·
          refine ⟨34191715028699236426711697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91177906743197963804564525 34191715028699236426711697)
          ·
            refine ⟨25643786271524427320033773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34191715028699236426711697 25643786271524427320033773)
            ·
              refine ⟨9616419851821660245012665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25643786271524427320033773 9616419851821660245012665)
              ·
                refine ⟨7212314888866245183759499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9616419851821660245012665 7212314888866245183759499)
                ·
                  refine ⟨10818472333299367775639249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7212314888866245183759499 10818472333299367775639249)
                  ·
                    refine ⟨8113854249974525831729437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10818472333299367775639249 8113854249974525831729437)
                    ·
                      refine ⟨3042695343740447186898539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8113854249974525831729437 3042695343740447186898539)
                      ·
                        rfl

theorem cell23_5925628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_5925628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925628 prefixEnd_5925628 := by exact prefixLift 5925628
  have htrace : WordTrace (prefixWord ++ tailWord_5925628) baseStart_5925628 baseEnd_5925628 := by
    simpa [prefixWord, tailWord_5925628, baseEnd_5925628] using wordTrace_append hprefix tailTrace_5925628
  have hstable : (prefixWord ++ tailWord_5925628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925628).length < 2 ^ (prefixWord ++ tailWord_5925628).sum := by decide
  have hdescent : baseEnd_5925628 < baseStart_5925628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925641 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 6, 1, 3]
def baseStart_5925641 : Nat := 118140960795 + 5925641 * 2 ^ 59
def prefixEnd_5925641 : Nat := 4983230072969 + 3 ^ 40 * 5925641 * 2
def baseEnd_5925641 : Nat := 3042702018988955636035979

theorem tailTrace_5925641 : CollatzResearch.WordTrace tailWord_5925641 prefixEnd_5925641 3042702018988955636035979 := by
  unfold tailWord_5925641
  simp only [CollatzResearch.WordTrace]
  refine ⟨216125882725422150756968777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144083921816948100504645851 216125882725422150756968777)
  ·
    refine ⟨162094412044066613067726583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216125882725422150756968777 162094412044066613067726583)
    ·
      refine ⟨243141618066099919601589875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162094412044066613067726583 243141618066099919601589875)
      ·
        refine ⟨364712427099149879402384813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243141618066099919601589875 364712427099149879402384813)
        ·
          refine ⟨136767160162181204775894305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364712427099149879402384813 136767160162181204775894305)
          ·
            refine ⟨102575370121635903581920729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136767160162181204775894305 102575370121635903581920729)
            ·
              refine ⟨76931527591226927686440547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102575370121635903581920729 76931527591226927686440547)
              ·
                refine ⟨115397291386840391529660821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76931527591226927686440547 115397291386840391529660821)
                ·
                  refine ⟨5409248033758143352952851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115397291386840391529660821 5409248033758143352952851)
                  ·
                    refine ⟨8113872050637215029429277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5409248033758143352952851 8113872050637215029429277)
                    ·
                      refine ⟨3042702018988955636035979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8113872050637215029429277 3042702018988955636035979)
                      ·
                        rfl

theorem cell23_5925641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 1, 3].length) (baseStart_5925641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925641 prefixEnd_5925641 := by exact prefixLift 5925641
  have htrace : WordTrace (prefixWord ++ tailWord_5925641) baseStart_5925641 baseEnd_5925641 := by
    simpa [prefixWord, tailWord_5925641, baseEnd_5925641] using wordTrace_append hprefix tailTrace_5925641
  have hstable : (prefixWord ++ tailWord_5925641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925641).length < 2 ^ (prefixWord ++ tailWord_5925641).sum := by decide
  have hdescent : baseEnd_5925641 < baseStart_5925641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925704 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 9]
def baseStart_5925704 : Nat := 118140960795 + 5925704 * 2 ^ 59
def prefixEnd_5925704 : Nat := 4983230072969 + 3 ^ 40 * 5925704 * 2
def baseEnd_5925704 : Nat := 338081596474465432172021

theorem tailTrace_5925704 : CollatzResearch.WordTrace tailWord_5925704 prefixEnd_5925704 338081596474465432172021 := by
  unfold tailWord_5925704
  simp only [CollatzResearch.WordTrace]
  refine ⟨108064090262096956258256083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144085453682795941677674777 108064090262096956258256083)
  ·
    refine ⟨162096135393145434387384125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108064090262096956258256083 162096135393145434387384125)
    ·
      refine ⟨60786050772429537895269047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162096135393145434387384125 60786050772429537895269047)
      ·
        refine ⟨91179076158644306842903571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60786050772429537895269047 91179076158644306842903571)
        ·
          refine ⟨136768614237966460264355357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91179076158644306842903571 136768614237966460264355357)
          ·
            refine ⟨51288230339237422599133259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136768614237966460264355357 51288230339237422599133259)
            ·
              refine ⟨76932345508856133898699889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51288230339237422599133259 76932345508856133898699889)
              ·
                refine ⟨57699259131642100424024917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76932345508856133898699889 57699259131642100424024917)
                ·
                  refine ⟨338081596474465432172021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57699259131642100424024917 338081596474465432172021)
                  ·
                    rfl

theorem cell23_5925704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 9].length) (baseStart_5925704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925704 prefixEnd_5925704 := by exact prefixLift 5925704
  have htrace : WordTrace (prefixWord ++ tailWord_5925704) baseStart_5925704 baseEnd_5925704 := by
    simpa [prefixWord, tailWord_5925704, baseEnd_5925704] using wordTrace_append hprefix tailTrace_5925704
  have hstable : (prefixWord ++ tailWord_5925704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925704).length < 2 ^ (prefixWord ++ tailWord_5925704).sum := by decide
  have hdescent : baseEnd_5925704 < baseStart_5925704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925709 : List Nat := [1, 6, 1, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_5925709 : Nat := 118140960795 + 5925709 * 2 ^ 59
def prefixEnd_5925709 : Nat := 4983230072969 + 3 ^ 40 * 5925709 * 2
def baseEnd_5925709 : Nat := 3042736935673461369985667

theorem tailTrace_5925709 : CollatzResearch.WordTrace tailWord_5925709 prefixEnd_5925709 3042736935673461369985667 := by
  unfold tailWord_5925709
  simp only [CollatzResearch.WordTrace]
  refine ⟨216128362889175798370444181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144085575259450532246962787 216128362889175798370444181)
  ·
    refine ⟨10131017010430115548614571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 216128362889175798370444181 10131017010430115548614571)
    ·
      refine ⟨15196525515645173322921857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10131017010430115548614571 15196525515645173322921857)
      ·
        refine ⟨11397394136733879992191393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15196525515645173322921857 11397394136733879992191393)
        ·
          refine ⟨8548045602550409994143545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11397394136733879992191393 8548045602550409994143545)
          ·
            refine ⟨6411034201912807495607659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8548045602550409994143545 6411034201912807495607659)
            ·
              refine ⟨9616551302869211243411489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6411034201912807495607659 9616551302869211243411489)
              ·
                refine ⟨7212413477151908432558617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9616551302869211243411489 7212413477151908432558617)
                ·
                  refine ⟨5409310107863931324418963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7212413477151908432558617 5409310107863931324418963)
                  ·
                    refine ⟨8113965161795896986628445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5409310107863931324418963 8113965161795896986628445)
                    ·
                      refine ⟨3042736935673461369985667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8113965161795896986628445 3042736935673461369985667)
                      ·
                        rfl

theorem cell23_5925709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_5925709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925709 prefixEnd_5925709 := by exact prefixLift 5925709
  have htrace : WordTrace (prefixWord ++ tailWord_5925709) baseStart_5925709 baseEnd_5925709 := by
    simpa [prefixWord, tailWord_5925709, baseEnd_5925709] using wordTrace_append hprefix tailTrace_5925709
  have hstable : (prefixWord ++ tailWord_5925709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925709).length < 2 ^ (prefixWord ++ tailWord_5925709).sum := by decide
  have hdescent : baseEnd_5925709 < baseStart_5925709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925721 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 7]
def baseStart_5925721 : Nat := 118140960795 + 5925721 * 2 ^ 59
def prefixEnd_5925721 : Nat := 4983230072969 + 3 ^ 40 * 5925721 * 2
def baseEnd_5925721 : Nat := 338082566382368369226179

theorem tailTrace_5925721 : CollatzResearch.WordTrace tailWord_5925721 prefixEnd_5925721 338082566382368369226179 := by
  unfold tailWord_5925721
  simp only [CollatzResearch.WordTrace]
  refine ⟨216128800565132324419881017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144085867043421549613254011 216128800565132324419881017)
  ·
    refine ⟨162096600423849243314910763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216128800565132324419881017 162096600423849243314910763)
    ·
      refine ⟨243144900635773864972366145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162096600423849243314910763 243144900635773864972366145)
      ·
        refine ⟨182358675476830398729274609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243144900635773864972366145 182358675476830398729274609)
        ·
          refine ⟨136769006607622799046955957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182358675476830398729274609 136769006607622799046955957)
          ·
            refine ⟨12822094369464637410652121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136769006607622799046955957 12822094369464637410652121)
            ·
              refine ⟨9616570777098478057989091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12822094369464637410652121 9616570777098478057989091)
              ·
                refine ⟨14424856165647717086983637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9616570777098478057989091 14424856165647717086983637)
                ·
                  refine ⟨338082566382368369226179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14424856165647717086983637 338082566382368369226179)
                  ·
                    rfl

theorem cell23_5925721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 7].length) (baseStart_5925721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925721 prefixEnd_5925721 := by exact prefixLift 5925721
  have htrace : WordTrace (prefixWord ++ tailWord_5925721) baseStart_5925721 baseEnd_5925721 := by
    simpa [prefixWord, tailWord_5925721, baseEnd_5925721] using wordTrace_append hprefix tailTrace_5925721
  have hstable : (prefixWord ++ tailWord_5925721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925721).length < 2 ^ (prefixWord ++ tailWord_5925721).sum := by decide
  have hdescent : baseEnd_5925721 < baseStart_5925721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925768 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 2, 5]
def baseStart_5925768 : Nat := 118140960795 + 5925768 * 2 ^ 59
def prefixEnd_5925768 : Nat := 4983230072969 + 3 ^ 40 * 5925768 * 2
def baseEnd_5925768 : Nat := 1014255743677358879715965

theorem tailTrace_5925768 : CollatzResearch.WordTrace tailWord_5925768 prefixEnd_5925768 1014255743677358879715965 := by
  unfold tailWord_5925768
  simp only [CollatzResearch.WordTrace]
  refine ⟨108065257397981025723420979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144087009863974700964561305 108065257397981025723420979)
  ·
    refine ⟨162097886096971538585131469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108065257397981025723420979 162097886096971538585131469)
    ·
      refine ⟨60786707286364326969424301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162097886096971538585131469 60786707286364326969424301)
      ·
        refine ⟨22795015232386622613534113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60786707286364326969424301 22795015232386622613534113)
        ·
          refine ⟨17096261424289966960150585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22795015232386622613534113 17096261424289966960150585)
          ·
            refine ⟨12822196068217475220112939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17096261424289966960150585 12822196068217475220112939)
            ·
              refine ⟨19233294102326212830169409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12822196068217475220112939 19233294102326212830169409)
              ·
                refine ⟨14424970576744659622627057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19233294102326212830169409 14424970576744659622627057)
                ·
                  refine ⟨10818727932558494716970293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14424970576744659622627057 10818727932558494716970293)
                  ·
                    refine ⟨1014255743677358879715965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10818727932558494716970293 1014255743677358879715965)
                    ·
                      rfl

theorem cell23_5925768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_5925768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925768 prefixEnd_5925768 := by exact prefixLift 5925768
  have htrace : WordTrace (prefixWord ++ tailWord_5925768) baseStart_5925768 baseEnd_5925768 := by
    simpa [prefixWord, tailWord_5925768, baseEnd_5925768] using wordTrace_append hprefix tailTrace_5925768
  have hstable : (prefixWord ++ tailWord_5925768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925768).length < 2 ^ (prefixWord ++ tailWord_5925768).sum := by decide
  have hdescent : baseEnd_5925768 < baseStart_5925768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925771 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 4]
def baseStart_5925771 : Nat := 118140960795 + 5925771 * 2 ^ 59
def prefixEnd_5925771 : Nat := 4983230072969 + 3 ^ 40 * 5925771 * 2
def baseEnd_5925771 : Nat := 3042768771474040127410381

theorem tailTrace_5925771 : CollatzResearch.WordTrace tailWord_5925771 prefixEnd_5925771 3042768771474040127410381 := by
  unfold tailWord_5925771
  simp only [CollatzResearch.WordTrace]
  refine ⟨216130624214951182959201167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144087082809967455306134111 216130624214951182959201167)
  ·
    refine ⟨324195936322426774438801751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216130624214951182959201167 324195936322426774438801751)
    ·
      refine ⟨486293904483640161658202627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324195936322426774438801751 486293904483640161658202627)
      ·
        refine ⟨729440856725460242487303941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486293904483640161658202627 729440856725460242487303941)
        ·
          refine ⟨136770160636023795466369489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 729440856725460242487303941 136770160636023795466369489)
          ·
            refine ⟨102577620477017846599777117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136770160636023795466369489 102577620477017846599777117)
            ·
              refine ⟨38466607678881692474916419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102577620477017846599777117 38466607678881692474916419)
              ·
                refine ⟨57699911518322538712374629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38466607678881692474916419 57699911518322538712374629)
                ·
                  refine ⟨10818733409685476008570243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57699911518322538712374629 10818733409685476008570243)
                  ·
                    refine ⟨16228100114528214012855365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10818733409685476008570243 16228100114528214012855365)
                    ·
                      refine ⟨3042768771474040127410381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16228100114528214012855365 3042768771474040127410381)
                      ·
                        rfl

theorem cell23_5925771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 4].length) (baseStart_5925771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925771 prefixEnd_5925771 := by exact prefixLift 5925771
  have htrace : WordTrace (prefixWord ++ tailWord_5925771) baseStart_5925771 baseEnd_5925771 := by
    simpa [prefixWord, tailWord_5925771, baseEnd_5925771] using wordTrace_append hprefix tailTrace_5925771
  have hstable : (prefixWord ++ tailWord_5925771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925771).length < 2 ^ (prefixWord ++ tailWord_5925771).sum := by decide
  have hdescent : baseEnd_5925771 < baseStart_5925771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925832 : List Nat := [2, 1, 3, 1, 5, 1, 1, 4, 1, 4]
def baseStart_5925832 : Nat := 118140960795 + 5925832 * 2 ^ 59
def prefixEnd_5925832 : Nat := 4983230072969 + 3 ^ 40 * 5925832 * 2
def baseEnd_5925832 : Nat := 1014266697931321462915867

theorem tailTrace_5925832 : CollatzResearch.WordTrace tailWord_5925832 prefixEnd_5925832 1014266697931321462915867 := by
  unfold tailWord_5925832
  simp only [CollatzResearch.WordTrace]
  refine ⟨108066424533865095188585875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144088566045153460251447833 108066424533865095188585875)
  ·
    refine ⟨162099636800797642782878813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108066424533865095188585875 162099636800797642782878813)
    ·
      refine ⟨60787363800299116043579555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162099636800797642782878813 60787363800299116043579555)
      ·
        refine ⟨91181045700448674065369333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60787363800299116043579555 91181045700448674065369333)
        ·
          refine ⟨8548223034417063193628375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91181045700448674065369333 8548223034417063193628375)
          ·
            refine ⟨12822334551625594790442563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8548223034417063193628375 12822334551625594790442563)
            ·
              refine ⟨19233501827438392185663845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12822334551625594790442563 19233501827438392185663845)
              ·
                refine ⟨3606281592644698534811971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19233501827438392185663845 3606281592644698534811971)
                ·
                  refine ⟨5409422388967047802217957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3606281592644698534811971 5409422388967047802217957)
                  ·
                    refine ⟨1014266697931321462915867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5409422388967047802217957 1014266697931321462915867)
                    ·
                      rfl

theorem cell23_5925832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_5925832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925832 prefixEnd_5925832 := by exact prefixLift 5925832
  have htrace : WordTrace (prefixWord ++ tailWord_5925832) baseStart_5925832 baseEnd_5925832 := by
    simpa [prefixWord, tailWord_5925832, baseEnd_5925832] using wordTrace_append hprefix tailTrace_5925832
  have hstable : (prefixWord ++ tailWord_5925832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925832).length < 2 ^ (prefixWord ++ tailWord_5925832).sum := by decide
  have hdescent : baseEnd_5925832 < baseStart_5925832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925841 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 5, 5]
def baseStart_5925841 : Nat := 118140960795 + 5925841 * 2 ^ 59
def prefixEnd_5925841 : Nat := 4983230072969 + 3 ^ 40 * 5925841 * 2
def baseEnd_5925841 : Nat := 1014268238373284951178353

theorem tailTrace_5925841 : CollatzResearch.WordTrace tailWord_5925841 prefixEnd_5925841 1014268238373284951178353 := by
  unfold tailWord_5925841
  simp only [CollatzResearch.WordTrace]
  refine ⟨216133177324697584914249377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144088784883131723276166251 216133177324697584914249377)
  ·
    refine ⟨162099882993523188685687033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216133177324697584914249377 162099882993523188685687033)
    ·
      refine ⟨121574912245142391514265275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162099882993523188685687033 121574912245142391514265275)
      ·
        refine ⟨182362368367713587271397913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121574912245142391514265275 182362368367713587271397913)
        ·
          refine ⟨136771776275785190453548435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182362368367713587271397913 136771776275785190453548435)
          ·
            refine ⟨205157664413677785680322653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136771776275785190453548435 205157664413677785680322653)
            ·
              refine ⟨76934124155129169630120995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205157664413677785680322653 76934124155129169630120995)
              ·
                refine ⟨115401186232693754445181493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76934124155129169630120995 115401186232693754445181493)
                ·
                  refine ⟨10818861209315039479235765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115401186232693754445181493 10818861209315039479235765)
                  ·
                    refine ⟨1014268238373284951178353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10818861209315039479235765 1014268238373284951178353)
                    ·
                      rfl

theorem cell23_5925841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_5925841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925841 prefixEnd_5925841 := by exact prefixLift 5925841
  have htrace : WordTrace (prefixWord ++ tailWord_5925841) baseStart_5925841 baseEnd_5925841 := by
    simpa [prefixWord, tailWord_5925841, baseEnd_5925841] using wordTrace_append hprefix tailTrace_5925841
  have hstable : (prefixWord ++ tailWord_5925841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925841).length < 2 ^ (prefixWord ++ tailWord_5925841).sum := by decide
  have hdescent : baseEnd_5925841 < baseStart_5925841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925891 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 4]
def baseStart_5925891 : Nat := 118140960795 + 5925891 * 2 ^ 59
def prefixEnd_5925891 : Nat := 4983230072969 + 3 ^ 40 * 5925891 * 2
def baseEnd_5925891 : Nat := 3042830389152579657909829

theorem tailTrace_5925891 : CollatzResearch.WordTrace tailWord_5925891 prefixEnd_5925891 3042830389152579657909829 := by
  unfold tailWord_5925891
  simp only [CollatzResearch.WordTrace]
  refine ⟨216135000974516443453569527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144090000649677628969046351 216135000974516443453569527)
  ·
    refine ⟨324202501461774665180354291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216135000974516443453569527 324202501461774665180354291)
    ·
      refine ⟨486303752192661997770531437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324202501461774665180354291 486303752192661997770531437)
      ·
        refine ⟨182363907072248249163949289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 486303752192661997770531437 182363907072248249163949289)
        ·
          refine ⟨136772930304186186872961967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182363907072248249163949289 136772930304186186872961967)
          ·
            refine ⟨205159395456279280309442951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136772930304186186872961967 205159395456279280309442951)
            ·
              refine ⟨307739093184418920464164427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205159395456279280309442951 307739093184418920464164427)
              ·
                refine ⟨461608639776628380696246641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307739093184418920464164427 461608639776628380696246641)
                ·
                  refine ⟨346206479832471285522184981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461608639776628380696246641 346206479832471285522184981)
                  ·
                    refine ⟨16228428742147091508852421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 346206479832471285522184981 16228428742147091508852421)
                    ·
                      refine ⟨3042830389152579657909829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16228428742147091508852421 3042830389152579657909829)
                      ·
                        rfl

theorem cell23_5925891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_5925891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925891 prefixEnd_5925891 := by exact prefixLift 5925891
  have htrace : WordTrace (prefixWord ++ tailWord_5925891) baseStart_5925891 baseEnd_5925891 := by
    simpa [prefixWord, tailWord_5925891, baseEnd_5925891] using wordTrace_append hprefix tailTrace_5925891
  have hstable : (prefixWord ++ tailWord_5925891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925891).length < 2 ^ (prefixWord ++ tailWord_5925891).sum := by decide
  have hdescent : baseEnd_5925891 < baseStart_5925891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925898 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_5925898 : Nat := 118140960795 + 5925898 * 2 ^ 59
def prefixEnd_5925898 : Nat := 4983230072969 + 3 ^ 40 * 5925898 * 2
def baseEnd_5925898 : Nat := 3042833983517161130522297

theorem tailTrace_5925898 : CollatzResearch.WordTrace tailWord_5925898 prefixEnd_5925898 3042833983517161130522297 := by
  unfold tailWord_5925898
  simp only [CollatzResearch.WordTrace]
  refine ⟨54033814071372770912268587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144090170856994055766049565 54033814071372770912268587)
  ·
    refine ⟨81050721107059156368402881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54033814071372770912268587 81050721107059156368402881)
    ·
      refine ⟨60788040830294367276302161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81050721107059156368402881 60788040830294367276302161)
      ·
        refine ⟨45591030622720775457226621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60788040830294367276302161 45591030622720775457226621)
        ·
          refine ⟨17096636483520290796459983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45591030622720775457226621 17096636483520290796459983)
          ·
            refine ⟨25644954725280436194689975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17096636483520290796459983 25644954725280436194689975)
            ·
              refine ⟨38467432087920654292034963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25644954725280436194689975 38467432087920654292034963)
              ·
                refine ⟨57701148131880981438052445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38467432087920654292034963 57701148131880981438052445)
                ·
                  refine ⟨21637930549455368039269667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57701148131880981438052445 21637930549455368039269667)
                  ·
                    refine ⟨32456895824183052058904501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21637930549455368039269667 32456895824183052058904501)
                    ·
                      refine ⟨3042833983517161130522297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32456895824183052058904501 3042833983517161130522297)
                      ·
                        rfl

theorem cell23_5925898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_5925898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925898 prefixEnd_5925898 := by exact prefixLift 5925898
  have htrace : WordTrace (prefixWord ++ tailWord_5925898) baseStart_5925898 baseEnd_5925898 := by
    simpa [prefixWord, tailWord_5925898, baseEnd_5925898] using wordTrace_append hprefix tailTrace_5925898
  have hstable : (prefixWord ++ tailWord_5925898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925898).length < 2 ^ (prefixWord ++ tailWord_5925898).sum := by decide
  have hdescent : baseEnd_5925898 < baseStart_5925898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925912 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 3, 2, 2]
def baseStart_5925912 : Nat := 118140960795 + 5925912 * 2 ^ 59
def prefixEnd_5925912 : Nat := 4983230072969 + 3 ^ 40 * 5925912 * 2
def baseEnd_5925912 : Nat := 3042841172246324075747233

theorem tailTrace_5925912 : CollatzResearch.WordTrace tailWord_5925912 prefixEnd_5925912 3042841172246324075747233 := by
  unfold tailWord_5925912
  simp only [CollatzResearch.WordTrace]
  refine ⟨108067883453720182020041995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144090511271626909360055993 108067883453720182020041995)
  ·
    refine ⟨162101825180580273030062993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108067883453720182020041995 162101825180580273030062993)
    ·
      refine ⟨121576368885435204772547245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162101825180580273030062993 121576368885435204772547245)
      ·
        refine ⟨45591138332038201789705217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121576368885435204772547245 45591138332038201789705217)
        ·
          refine ⟨34193353749028651342278913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45591138332038201789705217 34193353749028651342278913)
          ·
            refine ⟨25645015311771488506709185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34193353749028651342278913 25645015311771488506709185)
            ·
              refine ⟨19233761483828616380031889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25645015311771488506709185 19233761483828616380031889)
              ·
                refine ⟨14425321112871462285023917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19233761483828616380031889 14425321112871462285023917)
                ·
                  refine ⟨5409495417326798356883969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14425321112871462285023917 5409495417326798356883969)
                  ·
                    refine ⟨4057121562995098767662977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5409495417326798356883969 4057121562995098767662977)
                    ·
                      refine ⟨3042841172246324075747233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057121562995098767662977 3042841172246324075747233)
                      ·
                        rfl

theorem cell23_5925912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_5925912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925912 prefixEnd_5925912 := by exact prefixLift 5925912
  have htrace : WordTrace (prefixWord ++ tailWord_5925912) baseStart_5925912 baseEnd_5925912 := by
    simpa [prefixWord, tailWord_5925912, baseEnd_5925912] using wordTrace_append hprefix tailTrace_5925912
  have hstable : (prefixWord ++ tailWord_5925912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925912).length < 2 ^ (prefixWord ++ tailWord_5925912).sum := by decide
  have hdescent : baseEnd_5925912 < baseStart_5925912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925955 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 3, 3, 2]
def baseStart_5925955 : Nat := 118140960795 + 5925955 * 2 ^ 59
def prefixEnd_5925955 : Nat := 4983230072969 + 3 ^ 40 * 5925955 * 2
def baseEnd_5925955 : Nat := 3042863251914467407509535

theorem tailTrace_5925955 : CollatzResearch.WordTrace tailWord_5925955 prefixEnd_5925955 3042863251914467407509535 := by
  unfold tailWord_5925955
  simp only [CollatzResearch.WordTrace]
  refine ⟨216137335246284582383899319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144091556830856388255932879 216137335246284582383899319)
  ·
    refine ⟨324206002869426873575848979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216137335246284582383899319 324206002869426873575848979)
    ·
      refine ⟨486309004304140310363773469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324206002869426873575848979 486309004304140310363773469)
      ·
        refine ⟨182365876614052616386415051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 486309004304140310363773469 182365876614052616386415051)
        ·
          refine ⟨273548814921078924579622577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182365876614052616386415051 273548814921078924579622577)
          ·
            refine ⟨205161611190809193434716933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273548814921078924579622577 205161611190809193434716933)
            ·
              refine ⟨38467802098276723769009425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205161611190809193434716933 38467802098276723769009425)
              ·
                refine ⟨28850851573707542826757069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38467802098276723769009425 28850851573707542826757069)
                ·
                  refine ⟨10819069340140328560033901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28850851573707542826757069 10819069340140328560033901)
                  ·
                    refine ⟨4057151002552623210012713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10819069340140328560033901 4057151002552623210012713)
                    ·
                      refine ⟨3042863251914467407509535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057151002552623210012713 3042863251914467407509535)
                      ·
                        rfl

theorem cell23_5925955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 3, 2].length) (baseStart_5925955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925955 prefixEnd_5925955 := by exact prefixLift 5925955
  have htrace : WordTrace (prefixWord ++ tailWord_5925955) baseStart_5925955 baseEnd_5925955 := by
    simpa [prefixWord, tailWord_5925955, baseEnd_5925955] using wordTrace_append hprefix tailTrace_5925955
  have hstable : (prefixWord ++ tailWord_5925955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925955).length < 2 ^ (prefixWord ++ tailWord_5925955).sum := by decide
  have hdescent : baseEnd_5925955 < baseStart_5925955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925985 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 3, 4, 2]
def baseStart_5925985 : Nat := 118140960795 + 5925985 * 2 ^ 59
def prefixEnd_5925985 : Nat := 4983230072969 + 3 ^ 40 * 5925985 * 2
def baseEnd_5925985 : Nat := 3042878656334102290134397

theorem tailTrace_5925985 : CollatzResearch.WordTrace tailWord_5925985 prefixEnd_5925985 3042878656334102290134397 := by
  unfold tailWord_5925985
  simp only [CollatzResearch.WordTrace]
  refine ⟨216138429436175897507491409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144092286290783931671660939 216138429436175897507491409)
  ·
    refine ⟨162103822077131923130618557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216138429436175897507491409 162103822077131923130618557)
    ·
      refine ⟨60788933278924471173981959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162103822077131923130618557 60788933278924471173981959)
      ·
        refine ⟨91183399918386706760972939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60788933278924471173981959 91183399918386706760972939)
        ·
          refine ⟨136775099877580060141459409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91183399918386706760972939 136775099877580060141459409)
          ·
            refine ⟨102581324908185045106094557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136775099877580060141459409 102581324908185045106094557)
            ·
              refine ⟨38467996840569391914785459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102581324908185045106094557 38467996840569391914785459)
              ·
                refine ⟨57701995260854087872178189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38467996840569391914785459 57701995260854087872178189)
                ·
                  refine ⟨21638248222820282952066821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57701995260854087872178189 21638248222820282952066821)
                  ·
                    refine ⟨4057171541778803053512529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21638248222820282952066821 4057171541778803053512529)
                    ·
                      refine ⟨3042878656334102290134397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057171541778803053512529 3042878656334102290134397)
                      ·
                        rfl

theorem cell23_5925985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_5925985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925985 prefixEnd_5925985 := by exact prefixLift 5925985
  have htrace : WordTrace (prefixWord ++ tailWord_5925985) baseStart_5925985 baseEnd_5925985 := by
    simpa [prefixWord, tailWord_5925985, baseEnd_5925985] using wordTrace_append hprefix tailTrace_5925985
  have hstable : (prefixWord ++ tailWord_5925985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925985).length < 2 ^ (prefixWord ++ tailWord_5925985).sum := by decide
  have hdescent : baseEnd_5925985 < baseStart_5925985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5925989 : List Nat := [1, 3, 1, 3, 2, 1, 5, 1, 1, 3, 2]
def baseStart_5925989 : Nat := 118140960795 + 5925989 * 2 ^ 59
def prefixEnd_5925989 : Nat := 4983230072969 + 3 ^ 40 * 5925989 * 2
def baseEnd_5925989 : Nat := 3042880710256720274484379

theorem tailTrace_5925989 : CollatzResearch.WordTrace tailWord_5925989 prefixEnd_5925989 3042880710256720274484379 := by
  unfold tailWord_5925989
  simp only [CollatzResearch.WordTrace]
  refine ⟨216138575328161406190637021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144092383552107604127091347 216138575328161406190637021)
  ·
    refine ⟨81051965748060527321488883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216138575328161406190637021 81051965748060527321488883)
    ·
      refine ⟨121577948622090790982233325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81051965748060527321488883 121577948622090790982233325)
      ·
        refine ⟨45591730733284046618337497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121577948622090790982233325 45591730733284046618337497)
        ·
          refine ⟨34193798049963034963753123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45591730733284046618337497 34193798049963034963753123)
          ·
            refine ⟨51290697074944552445629685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34193798049963034963753123 51290697074944552445629685)
            ·
              refine ⟨4808502850776051791777783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51290697074944552445629685 4808502850776051791777783)
              ·
                refine ⟨7212754276164077687666675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4808502850776051791777783 7212754276164077687666675)
                ·
                  refine ⟨10819131414246116531500013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7212754276164077687666675 10819131414246116531500013)
                  ·
                    refine ⟨4057174280342293699312505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10819131414246116531500013 4057174280342293699312505)
                    ·
                      refine ⟨3042880710256720274484379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057174280342293699312505 3042880710256720274484379)
                      ·
                        rfl

theorem cell23_5925989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_5925989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5925989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5925989 prefixEnd_5925989 := by exact prefixLift 5925989
  have htrace : WordTrace (prefixWord ++ tailWord_5925989) baseStart_5925989 baseEnd_5925989 := by
    simpa [prefixWord, tailWord_5925989, baseEnd_5925989] using wordTrace_append hprefix tailTrace_5925989
  have hstable : (prefixWord ++ tailWord_5925989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5925989).length < 2 ^ (prefixWord ++ tailWord_5925989).sum := by decide
  have hdescent : baseEnd_5925989 < baseStart_5925989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5925989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926042 : List Nat := [3, 1, 1, 5, 1, 1, 1, 5, 5]
def baseStart_5926042 : Nat := 118140960795 + 5926042 * 2 ^ 59
def prefixEnd_5926042 : Nat := 4983230072969 + 3 ^ 40 * 5926042 * 2
def baseEnd_5926042 : Nat := 338100880525712063013515

theorem tailTrace_5926042 : CollatzResearch.WordTrace tailWord_5926042 prefixEnd_5926042 338100880525712063013515 := by
  unfold tailWord_5926042
  simp only [CollatzResearch.WordTrace]
  refine ⟨54035127099242349060579095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144093672264646264161544253 54035127099242349060579095)
  ·
    refine ⟨81052690648863523590868643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54035127099242349060579095 81052690648863523590868643)
    ·
      refine ⟨121579035973295285386302965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81052690648863523590868643 121579035973295285386302965)
      ·
        refine ⟨11398034622496433004965903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121579035973295285386302965 11398034622496433004965903)
        ·
          refine ⟨17097051933744649507448855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11398034622496433004965903 17097051933744649507448855)
          ·
            refine ⟨25645577900616974261173283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17097051933744649507448855 25645577900616974261173283)
            ·
              refine ⟨38468366850925461391759925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25645577900616974261173283 38468366850925461391759925)
              ·
                refine ⟨3606409392274262005477493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38468366850925461391759925 3606409392274262005477493)
                ·
                  refine ⟨338100880525712063013515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3606409392274262005477493 338100880525712063013515)
                  ·
                    rfl

theorem cell23_5926042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 5].length) (baseStart_5926042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926042 prefixEnd_5926042 := by exact prefixLift 5926042
  have htrace : WordTrace (prefixWord ++ tailWord_5926042) baseStart_5926042 baseEnd_5926042 := by
    simpa [prefixWord, tailWord_5926042, baseEnd_5926042] using wordTrace_append hprefix tailTrace_5926042
  have hstable : (prefixWord ++ tailWord_5926042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926042).length < 2 ^ (prefixWord ++ tailWord_5926042).sum := by decide
  have hdescent : baseEnd_5926042 < baseStart_5926042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926070 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_5926070 : Nat := 118140960795 + 5926070 * 2 ^ 59
def prefixEnd_5926070 : Nat := 4983230072969 + 3 ^ 40 * 5926070 * 2
def baseEnd_5926070 : Nat := 3042922302189734457571507

theorem tailTrace_5926070 : CollatzResearch.WordTrace tailWord_5926070 prefixEnd_5926070 3042922302189734457571507 := by
  unfold tailWord_5926070
  simp only [CollatzResearch.WordTrace]
  refine ⟨13508845602554247314020979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144094353093911971349557109 13508845602554247314020979)
  ·
    refine ⟨20263268403831370971031469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13508845602554247314020979 20263268403831370971031469)
    ·
      refine ⟨7598725651436764114136801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20263268403831370971031469 7598725651436764114136801)
      ·
        refine ⟨5699044238577573085602601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7598725651436764114136801 5699044238577573085602601)
        ·
          refine ⟨4274283178933179814201951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5699044238577573085602601 4274283178933179814201951)
          ·
            refine ⟨6411424768399769721302927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4274283178933179814201951 6411424768399769721302927)
            ·
              refine ⟨9617137152599654581954391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6411424768399769721302927 9617137152599654581954391)
              ·
                refine ⟨14425705728899481872931587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9617137152599654581954391 14425705728899481872931587)
                ·
                  refine ⟨21638558593349222809397381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14425705728899481872931587 21638558593349222809397381)
                  ·
                    refine ⟨4057229736252979276762009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21638558593349222809397381 4057229736252979276762009)
                    ·
                      refine ⟨3042922302189734457571507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057229736252979276762009 3042922302189734457571507)
                      ·
                        rfl

theorem cell23_5926070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_5926070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926070 prefixEnd_5926070 := by exact prefixLift 5926070
  have htrace : WordTrace (prefixWord ++ tailWord_5926070) baseStart_5926070 baseEnd_5926070 := by
    simpa [prefixWord, tailWord_5926070, baseEnd_5926070] using wordTrace_append hprefix tailTrace_5926070
  have hstable : (prefixWord ++ tailWord_5926070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926070).length < 2 ^ (prefixWord ++ tailWord_5926070).sum := by decide
  have hdescent : baseEnd_5926070 < baseStart_5926070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926075 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 1, 6, 2]
def baseStart_5926075 : Nat := 118140960795 + 5926075 * 2 ^ 59
def prefixEnd_5926075 : Nat := 4983230072969 + 3 ^ 40 * 5926075 * 2
def baseEnd_5926075 : Nat := 3042924869593006938008983

theorem tailTrace_5926075 : CollatzResearch.WordTrace tailWord_5926075 prefixEnd_5926075 3042924869593006938008983 := by
  unfold tailWord_5926075
  simp only [CollatzResearch.WordTrace]
  refine ⟨216141712005849842878267679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144094474670566561918845119 216141712005849842878267679)
  ·
    refine ⟨324212568008774764317401519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216141712005849842878267679 324212568008774764317401519)
    ·
      refine ⟨486318852013162146476102279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324212568008774764317401519 486318852013162146476102279)
      ·
        refine ⟨729478278019743219714153419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486318852013162146476102279 729478278019743219714153419)
        ·
          refine ⟨1094217417029614829571230129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729478278019743219714153419 1094217417029614829571230129)
          ·
            refine ⟨820663062772211122178422597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1094217417029614829571230129 820663062772211122178422597)
            ·
              refine ⟨153874324269789585408454237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 820663062772211122178422597 153874324269789585408454237)
              ·
                refine ⟨57702871601171094528170339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153874324269789585408454237 57702871601171094528170339)
                ·
                  refine ⟨86554307401756641792255509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57702871601171094528170339 86554307401756641792255509)
                  ·
                    refine ⟨4057233159457342584011977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86554307401756641792255509 4057233159457342584011977)
                    ·
                      refine ⟨3042924869593006938008983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057233159457342584011977 3042924869593006938008983)
                      ·
                        rfl

theorem cell23_5926075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 6, 2].length) (baseStart_5926075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926075 prefixEnd_5926075 := by exact prefixLift 5926075
  have htrace : WordTrace (prefixWord ++ tailWord_5926075) baseStart_5926075 baseEnd_5926075 := by
    simpa [prefixWord, tailWord_5926075, baseEnd_5926075] using wordTrace_append hprefix tailTrace_5926075
  have hstable : (prefixWord ++ tailWord_5926075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926075).length < 2 ^ (prefixWord ++ tailWord_5926075).sum := by decide
  have hdescent : baseEnd_5926075 < baseStart_5926075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926093 : List Nat := [1, 6, 2, 2, 1, 2, 1, 3, 5]
def baseStart_5926093 : Nat := 118140960795 + 5926093 * 2 ^ 59
def prefixEnd_5926093 : Nat := 4983230072969 + 3 ^ 40 * 5926093 * 2
def baseEnd_5926093 : Nat := 338103790249420874175989

theorem tailTrace_5926093 : CollatzResearch.WordTrace tailWord_5926093 prefixEnd_5926093 338103790249420874175989 := by
  unfold tailWord_5926093
  simp only [CollatzResearch.WordTrace]
  refine ⟨216142368519784631952422933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144094912346523087968281955 216142368519784631952422933)
  ·
    refine ⟨10131673524364904622769825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 216142368519784631952422933 10131673524364904622769825)
    ·
      refine ⟨7598755143273678467077369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10131673524364904622769825 7598755143273678467077369)
      ·
        refine ⟨5699066357455258850308027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7598755143273678467077369 5699066357455258850308027)
        ·
          refine ⟨8548599536182888275462041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5699066357455258850308027 8548599536182888275462041)
          ·
            refine ⟨6411449652137166206596531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8548599536182888275462041 6411449652137166206596531)
            ·
              refine ⟨9617174478205749309894797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6411449652137166206596531 9617174478205749309894797)
              ·
                refine ⟨3606440429327155991210549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9617174478205749309894797 3606440429327155991210549)
                ·
                  refine ⟨338103790249420874175989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3606440429327155991210549 338103790249420874175989)
                  ·
                    rfl

theorem cell23_5926093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_5926093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926093 prefixEnd_5926093 := by exact prefixLift 5926093
  have htrace : WordTrace (prefixWord ++ tailWord_5926093) baseStart_5926093 baseEnd_5926093 := by
    simpa [prefixWord, tailWord_5926093, baseEnd_5926093] using wordTrace_append hprefix tailTrace_5926093
  have hstable : (prefixWord ++ tailWord_5926093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926093).length < 2 ^ (prefixWord ++ tailWord_5926093).sum := by decide
  have hdescent : baseEnd_5926093 < baseStart_5926093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926109 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_5926109 : Nat := 118140960795 + 5926109 * 2 ^ 59
def prefixEnd_5926109 : Nat := 4983230072969 + 3 ^ 40 * 5926109 * 2
def baseEnd_5926109 : Nat := 3042942327935259804983827

theorem tailTrace_5926109 : CollatzResearch.WordTrace tailWord_5926109 prefixEnd_5926109 3042942327935259804983827 := by
  unfold tailWord_5926109
  simp only [CollatzResearch.WordTrace]
  refine ⟨216142952087726666685005381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144095301391817777790003587 216142952087726666685005381)
  ·
    refine ⟨40526803516448750003438509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216142952087726666685005381 40526803516448750003438509)
    ·
      refine ⟨15197551318668281251289441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40526803516448750003438509 15197551318668281251289441)
      ·
        refine ⟨11398163489001210938467081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15197551318668281251289441 11398163489001210938467081)
        ·
          refine ⟨8548622616750908203850311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11398163489001210938467081 8548622616750908203850311)
          ·
            refine ⟨12822933925126362305775467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8548622616750908203850311 12822933925126362305775467)
            ·
              refine ⟨19234400887689543458663201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12822933925126362305775467 19234400887689543458663201)
              ·
                refine ⟨14425800665767157593997401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19234400887689543458663201 14425800665767157593997401)
                ·
                  refine ⟨10819350499325368195498051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14425800665767157593997401 10819350499325368195498051)
                  ·
                    refine ⟨16229025748988052293247077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10819350499325368195498051 16229025748988052293247077)
                    ·
                      refine ⟨3042942327935259804983827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16229025748988052293247077 3042942327935259804983827)
                      ·
                        rfl

theorem cell23_5926109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_5926109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926109 prefixEnd_5926109 := by exact prefixLift 5926109
  have htrace : WordTrace (prefixWord ++ tailWord_5926109) baseStart_5926109 baseEnd_5926109 := by
    simpa [prefixWord, tailWord_5926109, baseEnd_5926109] using wordTrace_append hprefix tailTrace_5926109
  have hstable : (prefixWord ++ tailWord_5926109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926109).length < 2 ^ (prefixWord ++ tailWord_5926109).sum := by decide
  have hdescent : baseEnd_5926109 < baseStart_5926109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926112 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 3]
def baseStart_5926112 : Nat := 118140960795 + 5926112 * 2 ^ 59
def prefixEnd_5926112 : Nat := 4983230072969 + 3 ^ 40 * 5926112 * 2
def baseEnd_5926112 : Nat := 3042943868377223293246313

theorem tailTrace_5926112 : CollatzResearch.WordTrace tailWord_5926112 prefixEnd_5926112 3042943868377223293246313 := by
  unfold tailWord_5926112
  simp only [CollatzResearch.WordTrace]
  refine ⟨108071530753357899098682295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144095374337810532131576393 108071530753357899098682295)
  ·
    refine ⟨162107296130036848648023443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108071530753357899098682295 162107296130036848648023443)
    ·
      refine ⟨243160944195055272972035165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162107296130036848648023443 243160944195055272972035165)
      ·
        refine ⟨91185354073145727364513187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243160944195055272972035165 91185354073145727364513187)
        ·
          refine ⟨136778031109718591046769781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91185354073145727364513187 136778031109718591046769781)
          ·
            refine ⟨12822940416536117910634667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136778031109718591046769781 12822940416536117910634667)
            ·
              refine ⟨19234410624804176865952001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12822940416536117910634667 19234410624804176865952001)
              ·
                refine ⟨14425807968603132649464001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19234410624804176865952001 14425807968603132649464001)
                ·
                  refine ⟨10819355976452349487098001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14425807968603132649464001 10819355976452349487098001)
                  ·
                    refine ⟨8114516982339262115323501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10819355976452349487098001 8114516982339262115323501)
                    ·
                      refine ⟨3042943868377223293246313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8114516982339262115323501 3042943868377223293246313)
                      ·
                        rfl

theorem cell23_5926112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_5926112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926112 prefixEnd_5926112 := by exact prefixLift 5926112
  have htrace : WordTrace (prefixWord ++ tailWord_5926112) baseStart_5926112 baseEnd_5926112 := by
    simpa [prefixWord, tailWord_5926112, baseEnd_5926112] using wordTrace_append hprefix tailTrace_5926112
  have hstable : (prefixWord ++ tailWord_5926112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926112).length < 2 ^ (prefixWord ++ tailWord_5926112).sum := by decide
  have hdescent : baseEnd_5926112 < baseStart_5926112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926128 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 1, 11]
def baseStart_5926128 : Nat := 118140960795 + 5926128 * 2 ^ 59
def prefixEnd_5926128 : Nat := 4983230072969 + 3 ^ 40 * 5926128 * 2
def baseEnd_5926128 : Nat := 1014317361355898410215413

theorem tailTrace_5926128 : CollatzResearch.WordTrace tailWord_5926128 prefixEnd_5926128 1014317361355898410215413 := by
  unfold tailWord_5926128
  simp only [CollatzResearch.WordTrace]
  refine ⟨108071822537328916464973519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144095763383105221953298025 108071822537328916464973519)
  ·
    refine ⟨162107733805993374697460279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108071822537328916464973519 162107733805993374697460279)
    ·
      refine ⟨243161600708990062046190419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162107733805993374697460279 243161600708990062046190419)
      ·
        refine ⟨364742401063485093069285629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243161600708990062046190419 364742401063485093069285629)
        ·
          refine ⟨136778400398806909900982111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364742401063485093069285629 136778400398806909900982111)
          ·
            refine ⟨205167600598210364851473167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136778400398806909900982111 205167600598210364851473167)
            ·
              refine ⟨307751400897315547277209751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205167600598210364851473167 307751400897315547277209751)
              ·
                refine ⟨461627101345973320915814627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307751400897315547277209751 461627101345973320915814627)
                ·
                  refine ⟨692440652018959981373721941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461627101345973320915814627 692440652018959981373721941)
                  ·
                    refine ⟨1014317361355898410215413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 692440652018959981373721941 1014317361355898410215413)
                    ·
                      rfl

theorem cell23_5926128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_5926128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926128 prefixEnd_5926128 := by exact prefixLift 5926128
  have htrace : WordTrace (prefixWord ++ tailWord_5926128) baseStart_5926128 baseEnd_5926128 := by
    simpa [prefixWord, tailWord_5926128, baseEnd_5926128] using wordTrace_append hprefix tailTrace_5926128
  have hstable : (prefixWord ++ tailWord_5926128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926128).length < 2 ^ (prefixWord ++ tailWord_5926128).sum := by decide
  have hdescent : baseEnd_5926128 < baseStart_5926128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926146 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_5926146 : Nat := 118140960795 + 5926146 * 2 ^ 59
def prefixEnd_5926146 : Nat := 4983230072969 + 3 ^ 40 * 5926146 * 2
def baseEnd_5926146 : Nat := 3042961326719476160221157

theorem tailTrace_5926146 : CollatzResearch.WordTrace tailWord_5926146 prefixEnd_5926146 3042961326719476160221157 := by
  unfold tailWord_5926146
  simp only [CollatzResearch.WordTrace]
  refine ⟨54036075397148155501025573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144096201059061748002734861 54036075397148155501025573)
  ·
    refine ⟨10131764136965279156442295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54036075397148155501025573 10131764136965279156442295)
    ·
      refine ⟨15197646205447918734663443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10131764136965279156442295 15197646205447918734663443)
      ·
        refine ⟨22796469308171878101995165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15197646205447918734663443 22796469308171878101995165)
        ·
          refine ⟨8548675990564454288248187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22796469308171878101995165 8548675990564454288248187)
          ·
            refine ⟨12823013985846681432372281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8548675990564454288248187 12823013985846681432372281)
            ·
              refine ⟨9617260489385011074279211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12823013985846681432372281 9617260489385011074279211)
              ·
                refine ⟨14425890734077516611418817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9617260489385011074279211 14425890734077516611418817)
                ·
                  refine ⟨10819418050558137458564113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14425890734077516611418817 10819418050558137458564113)
                  ·
                    refine ⟨8114563537918603093923085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10819418050558137458564113 8114563537918603093923085)
                    ·
                      refine ⟨3042961326719476160221157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8114563537918603093923085 3042961326719476160221157)
                      ·
                        rfl

theorem cell23_5926146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_5926146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926146 prefixEnd_5926146 := by exact prefixLift 5926146
  have htrace : WordTrace (prefixWord ++ tailWord_5926146) baseStart_5926146 baseEnd_5926146 := by
    simpa [prefixWord, tailWord_5926146, baseEnd_5926146] using wordTrace_append hprefix tailTrace_5926146
  have hstable : (prefixWord ++ tailWord_5926146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926146).length < 2 ^ (prefixWord ++ tailWord_5926146).sum := by decide
  have hdescent : baseEnd_5926146 < baseStart_5926146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926192 : List Nat := [2, 1, 1, 1, 2, 2, 3, 5, 2, 4]
def baseStart_5926192 : Nat := 118140960795 + 5926192 * 2 ^ 59
def prefixEnd_5926192 : Nat := 4983230072969 + 3 ^ 40 * 5926192 * 2
def baseEnd_5926192 : Nat := 1014328315609860993415315

theorem tailTrace_5926192 : CollatzResearch.WordTrace tailWord_5926192 prefixEnd_5926192 1014328315609860993415315 := by
  unfold tailWord_5926192
  simp only [CollatzResearch.WordTrace]
  refine ⟨108072989673212985930138415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144097319564283981240184553 108072989673212985930138415)
  ·
    refine ⟨162109484509819478895207623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108072989673212985930138415 162109484509819478895207623)
    ·
      refine ⟨243164226764729218342811435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162109484509819478895207623 243164226764729218342811435)
      ·
        refine ⟨364746340147093827514217153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243164226764729218342811435 364746340147093827514217153)
        ·
          refine ⟨273559755110320370635662865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364746340147093827514217153 273559755110320370635662865)
          ·
            refine ⟨205169816332740277976747149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273559755110320370635662865 205169816332740277976747149)
            ·
              refine ⟨76938681124777604241280181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205169816332740277976747149 76938681124777604241280181)
              ·
                refine ⟨7213001355447900397620017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76938681124777604241280181 7213001355447900397620017)
                ·
                  refine ⟨5409751016585925298215013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7213001355447900397620017 5409751016585925298215013)
                  ·
                    refine ⟨1014328315609860993415315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5409751016585925298215013 1014328315609860993415315)
                    ·
                      rfl

theorem cell23_5926192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 2, 4].length) (baseStart_5926192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926192 prefixEnd_5926192 := by exact prefixLift 5926192
  have htrace : WordTrace (prefixWord ++ tailWord_5926192) baseStart_5926192 baseEnd_5926192 := by
    simpa [prefixWord, tailWord_5926192, baseEnd_5926192] using wordTrace_append hprefix tailTrace_5926192
  have hstable : (prefixWord ++ tailWord_5926192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926192).length < 2 ^ (prefixWord ++ tailWord_5926192).sum := by decide
  have hdescent : baseEnd_5926192 < baseStart_5926192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926202 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3]
def baseStart_5926202 : Nat := 118140960795 + 5926202 * 2 ^ 59
def prefixEnd_5926202 : Nat := 4983230072969 + 3 ^ 40 * 5926202 * 2
def baseEnd_5926202 : Nat := 3042990081636127941120899

theorem tailTrace_5926202 : CollatzResearch.WordTrace tailWord_5926202 prefixEnd_5926202 3042990081636127941120899 := by
  unfold tailWord_5926202
  simp only [CollatzResearch.WordTrace]
  refine ⟨54036586019097435892035215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144097562717593162378760573 54036586019097435892035215)
  ·
    refine ⟨81054879028646153838052823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54036586019097435892035215 81054879028646153838052823)
    ·
      refine ⟨121582318542969230757079235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81054879028646153838052823 121582318542969230757079235)
      ·
        refine ⟨182373477814453846135618853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121582318542969230757079235 182373477814453846135618853)
        ·
          refine ⟨34195027090210096150428535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182373477814453846135618853 34195027090210096150428535)
          ·
            refine ⟨51292540635315144225642803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34195027090210096150428535 51292540635315144225642803)
            ·
              refine ⟨76938810952972716338464205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51292540635315144225642803 76938810952972716338464205)
              ·
                refine ⟨28852054107364768626924077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76938810952972716338464205 28852054107364768626924077)
                ·
                  refine ⟨10819520290261788235096529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28852054107364768626924077 10819520290261788235096529)
                  ·
                    refine ⟨8114640217696341176322397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10819520290261788235096529 8114640217696341176322397)
                    ·
                      refine ⟨3042990081636127941120899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8114640217696341176322397 3042990081636127941120899)
                      ·
                        rfl

theorem cell23_5926202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_5926202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926202 prefixEnd_5926202 := by exact prefixLift 5926202
  have htrace : WordTrace (prefixWord ++ tailWord_5926202) baseStart_5926202 baseEnd_5926202 := by
    simpa [prefixWord, tailWord_5926202, baseEnd_5926202] using wordTrace_append hprefix tailTrace_5926202
  have hstable : (prefixWord ++ tailWord_5926202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926202).length < 2 ^ (prefixWord ++ tailWord_5926202).sum := by decide
  have hdescent : baseEnd_5926202 < baseStart_5926202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926265 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 1, 8]
def baseStart_5926265 : Nat := 118140960795 + 5926265 * 2 ^ 59
def prefixEnd_5926265 : Nat := 4983230072969 + 3 ^ 40 * 5926265 * 2
def baseEnd_5926265 : Nat := 1014340810305787064877703

theorem tailTrace_5926265 : CollatzResearch.WordTrace tailWord_5926265 prefixEnd_5926265 1014340810305787064877703 := by
  unfold tailWord_5926265
  simp only [CollatzResearch.WordTrace]
  refine ⟨216148641875161505327684249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144099094583441003551789499 216148641875161505327684249)
  ·
    refine ⟨162111481406371128995763187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216148641875161505327684249 162111481406371128995763187)
    ·
      refine ⟨243167222109556693493644781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162111481406371128995763187 243167222109556693493644781)
      ·
        refine ⟨91187708291083760060116793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243167222109556693493644781 91187708291083760060116793)
        ·
          refine ⟨68390781218312820045087595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91187708291083760060116793 68390781218312820045087595)
          ·
            refine ⟨102586171827469230067631393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68390781218312820045087595 102586171827469230067631393)
            ·
              refine ⟨76939628870601922550723545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102586171827469230067631393 76939628870601922550723545)
              ·
                refine ⟨57704721652951441913042659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76939628870601922550723545 57704721652951441913042659)
                ·
                  refine ⟨86557082479427162869563989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57704721652951441913042659 86557082479427162869563989)
                  ·
                    refine ⟨1014340810305787064877703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86557082479427162869563989 1014340810305787064877703)
                    ·
                      rfl

theorem cell23_5926265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_5926265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926265 prefixEnd_5926265 := by exact prefixLift 5926265
  have htrace : WordTrace (prefixWord ++ tailWord_5926265) baseStart_5926265 baseEnd_5926265 := by
    simpa [prefixWord, tailWord_5926265, baseEnd_5926265] using wordTrace_append hprefix tailTrace_5926265
  have hstable : (prefixWord ++ tailWord_5926265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926265).length < 2 ^ (prefixWord ++ tailWord_5926265).sum := by decide
  have hdescent : baseEnd_5926265 < baseStart_5926265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926276 : List Nat := [2, 3, 2, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_5926276 : Nat := 118140960795 + 5926276 * 2 ^ 59
def prefixEnd_5926276 : Nat := 4983230072969 + 3 ^ 40 * 5926276 * 2
def baseEnd_5926276 : Nat := 3043028079204560651595559

theorem tailTrace_5926276 : CollatzResearch.WordTrace tailWord_5926276 prefixEnd_5926276 3043028079204560651595559 := by
  unfold tailWord_5926276
  simp only [CollatzResearch.WordTrace]
  refine ⟨108074521539060827103167341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144099362052081102804223121 108074521539060827103167341)
  ·
    refine ⟨40527945577147810163687753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108074521539060827103167341 40527945577147810163687753)
    ·
      refine ⟨30395959182860857622765815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40527945577147810163687753 30395959182860857622765815)
      ·
        refine ⟨45593938774291286434148723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30395959182860857622765815 45593938774291286434148723)
        ·
          refine ⟨68390908161436929651223085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45593938774291286434148723 68390908161436929651223085)
          ·
            refine ⟨25646590560538848619208657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68390908161436929651223085 25646590560538848619208657)
            ·
              refine ⟨19234942920404136464406493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25646590560538848619208657 19234942920404136464406493)
              ·
                refine ⟨7213103595151551174152435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19234942920404136464406493 7213103595151551174152435)
                ·
                  refine ⟨10819655392727326761228653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7213103595151551174152435 10819655392727326761228653)
                  ·
                    refine ⟨4057370772272747535460745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10819655392727326761228653 4057370772272747535460745)
                    ·
                      refine ⟨3043028079204560651595559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057370772272747535460745 3043028079204560651595559)
                      ·
                        rfl

theorem cell23_5926276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_5926276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926276 prefixEnd_5926276 := by exact prefixLift 5926276
  have htrace : WordTrace (prefixWord ++ tailWord_5926276) baseStart_5926276 baseEnd_5926276 := by
    simpa [prefixWord, tailWord_5926276, baseEnd_5926276] using wordTrace_append hprefix tailTrace_5926276
  have hstable : (prefixWord ++ tailWord_5926276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926276).length < 2 ^ (prefixWord ++ tailWord_5926276).sum := by decide
  have hdescent : baseEnd_5926276 < baseStart_5926276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926322 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_5926322 : Nat := 118140960795 + 5926322 * 2 ^ 59
def prefixEnd_5926322 : Nat := 4983230072969 + 3 ^ 40 * 5926322 * 2
def baseEnd_5926322 : Nat := 3043051699314667471620347

theorem tailTrace_5926322 : CollatzResearch.WordTrace tailWord_5926322 prefixEnd_5926322 3043051699314667471620347 := by
  unfold tailWord_5926322
  simp only [CollatzResearch.WordTrace]
  refine ⟨54037680208988751015627305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144100480557303336041672813 54037680208988751015627305)
  ·
    refine ⟨40528260156741563261720479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54037680208988751015627305 40528260156741563261720479)
    ·
      refine ⟨60792390235112344892580719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40528260156741563261720479 60792390235112344892580719)
      ·
        refine ⟨91188585352668517338871079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60792390235112344892580719 91188585352668517338871079)
        ·
          refine ⟨136782878029002776008306619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91188585352668517338871079 136782878029002776008306619)
          ·
            refine ⟨205174317043504164012459929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136782878029002776008306619 205174317043504164012459929)
            ·
              refine ⟨153880737782628123009344947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205174317043504164012459929 153880737782628123009344947)
              ·
                refine ⟨230821106673942184514017421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153880737782628123009344947 230821106673942184514017421)
                ·
                  refine ⟨86557915002728319192756533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230821106673942184514017421 86557915002728319192756533)
                  ·
                    refine ⟨8114804531505779924320925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86557915002728319192756533 8114804531505779924320925)
                    ·
                      refine ⟨3043051699314667471620347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8114804531505779924320925 3043051699314667471620347)
                      ·
                        rfl

theorem cell23_5926322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_5926322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926322 prefixEnd_5926322 := by exact prefixLift 5926322
  have htrace : WordTrace (prefixWord ++ tailWord_5926322) baseStart_5926322 baseEnd_5926322 := by
    simpa [prefixWord, tailWord_5926322, baseEnd_5926322] using wordTrace_append hprefix tailTrace_5926322
  have hstable : (prefixWord ++ tailWord_5926322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926322).length < 2 ^ (prefixWord ++ tailWord_5926322).sum := by decide
  have hdescent : baseEnd_5926322 < baseStart_5926322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926340 : List Nat := [2, 3, 3, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_5926340 : Nat := 118140960795 + 5926340 * 2 ^ 59
def prefixEnd_5926340 : Nat := 4983230072969 + 3 ^ 40 * 5926340 * 2
def baseEnd_5926340 : Nat := 3043060941966448401195265

theorem tailTrace_5926340 : CollatzResearch.WordTrace tailWord_5926340 prefixEnd_5926340 3043060941966448401195265 := by
  unfold tailWord_5926340
  simp only [CollatzResearch.WordTrace]
  refine ⟨108075688674944896568332237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144100918233259862091109649 108075688674944896568332237)
  ·
    refine ⟨40528383253104336213124589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108075688674944896568332237 40528383253104336213124589)
    ·
      refine ⟨15198143719914126079921721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40528383253104336213124589 15198143719914126079921721)
      ·
        refine ⟨11398607789935594559941291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15198143719914126079921721 11398607789935594559941291)
        ·
          refine ⟨17097911684903391839911937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11398607789935594559941291 17097911684903391839911937)
          ·
            refine ⟨12823433763677543879933953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17097911684903391839911937 12823433763677543879933953)
            ·
              refine ⟨9617575322758157909950465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12823433763677543879933953 9617575322758157909950465)
              ·
                refine ⟨7213181492068618432462849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9617575322758157909950465 7213181492068618432462849)
                ·
                  refine ⟨5409886119051463824347137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7213181492068618432462849 5409886119051463824347137)
                  ·
                    refine ⟨4057414589288597868260353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5409886119051463824347137 4057414589288597868260353)
                    ·
                      refine ⟨3043060941966448401195265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057414589288597868260353 3043060941966448401195265)
                      ·
                        rfl

theorem cell23_5926340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_5926340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926340 prefixEnd_5926340 := by exact prefixLift 5926340
  have htrace : WordTrace (prefixWord ++ tailWord_5926340) baseStart_5926340 baseEnd_5926340 := by
    simpa [prefixWord, tailWord_5926340, baseEnd_5926340] using wordTrace_append hprefix tailTrace_5926340
  have hstable : (prefixWord ++ tailWord_5926340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926340).length < 2 ^ (prefixWord ++ tailWord_5926340).sum := by decide
  have hdescent : baseEnd_5926340 < baseStart_5926340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926346 : List Nat := [3, 1, 2, 1, 2, 3, 4, 2, 5]
def baseStart_5926346 : Nat := 118140960795 + 5926346 * 2 ^ 59
def prefixEnd_5926346 : Nat := 4983230072969 + 3 ^ 40 * 5926346 * 2
def baseEnd_5926346 : Nat := 338118224761152819746693

theorem tailTrace_5926346 : CollatzResearch.WordTrace tailWord_5926346 prefixEnd_5926346 338118224761152819746693 := by
  unfold tailWord_5926346
  simp only [CollatzResearch.WordTrace]
  refine ⟨54037899046967014040345723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144101064125245370774255261 54037899046967014040345723)
  ·
    refine ⟨81056848570450521060518585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54037899046967014040345723 81056848570450521060518585)
    ·
      refine ⟨60792636427837890795388939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81056848570450521060518585 60792636427837890795388939)
      ·
        refine ⟨91188954641756836193083409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60792636427837890795388939 91188954641756836193083409)
        ·
          refine ⟨68391715981317627144812557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91188954641756836193083409 68391715981317627144812557)
          ·
            refine ⟨25646893492994110179304709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68391715981317627144812557 25646893492994110179304709)
            ·
              refine ⟨4808792529936395658619633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25646893492994110179304709 4808792529936395658619633)
              ·
                refine ⟨3606594397452296743964725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4808792529936395658619633 3606594397452296743964725)
                ·
                  refine ⟨338118224761152819746693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3606594397452296743964725 338118224761152819746693)
                  ·
                    rfl

theorem cell23_5926346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 5].length) (baseStart_5926346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926346 prefixEnd_5926346 := by exact prefixLift 5926346
  have htrace : WordTrace (prefixWord ++ tailWord_5926346) baseStart_5926346 baseEnd_5926346 := by
    simpa [prefixWord, tailWord_5926346, baseEnd_5926346] using wordTrace_append hprefix tailTrace_5926346
  have hstable : (prefixWord ++ tailWord_5926346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926346).length < 2 ^ (prefixWord ++ tailWord_5926346).sum := by decide
  have hdescent : baseEnd_5926346 < baseStart_5926346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926356 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_5926356 : Nat := 118140960795 + 5926356 * 2 ^ 59
def prefixEnd_5926356 : Nat := 4983230072969 + 3 ^ 40 * 5926356 * 2
def baseEnd_5926356 : Nat := 3043069157656920338595191

theorem tailTrace_5926356 : CollatzResearch.WordTrace tailWord_5926356 prefixEnd_5926356 3043069157656920338595191 := by
  unfold tailWord_5926356
  simp only [CollatzResearch.WordTrace]
  refine ⟨108075980458915913934623461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144101307278554551912831281 108075980458915913934623461)
  ·
    refine ⟨20264246336046733862741899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108075980458915913934623461 20264246336046733862741899)
    ·
      refine ⟨30396369504070100794112849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20264246336046733862741899 30396369504070100794112849)
      ·
        refine ⟨22797277128052575595584637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30396369504070100794112849 22797277128052575595584637)
        ·
          refine ⟨8548978923019715848344239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22797277128052575595584637 8548978923019715848344239)
          ·
            refine ⟨12823468384529573772516359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8548978923019715848344239 12823468384529573772516359)
            ·
              refine ⟨19235202576794360658774539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12823468384529573772516359 19235202576794360658774539)
              ·
                refine ⟨28852803865191540988161809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19235202576794360658774539 28852803865191540988161809)
                ·
                  refine ⟨21639602898893655741121357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28852803865191540988161809 21639602898893655741121357)
                  ·
                    refine ⟨8114851087085120902920509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21639602898893655741121357 8114851087085120902920509)
                    ·
                      refine ⟨3043069157656920338595191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8114851087085120902920509 3043069157656920338595191)
                      ·
                        rfl

theorem cell23_5926356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_5926356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926356 prefixEnd_5926356 := by exact prefixLift 5926356
  have htrace : WordTrace (prefixWord ++ tailWord_5926356) baseStart_5926356 baseEnd_5926356 := by
    simpa [prefixWord, tailWord_5926356, baseEnd_5926356] using wordTrace_append hprefix tailTrace_5926356
  have hstable : (prefixWord ++ tailWord_5926356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926356).length < 2 ^ (prefixWord ++ tailWord_5926356).sum := by decide
  have hdescent : baseEnd_5926356 < baseStart_5926356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926392 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_5926392 : Nat := 118140960795 + 5926392 * 2 ^ 59
def prefixEnd_5926392 : Nat := 4983230072969 + 3 ^ 40 * 5926392 * 2
def baseEnd_5926392 : Nat := 3043087642960482197745025

theorem tailTrace_5926392 : CollatzResearch.WordTrace tailWord_5926392 prefixEnd_5926392 3043087642960482197745025 := by
  unfold tailWord_5926392
  simp only [CollatzResearch.WordTrace]
  refine ⟨108076636972850703008778715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144102182630467604011704953 108076636972850703008778715)
  ·
    refine ⟨162114955459276054513168073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108076636972850703008778715 162114955459276054513168073)
    ·
      refine ⟨121586216594457040884876055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162114955459276054513168073 121586216594457040884876055)
      ·
        refine ⟨182379324891685561327314083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121586216594457040884876055 182379324891685561327314083)
        ·
          refine ⟨273568987337528341990971125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182379324891685561327314083 273568987337528341990971125)
          ·
            refine ⟨25647092562893282061653543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 273568987337528341990971125 25647092562893282061653543)
            ·
              refine ⟨38470638844339923092480315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25647092562893282061653543 38470638844339923092480315)
              ·
                refine ⟨57705958266509884638720473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38470638844339923092480315 57705958266509884638720473)
                ·
                  refine ⟨43279468699882413479040355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57705958266509884638720473 43279468699882413479040355)
                  ·
                    refine ⟨64919203049823620218560533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43279468699882413479040355 64919203049823620218560533)
                    ·
                      refine ⟨3043087642960482197745025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64919203049823620218560533 3043087642960482197745025)
                      ·
                        rfl

theorem cell23_5926392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_5926392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926392 prefixEnd_5926392 := by exact prefixLift 5926392
  have htrace : WordTrace (prefixWord ++ tailWord_5926392) baseStart_5926392 baseEnd_5926392 := by
    simpa [prefixWord, tailWord_5926392, baseEnd_5926392] using wordTrace_append hprefix tailTrace_5926392
  have hstable : (prefixWord ++ tailWord_5926392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926392).length < 2 ^ (prefixWord ++ tailWord_5926392).sum := by decide
  have hdescent : baseEnd_5926392 < baseStart_5926392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926429 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_5926429 : Nat := 118140960795 + 5926429 * 2 ^ 59
def prefixEnd_5926429 : Nat := 4983230072969 + 3 ^ 40 * 5926429 * 2
def baseEnd_5926429 : Nat := 3043106641744698552982355

theorem tailTrace_5926429 : CollatzResearch.WordTrace tailWord_5926429 prefixEnd_5926429 3043106641744698552982355 := by
  unfold tailWord_5926429
  simp only [CollatzResearch.WordTrace]
  refine ⟨216154623446567361336654341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144103082297711574224436227 216154623446567361336654341)
  ·
    refine ⟨40528991896231380250622689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216154623446567361336654341 40528991896231380250622689)
    ·
      refine ⟨30396743922173535187967017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40528991896231380250622689 30396743922173535187967017)
      ·
        refine ⟨22797557941630151390975263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30396743922173535187967017 22797557941630151390975263)
        ·
          refine ⟨34196336912445227086462895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22797557941630151390975263 34196336912445227086462895)
          ·
            refine ⟨51294505368667840629694343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34196336912445227086462895 51294505368667840629694343)
            ·
              refine ⟨76941758053001760944541515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51294505368667840629694343 76941758053001760944541515)
              ·
                refine ⟨115412637079502641416812273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76941758053001760944541515 115412637079502641416812273)
                ·
                  refine ⟨86559477809626981062609205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115412637079502641416812273 86559477809626981062609205)
                  ·
                    refine ⟨8114951044652529474619613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86559477809626981062609205 8114951044652529474619613)
                    ·
                      refine ⟨3043106641744698552982355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8114951044652529474619613 3043106641744698552982355)
                      ·
                        rfl

theorem cell23_5926429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_5926429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926429 prefixEnd_5926429 := by exact prefixLift 5926429
  have htrace : WordTrace (prefixWord ++ tailWord_5926429) baseStart_5926429 baseEnd_5926429 := by
    simpa [prefixWord, tailWord_5926429, baseEnd_5926429] using wordTrace_append hprefix tailTrace_5926429
  have hstable : (prefixWord ++ tailWord_5926429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926429).length < 2 ^ (prefixWord ++ tailWord_5926429).sum := by decide
  have hdescent : baseEnd_5926429 < baseStart_5926429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926456 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 4, 3, 2]
def baseStart_5926456 : Nat := 118140960795 + 5926456 * 2 ^ 59
def prefixEnd_5926456 : Nat := 4983230072969 + 3 ^ 40 * 5926456 * 2
def baseEnd_5926456 : Nat := 3043120505722369947344731

theorem tailTrace_5926456 : CollatzResearch.WordTrace tailWord_5926456 prefixEnd_5926456 3043120505722369947344731 := by
  unfold tailWord_5926456
  simp only [CollatzResearch.WordTrace]
  refine ⟨108077804108734772473943611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144103738811646363298591481 108077804108734772473943611)
  ·
    refine ⟨162116706163102158710915417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108077804108734772473943611 162116706163102158710915417)
    ·
      refine ⟨121587529622326619033186563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162116706163102158710915417 121587529622326619033186563)
      ·
        refine ⟨182381294433489928549779845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121587529622326619033186563 182381294433489928549779845)
        ·
          refine ⟨34196492706279361603083721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182381294433489928549779845 34196492706279361603083721)
          ·
            refine ⟨25647369529709521202312791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34196492706279361603083721 25647369529709521202312791)
            ·
              refine ⟨38471054294564281803469187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25647369529709521202312791 38471054294564281803469187)
              ·
                refine ⟨57706581441846422705203781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38471054294564281803469187 57706581441846422705203781)
                ·
                  refine ⟨10819984020346204257225709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57706581441846422705203781 10819984020346204257225709)
                  ·
                    refine ⟨4057494007629826596459641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10819984020346204257225709 4057494007629826596459641)
                    ·
                      refine ⟨3043120505722369947344731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057494007629826596459641 3043120505722369947344731)
                      ·
                        rfl

theorem cell23_5926456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4, 3, 2].length) (baseStart_5926456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926456 prefixEnd_5926456 := by exact prefixLift 5926456
  have htrace : WordTrace (prefixWord ++ tailWord_5926456) baseStart_5926456 baseEnd_5926456 := by
    simpa [prefixWord, tailWord_5926456, baseEnd_5926456] using wordTrace_append hprefix tailTrace_5926456
  have hstable : (prefixWord ++ tailWord_5926456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926456).length < 2 ^ (prefixWord ++ tailWord_5926456).sum := by decide
  have hdescent : baseEnd_5926456 < baseStart_5926456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926463 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 3, 1, 3]
def baseStart_5926463 : Nat := 118140960795 + 5926463 * 2 ^ 59
def prefixEnd_5926463 : Nat := 4983230072969 + 3 ^ 40 * 5926463 * 2
def baseEnd_5926463 : Nat := 3043124100086951419957199

theorem tailTrace_5926463 : CollatzResearch.WordTrace tailWord_5926463 prefixEnd_5926463 3043124100086951419957199 := by
  unfold tailWord_5926463
  simp only [CollatzResearch.WordTrace]
  refine ⟨216155863528444185143392043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144103909018962790095594695 216155863528444185143392043)
  ·
    refine ⟨324233795292666277715088065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216155863528444185143392043 324233795292666277715088065)
    ·
      refine ⟨243175346469499708286316049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324233795292666277715088065 243175346469499708286316049)
      ·
        refine ⟨182381509852124781214737037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243175346469499708286316049 182381509852124781214737037)
        ·
          refine ⟨68393066194546792955526389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182381509852124781214737037 68393066194546792955526389)
          ·
            refine ⟨6411849955738761839580599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68393066194546792955526389 6411849955738761839580599)
            ·
              refine ⟨9617774933608142759370899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6411849955738761839580599 9617774933608142759370899)
              ·
                refine ⟨14426662400412214139056349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9617774933608142759370899 14426662400412214139056349)
                ·
                  refine ⟨5409998400154580302146131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14426662400412214139056349 5409998400154580302146131)
                  ·
                    refine ⟨8114997600231870453219197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5409998400154580302146131 8114997600231870453219197)
                    ·
                      refine ⟨3043124100086951419957199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8114997600231870453219197 3043124100086951419957199)
                      ·
                        rfl

theorem cell23_5926463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_5926463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926463 prefixEnd_5926463 := by exact prefixLift 5926463
  have htrace : WordTrace (prefixWord ++ tailWord_5926463) baseStart_5926463 baseEnd_5926463 := by
    simpa [prefixWord, tailWord_5926463, baseEnd_5926463] using wordTrace_append hprefix tailTrace_5926463
  have hstable : (prefixWord ++ tailWord_5926463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926463).length < 2 ^ (prefixWord ++ tailWord_5926463).sum := by decide
  have hdescent : baseEnd_5926463 < baseStart_5926463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926469 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_5926469 : Nat := 118140960795 + 5926469 * 2 ^ 59
def prefixEnd_5926469 : Nat := 4983230072969 + 3 ^ 40 * 5926469 * 2
def baseEnd_5926469 : Nat := 3043127180970878396482171

theorem tailTrace_5926469 : CollatzResearch.WordTrace tailWord_5926469 prefixEnd_5926469 3043127180970878396482171 := by
  unfold tailWord_5926469
  simp only [CollatzResearch.WordTrace]
  refine ⟨216156082366422448168110461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144104054910948298778740307 216156082366422448168110461)
  ·
    refine ⟨81058530887408418063041423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216156082366422448168110461 81058530887408418063041423)
    ·
      refine ⟨121587796331112627094562135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81058530887408418063041423 121587796331112627094562135)
      ·
        refine ⟨182381694496668940641843203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121587796331112627094562135 182381694496668940641843203)
        ·
          refine ⟨273572541745003410962764805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182381694496668940641843203 273572541745003410962764805)
          ·
            refine ⟨51294851577188139555518401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 273572541745003410962764805 51294851577188139555518401)
            ·
              refine ⟨38471138682891104666638801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51294851577188139555518401 38471138682891104666638801)
              ·
                refine ⟨28853354012168328499979101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38471138682891104666638801 28853354012168328499979101)
                ·
                  refine ⟨10820007754563123187492163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28853354012168328499979101 10820007754563123187492163)
                  ·
                    refine ⟨16230011631844684781238245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10820007754563123187492163 16230011631844684781238245)
                    ·
                      refine ⟨3043127180970878396482171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16230011631844684781238245 3043127180970878396482171)
                      ·
                        rfl

theorem cell23_5926469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_5926469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926469 prefixEnd_5926469 := by exact prefixLift 5926469
  have htrace : WordTrace (prefixWord ++ tailWord_5926469) baseStart_5926469 baseEnd_5926469 := by
    simpa [prefixWord, tailWord_5926469, baseEnd_5926469] using wordTrace_append hprefix tailTrace_5926469
  have hstable : (prefixWord ++ tailWord_5926469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926469).length < 2 ^ (prefixWord ++ tailWord_5926469).sum := by decide
  have hdescent : baseEnd_5926469 < baseStart_5926469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926499 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 4]
def baseStart_5926499 : Nat := 118140960795 + 5926499 * 2 ^ 59
def prefixEnd_5926499 : Nat := 4983230072969 + 3 ^ 40 * 5926499 * 2
def baseEnd_5926499 : Nat := 3043142585390513279107033

theorem tailTrace_5926499 : CollatzResearch.WordTrace tailWord_5926499 prefixEnd_5926499 3043142585390513279107033 := by
  unfold tailWord_5926499
  simp only [CollatzResearch.WordTrace]
  refine ⟨216157176556313763291702551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144104784370875842194468367 216157176556313763291702551)
  ·
    refine ⟨324235764834470644937553827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216157176556313763291702551 324235764834470644937553827)
    ·
      refine ⟨486353647251705967406330741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324235764834470644937553827 486353647251705967406330741)
      ·
        refine ⟨45595654429847434444343507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 486353647251705967406330741 45595654429847434444343507)
        ·
          refine ⟨68393481644771151666515261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45595654429847434444343507 68393481644771151666515261)
          ·
            refine ⟨25647555616789181874943223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68393481644771151666515261 25647555616789181874943223)
            ·
              refine ⟨38471333425183772812414835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25647555616789181874943223 38471333425183772812414835)
              ·
                refine ⟨57707000137775659218622253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38471333425183772812414835 57707000137775659218622253)
                ·
                  refine ⟨21640125051665872206983345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57707000137775659218622253 21640125051665872206983345)
                  ·
                    refine ⟨16230093788749404155237509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21640125051665872206983345 16230093788749404155237509)
                    ·
                      refine ⟨3043142585390513279107033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16230093788749404155237509 3043142585390513279107033)
                      ·
                        rfl

theorem cell23_5926499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_5926499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926499 prefixEnd_5926499 := by exact prefixLift 5926499
  have htrace : WordTrace (prefixWord ++ tailWord_5926499) baseStart_5926499 baseEnd_5926499 := by
    simpa [prefixWord, tailWord_5926499, baseEnd_5926499] using wordTrace_append hprefix tailTrace_5926499
  have hstable : (prefixWord ++ tailWord_5926499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926499).length < 2 ^ (prefixWord ++ tailWord_5926499).sum := by decide
  have hdescent : baseEnd_5926499 < baseStart_5926499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926506 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_5926506 : Nat := 118140960795 + 5926506 * 2 ^ 59
def prefixEnd_5926506 : Nat := 4983230072969 + 3 ^ 40 * 5926506 * 2
def baseEnd_5926506 : Nat := 3043146179755094751719501

theorem tailTrace_5926506 : CollatzResearch.WordTrace tailWord_5926506 prefixEnd_5926506 3043146179755094751719501 := by
  unfold tailWord_5926506
  simp only [CollatzResearch.WordTrace]
  refine ⟨54039357966822100871801843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144104954578192268991471581 54039357966822100871801843)
  ·
    refine ⟨81059036950233151307702765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54039357966822100871801843 81059036950233151307702765)
    ·
      refine ⟨30397138856337431740388537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81059036950233151307702765 30397138856337431740388537)
      ·
        refine ⟨22797854142253073805291403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30397138856337431740388537 22797854142253073805291403)
        ·
          refine ⟨34196781213379610707937105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22797854142253073805291403 34196781213379610707937105)
          ·
            refine ⟨25647585910034708030952829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34196781213379610707937105 25647585910034708030952829)
            ·
              refine ⟨9617844716263015511607311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25647585910034708030952829 9617844716263015511607311)
              ·
                refine ⟨14426767074394523267410967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9617844716263015511607311 14426767074394523267410967)
                ·
                  refine ⟨21640150611591784901116451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14426767074394523267410967 21640150611591784901116451)
                  ·
                    refine ⟨32460225917387677351674677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21640150611591784901116451 32460225917387677351674677)
                    ·
                      refine ⟨3043146179755094751719501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32460225917387677351674677 3043146179755094751719501)
                      ·
                        rfl

theorem cell23_5926506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_5926506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926506 prefixEnd_5926506 := by exact prefixLift 5926506
  have htrace : WordTrace (prefixWord ++ tailWord_5926506) baseStart_5926506 baseEnd_5926506 := by
    simpa [prefixWord, tailWord_5926506, baseEnd_5926506] using wordTrace_append hprefix tailTrace_5926506
  have hstable : (prefixWord ++ tailWord_5926506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926506).length < 2 ^ (prefixWord ++ tailWord_5926506).sum := by decide
  have hdescent : baseEnd_5926506 < baseStart_5926506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926509 : List Nat := [1, 5, 1, 1, 4, 11]
def baseStart_5926509 : Nat := 118140960795 + 5926509 * 2 ^ 59
def prefixEnd_5926509 : Nat := 4983230072969 + 3 ^ 40 * 5926509 * 2
def baseEnd_5926509 : Nat := 12523241646901474238609

theorem tailTrace_5926509 : CollatzResearch.WordTrace tailWord_5926509 prefixEnd_5926509 12523241646901474238609 := by
  unfold tailWord_5926509
  simp only [CollatzResearch.WordTrace]
  refine ⟨216157541286277534999566581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144105027524185023333044387 216157541286277534999566581)
  ·
    refine ⟨20264769495588518906209367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 216157541286277534999566581 20264769495588518906209367)
    ·
      refine ⟨30397154243382778359314051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20264769495588518906209367 30397154243382778359314051)
      ·
        refine ⟨45595731365074167538971077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30397154243382778359314051 45595731365074167538971077)
        ·
          refine ⟨8549199630951406413557077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45595731365074167538971077 8549199630951406413557077)
          ·
            refine ⟨12523241646901474238609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8549199630951406413557077 12523241646901474238609)
            ·
              rfl

theorem cell23_5926509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 11].length) (baseStart_5926509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926509 prefixEnd_5926509 := by exact prefixLift 5926509
  have htrace : WordTrace (prefixWord ++ tailWord_5926509) baseStart_5926509 baseEnd_5926509 := by
    simpa [prefixWord, tailWord_5926509, baseEnd_5926509] using wordTrace_append hprefix tailTrace_5926509
  have hstable : (prefixWord ++ tailWord_5926509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926509).length < 2 ^ (prefixWord ++ tailWord_5926509).sum := by decide
  have hdescent : baseEnd_5926509 < baseStart_5926509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926519 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 3]
def baseStart_5926519 : Nat := 118140960795 + 5926519 * 2 ^ 59
def prefixEnd_5926519 : Nat := 4983230072969 + 3 ^ 40 * 5926519 * 2
def baseEnd_5926519 : Nat := 3043152855003603200856941

theorem tailTrace_5926519 : CollatzResearch.WordTrace tailWord_5926519 prefixEnd_5926519 3043152855003603200856941 := by
  unfold tailWord_5926519
  simp only [CollatzResearch.WordTrace]
  refine ⟨216157906016241306707430611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144105270677494204471620407 216157906016241306707430611)
  ·
    refine ⟨324236859024361960061145917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216157906016241306707430611 324236859024361960061145917)
    ·
      refine ⟨121588822134135735022929719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324236859024361960061145917 121588822134135735022929719)
      ·
        refine ⟨182383233201203602534394579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121588822134135735022929719 182383233201203602534394579)
        ·
          refine ⟨273574849801805403801591869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182383233201203602534394579 273574849801805403801591869)
          ·
            refine ⟨102590568675677026425596951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273574849801805403801591869 102590568675677026425596951)
            ·
              refine ⟨153885853013515539638395427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102590568675677026425596951 153885853013515539638395427)
              ·
                refine ⟨230828779520273309457593141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153885853013515539638395427 230828779520273309457593141)
                ·
                  refine ⟨21640198080025622761649357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 230828779520273309457593141 21640198080025622761649357)
                  ·
                    refine ⟨8115074280009608535618509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21640198080025622761649357 8115074280009608535618509)
                    ·
                      refine ⟨3043152855003603200856941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8115074280009608535618509 3043152855003603200856941)
                      ·
                        rfl

theorem cell23_5926519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_5926519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926519 prefixEnd_5926519 := by exact prefixLift 5926519
  have htrace : WordTrace (prefixWord ++ tailWord_5926519) baseStart_5926519 baseEnd_5926519 := by
    simpa [prefixWord, tailWord_5926519, baseEnd_5926519] using wordTrace_append hprefix tailTrace_5926519
  have hstable : (prefixWord ++ tailWord_5926519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926519).length < 2 ^ (prefixWord ++ tailWord_5926519).sum := by decide
  have hdescent : baseEnd_5926519 < baseStart_5926519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926563 : List Nat := [1, 1, 1, 4, 1, 1, 5, 3, 1, 3, 2]
def baseStart_5926563 : Nat := 118140960795 + 5926563 * 2 ^ 59
def prefixEnd_5926563 : Nat := 4983230072969 + 3 ^ 40 * 5926563 * 2
def baseEnd_5926563 : Nat := 3043175448152401028706739

theorem tailTrace_5926563 : CollatzResearch.WordTrace tailWord_5926563 prefixEnd_5926563 3043175448152401028706739 := by
  unfold tailWord_5926563
  simp only [CollatzResearch.WordTrace]
  refine ⟨216159510828081902222032343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144106340552054601481354895 216159510828081902222032343)
  ·
    refine ⟨324239266242122853333048515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216159510828081902222032343 324239266242122853333048515)
    ·
      refine ⟨486358899363184279999572773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324239266242122853333048515 486358899363184279999572773)
      ·
        refine ⟨91192293630597052499919895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 486358899363184279999572773 91192293630597052499919895)
        ·
          refine ⟨136788440445895578749879843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91192293630597052499919895 136788440445895578749879843)
          ·
            refine ⟨205182660668843368124819765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136788440445895578749879843 205182660668843368124819765)
            ·
              refine ⟨19235874437704065761701853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205182660668843368124819765 19235874437704065761701853)
              ·
                refine ⟨7213452914139024660638195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19235874437704065761701853 7213452914139024660638195)
                ·
                  refine ⟨10820179371208536990957293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7213452914139024660638195 10820179371208536990957293)
                  ·
                    refine ⟨4057567264203201371608985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10820179371208536990957293 4057567264203201371608985)
                    ·
                      refine ⟨3043175448152401028706739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057567264203201371608985 3043175448152401028706739)
                      ·
                        rfl

theorem cell23_5926563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_5926563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926563 prefixEnd_5926563 := by exact prefixLift 5926563
  have htrace : WordTrace (prefixWord ++ tailWord_5926563) baseStart_5926563 baseEnd_5926563 := by
    simpa [prefixWord, tailWord_5926563, baseEnd_5926563] using wordTrace_append hprefix tailTrace_5926563
  have hstable : (prefixWord ++ tailWord_5926563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926563).length < 2 ^ (prefixWord ++ tailWord_5926563).sum := by decide
  have hdescent : baseEnd_5926563 < baseStart_5926563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926576 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 3, 4, 2]
def baseStart_5926576 : Nat := 118140960795 + 5926576 * 2 ^ 59
def prefixEnd_5926576 : Nat := 4983230072969 + 3 ^ 40 * 5926576 * 2
def baseEnd_5926576 : Nat := 3043182123400909477844179

theorem tailTrace_5926576 : CollatzResearch.WordTrace tailWord_5926576 prefixEnd_5926576 3043182123400909477844179 := by
  unfold tailWord_5926576
  simp only [CollatzResearch.WordTrace]
  refine ⟨108079992488517402721127791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144106656651356536961503721 108079992488517402721127791)
  ·
    refine ⟨162119988732776104081691687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108079992488517402721127791 162119988732776104081691687)
    ·
      refine ⟨243179983099164156122537531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162119988732776104081691687 243179983099164156122537531)
      ·
        refine ⟨364769974648746234183806297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243179983099164156122537531 364769974648746234183806297)
        ·
          refine ⟨273577480986559675637854723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364769974648746234183806297 273577480986559675637854723)
          ·
            refine ⟨410366221479839513456782085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273577480986559675637854723 410366221479839513456782085)
            ·
              refine ⟨76943666527469908773146641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 410366221479839513456782085 76943666527469908773146641)
              ·
                refine ⟨57707749895602431579859981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76943666527469908773146641 57707749895602431579859981)
                ·
                  refine ⟨21640406210850911842447493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57707749895602431579859981 21640406210850911842447493)
                  ·
                    refine ⟨4057576164534545970458905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21640406210850911842447493 4057576164534545970458905)
                    ·
                      refine ⟨3043182123400909477844179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057576164534545970458905 3043182123400909477844179)
                      ·
                        rfl

theorem cell23_5926576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 4, 2].length) (baseStart_5926576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926576 prefixEnd_5926576 := by exact prefixLift 5926576
  have htrace : WordTrace (prefixWord ++ tailWord_5926576) baseStart_5926576 baseEnd_5926576 := by
    simpa [prefixWord, tailWord_5926576, baseEnd_5926576] using wordTrace_append hprefix tailTrace_5926576
  have hstable : (prefixWord ++ tailWord_5926576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926576).length < 2 ^ (prefixWord ++ tailWord_5926576).sum := by decide
  have hdescent : baseEnd_5926576 < baseStart_5926576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926594 : List Nat := [3, 5, 1, 2, 2, 1, 2, 7]
def baseStart_5926594 : Nat := 118140960795 + 5926594 * 2 ^ 59
def prefixEnd_5926594 : Nat := 4983230072969 + 3 ^ 40 * 5926594 * 2
def baseEnd_5926594 : Nat := 112710791335284829904411

theorem tailTrace_5926594 : CollatzResearch.WordTrace tailWord_5926594 prefixEnd_5926594 112710791335284829904411 := by
  unfold tailWord_5926594
  simp only [CollatzResearch.WordTrace]
  refine ⟨54040160372742398629102709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144107094327313063010940557 54040160372742398629102709)
  ·
    refine ⟨5066265034944599871478379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54040160372742398629102709 5066265034944599871478379)
    ·
      refine ⟨7599397552416899807217569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5066265034944599871478379 7599397552416899807217569)
      ·
        refine ⟨5699548164312674855413177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7599397552416899807217569 5699548164312674855413177)
        ·
          refine ⟨4274661123234506141559883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5699548164312674855413177 4274661123234506141559883)
          ·
            refine ⟨6411991684851759212339825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4274661123234506141559883 6411991684851759212339825)
            ·
              refine ⟨4808993763638819409254869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6411991684851759212339825 4808993763638819409254869)
              ·
                refine ⟨112710791335284829904411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4808993763638819409254869 112710791335284829904411)
                ·
                  rfl

theorem cell23_5926594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 7].length) (baseStart_5926594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926594 prefixEnd_5926594 := by exact prefixLift 5926594
  have htrace : WordTrace (prefixWord ++ tailWord_5926594) baseStart_5926594 baseEnd_5926594 := by
    simpa [prefixWord, tailWord_5926594, baseEnd_5926594] using wordTrace_append hprefix tailTrace_5926594
  have hstable : (prefixWord ++ tailWord_5926594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926594).length < 2 ^ (prefixWord ++ tailWord_5926594).sum := by decide
  have hdescent : baseEnd_5926594 < baseStart_5926594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926596 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_5926596 : Nat := 118140960795 + 5926596 * 2 ^ 59
def prefixEnd_5926596 : Nat := 4983230072969 + 3 ^ 40 * 5926596 * 2
def baseEnd_5926596 : Nat := 3043192393013999399594087

theorem tailTrace_5926596 : CollatzResearch.WordTrace tailWord_5926596 prefixEnd_5926596 3043192393013999399594087 := by
  unfold tailWord_5926596
  simp only [CollatzResearch.WordTrace]
  refine ⟨108080357218481174428991821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144107142957974899238655761 108080357218481174428991821)
  ·
    refine ⟨40530133956930440410871933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108080357218481174428991821 40530133956930440410871933)
    ·
      refine ⟨15198800233848915154076975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40530133956930440410871933 15198800233848915154076975)
      ·
        refine ⟨22798200350773372731115463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15198800233848915154076975 22798200350773372731115463)
        ·
          refine ⟨34197300526160059096673195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22798200350773372731115463 34197300526160059096673195)
          ·
            refine ⟨51295950789240088645009793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34197300526160059096673195 51295950789240088645009793)
            ·
              refine ⟨38471963091930066483757345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51295950789240088645009793 38471963091930066483757345)
              ·
                refine ⟨28853972318947549862818009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38471963091930066483757345 28853972318947549862818009)
                ·
                  refine ⟨21640479239210662397113507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28853972318947549862818009 21640479239210662397113507)
                  ·
                    refine ⟨32460718858815993595670261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21640479239210662397113507 32460718858815993595670261)
                    ·
                      refine ⟨3043192393013999399594087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32460718858815993595670261 3043192393013999399594087)
                      ·
                        rfl

theorem cell23_5926596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_5926596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926596 prefixEnd_5926596 := by exact prefixLift 5926596
  have htrace : WordTrace (prefixWord ++ tailWord_5926596) baseStart_5926596 baseEnd_5926596 := by
    simpa [prefixWord, tailWord_5926596, baseEnd_5926596] using wordTrace_append hprefix tailTrace_5926596
  have hstable : (prefixWord ++ tailWord_5926596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926596).length < 2 ^ (prefixWord ++ tailWord_5926596).sum := by decide
  have hdescent : baseEnd_5926596 < baseStart_5926596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926599 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 7]
def baseStart_5926599 : Nat := 118140960795 + 5926599 * 2 ^ 59
def prefixEnd_5926599 : Nat := 4983230072969 + 3 ^ 40 * 5926599 * 2
def baseEnd_5926599 : Nat := 338132659272884765317397

theorem tailTrace_5926599 : CollatzResearch.WordTrace tailWord_5926599 prefixEnd_5926599 338132659272884765317397 := by
  unfold tailWord_5926599
  simp only [CollatzResearch.WordTrace]
  refine ⟨216160823855951480370342851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144107215903967653580228567 216160823855951480370342851)
  ·
    refine ⟨324241235783927220555514277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216160823855951480370342851 324241235783927220555514277)
    ·
      refine ⟨60795231709486353854158927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 324241235783927220555514277 60795231709486353854158927)
      ·
        refine ⟨91192847564229530781238391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60795231709486353854158927 91192847564229530781238391)
        ·
          refine ⟨136789271346344296171857587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91192847564229530781238391 136789271346344296171857587)
          ·
            refine ⟨205183907019516444257786381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136789271346344296171857587 205183907019516444257786381)
            ·
              refine ⟨76943965132318666596669893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205183907019516444257786381 76943965132318666596669893)
              ·
                refine ⟨14426993462309749986875605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76943965132318666596669893 14426993462309749986875605)
                ·
                  refine ⟨338132659272884765317397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14426993462309749986875605 338132659272884765317397)
                  ·
                    rfl

theorem cell23_5926599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 7].length) (baseStart_5926599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926599 prefixEnd_5926599 := by exact prefixLift 5926599
  have htrace : WordTrace (prefixWord ++ tailWord_5926599) baseStart_5926599 baseEnd_5926599 := by
    simpa [prefixWord, tailWord_5926599, baseEnd_5926599] using wordTrace_append hprefix tailTrace_5926599
  have hstable : (prefixWord ++ tailWord_5926599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926599).length < 2 ^ (prefixWord ++ tailWord_5926599).sum := by decide
  have hdescent : baseEnd_5926599 < baseStart_5926599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926610 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_5926610 : Nat := 118140960795 + 5926610 * 2 ^ 59
def prefixEnd_5926610 : Nat := 4983230072969 + 3 ^ 40 * 5926610 * 2
def baseEnd_5926610 : Nat := 3043199581743162344819023

theorem tailTrace_5926610 : CollatzResearch.WordTrace tailWord_5926610 prefixEnd_5926610 3043199581743162344819023 := by
  unfold tailWord_5926610
  simp only [CollatzResearch.WordTrace]
  refine ⟨54040306264727907312248321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144107483372607752832662189 54040306264727907312248321)
  ·
    refine ⟨40530229698545930484186241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54040306264727907312248321 40530229698545930484186241)
    ·
      refine ⟨30397672273909447863139681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40530229698545930484186241 30397672273909447863139681)
      ·
        refine ⟨22798254205432085897354761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30397672273909447863139681 22798254205432085897354761)
        ·
          refine ⟨17098690654074064423016071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22798254205432085897354761 17098690654074064423016071)
          ·
            refine ⟨25648035981111096634524107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17098690654074064423016071 25648035981111096634524107)
            ·
              refine ⟨38472053971666644951786161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25648035981111096634524107 38472053971666644951786161)
              ·
                refine ⟨28854040478749983713839621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38472053971666644951786161 28854040478749983713839621)
                ·
                  refine ⟨5410132589765621946344929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28854040478749983713839621 5410132589765621946344929)
                  ·
                    refine ⟨4057599442324216459758697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5410132589765621946344929 4057599442324216459758697)
                    ·
                      refine ⟨3043199581743162344819023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057599442324216459758697 3043199581743162344819023)
                      ·
                        rfl

theorem cell23_5926610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_5926610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926610 prefixEnd_5926610 := by exact prefixLift 5926610
  have htrace : WordTrace (prefixWord ++ tailWord_5926610) baseStart_5926610 baseEnd_5926610 := by
    simpa [prefixWord, tailWord_5926610, baseEnd_5926610] using wordTrace_append hprefix tailTrace_5926610
  have hstable : (prefixWord ++ tailWord_5926610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926610).length < 2 ^ (prefixWord ++ tailWord_5926610).sum := by decide
  have hdescent : baseEnd_5926610 < baseStart_5926610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926659 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 2, 8]
def baseStart_5926659 : Nat := 118140960795 + 5926659 * 2 ^ 59
def prefixEnd_5926659 : Nat := 4983230072969 + 3 ^ 40 * 5926659 * 2
def baseEnd_5926659 : Nat := 1014408247431744217702099

theorem tailTrace_5926659 : CollatzResearch.WordTrace tailWord_5926659 prefixEnd_5926659 1014408247431744217702099 := by
  unfold tailWord_5926659
  simp only [CollatzResearch.WordTrace]
  refine ⟨216163012235734110617527031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144108674823822740411684687 216163012235734110617527031)
  ·
    refine ⟨324244518353601165926290547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216163012235734110617527031 324244518353601165926290547)
    ·
      refine ⟨486366777530401748889435821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324244518353601165926290547 486366777530401748889435821)
      ·
        refine ⟨182387541573900655833538433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 486366777530401748889435821 182387541573900655833538433)
        ·
          refine ⟨136790656180425491875153825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182387541573900655833538433 136790656180425491875153825)
          ·
            refine ⟨102592992135319118906365369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136790656180425491875153825 102592992135319118906365369)
            ·
              refine ⟨76944744101489339179774027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102592992135319118906365369 76944744101489339179774027)
              ·
                refine ⟨115417116152234008769661041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76944744101489339179774027 115417116152234008769661041)
                ·
                  refine ⟨86562837114175506577245781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115417116152234008769661041 86562837114175506577245781)
                  ·
                    refine ⟨1014408247431744217702099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86562837114175506577245781 1014408247431744217702099)
                    ·
                      rfl

theorem cell23_5926659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 8].length) (baseStart_5926659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926659 prefixEnd_5926659 := by exact prefixLift 5926659
  have htrace : WordTrace (prefixWord ++ tailWord_5926659) baseStart_5926659 baseEnd_5926659 := by
    simpa [prefixWord, tailWord_5926659, baseEnd_5926659] using wordTrace_append hprefix tailTrace_5926659
  have hstable : (prefixWord ++ tailWord_5926659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926659).length < 2 ^ (prefixWord ++ tailWord_5926659).sum := by decide
  have hdescent : baseEnd_5926659 < baseStart_5926659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926699 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 9]
def baseStart_5926699 : Nat := 118140960795 + 5926699 * 2 ^ 59
def prefixEnd_5926699 : Nat := 4983230072969 + 3 ^ 40 * 5926699 * 2
def baseEnd_5926699 : Nat := 3043245281521412496606113

theorem tailTrace_5926699 : CollatzResearch.WordTrace tailWord_5926699 prefixEnd_5926699 3043245281521412496606113 := by
  unfold tailWord_5926699
  simp only [CollatzResearch.WordTrace]
  refine ⟨216164471155589197448983151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144109647437059464965988767 216164471155589197448983151)
  ·
    refine ⟨324246706733383796173474727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216164471155589197448983151 324246706733383796173474727)
    ·
      refine ⟨486370060100075694260212091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324246706733383796173474727 486370060100075694260212091)
      ·
        refine ⟨729555090150113541390318137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486370060100075694260212091 729555090150113541390318137)
        ·
          refine ⟨547166317612585156042738603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 729555090150113541390318137 547166317612585156042738603)
          ·
            refine ⟨820749476418877734064107905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547166317612585156042738603 820749476418877734064107905)
            ·
              refine ⟨615562107314158300548080929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820749476418877734064107905 615562107314158300548080929)
              ·
                refine ⟨461671580485618725411060697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615562107314158300548080929 461671580485618725411060697)
                ·
                  refine ⟨346253685364214044058295523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461671580485618725411060697 346253685364214044058295523)
                  ·
                    refine ⟨519380528046321066087443285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 346253685364214044058295523 519380528046321066087443285)
                    ·
                      refine ⟨3043245281521412496606113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 519380528046321066087443285 3043245281521412496606113)
                      ·
                        rfl

theorem cell23_5926699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_5926699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926699 prefixEnd_5926699 := by exact prefixLift 5926699
  have htrace : WordTrace (prefixWord ++ tailWord_5926699) baseStart_5926699 baseEnd_5926699 := by
    simpa [prefixWord, tailWord_5926699, baseEnd_5926699] using wordTrace_append hprefix tailTrace_5926699
  have hstable : (prefixWord ++ tailWord_5926699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926699).length < 2 ^ (prefixWord ++ tailWord_5926699).sum := by decide
  have hdescent : baseEnd_5926699 < baseStart_5926699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926710 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_5926710 : Nat := 118140960795 + 5926710 * 2 ^ 59
def prefixEnd_5926710 : Nat := 4983230072969 + 3 ^ 40 * 5926710 * 2
def baseEnd_5926710 : Nat := 1014416976602870651189521

theorem tailTrace_5926710 : CollatzResearch.WordTrace tailWord_5926710 prefixEnd_5926710 1014416976602870651189521 := by
  unfold tailWord_5926710
  simp only [CollatzResearch.WordTrace]
  refine ⟨13510304522409334145477099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144109914905699564218422389 13510304522409334145477099)
  ·
    refine ⟨20265456783614001218215649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13510304522409334145477099 20265456783614001218215649)
    ·
      refine ⟨15199092587710500913661737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20265456783614001218215649 15199092587710500913661737)
      ·
        refine ⟨11399319440782875685246303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15199092587710500913661737 11399319440782875685246303)
        ·
          refine ⟨17098979161174313527869455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11399319440782875685246303 17098979161174313527869455)
          ·
            refine ⟨25648468741761470291804183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17098979161174313527869455 25648468741761470291804183)
            ·
              refine ⟨38472703112642205437706275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25648468741761470291804183 38472703112642205437706275)
              ·
                refine ⟨57709054668963308156559413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38472703112642205437706275 57709054668963308156559413)
                ·
                  refine ⟨5410223875215310139677445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57709054668963308156559413 5410223875215310139677445)
                  ·
                    refine ⟨1014416976602870651189521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5410223875215310139677445 1014416976602870651189521)
                    ·
                      rfl

theorem cell23_5926710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_5926710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926710 prefixEnd_5926710 := by exact prefixLift 5926710
  have htrace : WordTrace (prefixWord ++ tailWord_5926710) baseStart_5926710 baseEnd_5926710 := by
    simpa [prefixWord, tailWord_5926710, baseEnd_5926710] using wordTrace_append hprefix tailTrace_5926710
  have hstable : (prefixWord ++ tailWord_5926710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926710).length < 2 ^ (prefixWord ++ tailWord_5926710).sum := by decide
  have hdescent : baseEnd_5926710 < baseStart_5926710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926740 : List Nat := [2, 4, 1, 1, 3, 3, 1, 2, 6]
def baseStart_5926740 : Nat := 118140960795 + 5926740 * 2 ^ 59
def prefixEnd_5926740 : Nat := 4983230072969 + 3 ^ 40 * 5926740 * 2
def baseEnd_5926740 : Nat := 338140703803138537354825

theorem tailTrace_5926740 : CollatzResearch.WordTrace tailWord_5926740 prefixEnd_5926740 338140703803138537354825 := by
  unfold tailWord_5926740
  simp only [CollatzResearch.WordTrace]
  refine ⟨108082983274220330725612837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144110644365627107634150449 108082983274220330725612837)
  ·
    refine ⟨20265559363916312011052407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108082983274220330725612837 20265559363916312011052407)
    ·
      refine ⟨30398339045874468016578611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20265559363916312011052407 30398339045874468016578611)
      ·
        refine ⟨45597508568811702024867917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30398339045874468016578611 45597508568811702024867917)
        ·
          refine ⟨17099065713304388259325469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45597508568811702024867917 17099065713304388259325469)
          ·
            refine ⟨6412149642489145597247051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17099065713304388259325469 6412149642489145597247051)
            ·
              refine ⟨9618224463733718395870577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6412149642489145597247051 9618224463733718395870577)
              ·
                refine ⟨7213668347800288796902933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9618224463733718395870577 7213668347800288796902933)
                ·
                  refine ⟨338140703803138537354825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7213668347800288796902933 338140703803138537354825)
                  ·
                    rfl

theorem cell23_5926740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_5926740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926740 prefixEnd_5926740 := by exact prefixLift 5926740
  have htrace : WordTrace (prefixWord ++ tailWord_5926740) baseStart_5926740 baseEnd_5926740 := by
    simpa [prefixWord, tailWord_5926740, baseEnd_5926740] using wordTrace_append hprefix tailTrace_5926740
  have hstable : (prefixWord ++ tailWord_5926740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926740).length < 2 ^ (prefixWord ++ tailWord_5926740).sum := by decide
  have hdescent : baseEnd_5926740 < baseStart_5926740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926793 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 5]
def baseStart_5926793 : Nat := 118140960795 + 5926793 * 2 ^ 59
def prefixEnd_5926793 : Nat := 4983230072969 + 3 ^ 40 * 5926793 * 2
def baseEnd_5926793 : Nat := 3043293548702935128830681

theorem tailTrace_5926793 : CollatzResearch.WordTrace tailWord_5926793 prefixEnd_5926793 3043293548702935128830681 := by
  unfold tailWord_5926793
  simp only [CollatzResearch.WordTrace]
  refine ⟨216167899617248651502905033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144111933078165767668603355 216167899617248651502905033)
  ·
    refine ⟨162125924712936488627178775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216167899617248651502905033 162125924712936488627178775)
    ·
      refine ⟨243188887069404732940768163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162125924712936488627178775 243188887069404732940768163)
      ·
        refine ⟨364783330604107099411152245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243188887069404732940768163 364783330604107099411152245)
        ·
          refine ⟨34198437244135040569795523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 364783330604107099411152245 34198437244135040569795523)
          ·
            refine ⟨51297655866202560854693285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34198437244135040569795523 51297655866202560854693285)
            ·
              refine ⟨9618310474912980160254991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51297655866202560854693285 9618310474912980160254991)
              ·
                refine ⟨14427465712369470240382487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9618310474912980160254991 14427465712369470240382487)
                ·
                  refine ⟨21641198568554205360573731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14427465712369470240382487 21641198568554205360573731)
                  ·
                    refine ⟨32461797852831308040860597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21641198568554205360573731 32461797852831308040860597)
                    ·
                      refine ⟨3043293548702935128830681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32461797852831308040860597 3043293548702935128830681)
                      ·
                        rfl

theorem cell23_5926793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 5].length) (baseStart_5926793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926793 prefixEnd_5926793 := by exact prefixLift 5926793
  have htrace : WordTrace (prefixWord ++ tailWord_5926793) baseStart_5926793 baseEnd_5926793 := by
    simpa [prefixWord, tailWord_5926793, baseEnd_5926793] using wordTrace_append hprefix tailTrace_5926793
  have hstable : (prefixWord ++ tailWord_5926793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926793).length < 2 ^ (prefixWord ++ tailWord_5926793).sum := by decide
  have hdescent : baseEnd_5926793 < baseStart_5926793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926807 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 3, 2, 2]
def baseStart_5926807 : Nat := 118140960795 + 5926807 * 2 ^ 59
def prefixEnd_5926807 : Nat := 4983230072969 + 3 ^ 40 * 5926807 * 2
def baseEnd_5926807 : Nat := 3043300737432098074055617

theorem tailTrace_5926807 : CollatzResearch.WordTrace tailWord_5926807 prefixEnd_5926807 3043300737432098074055617 := by
  unfold tailWord_5926807
  simp only [CollatzResearch.WordTrace]
  refine ⟨216168410239197931893914675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144112273492798621262609783 216168410239197931893914675)
  ·
    refine ⟨324252615358796897840872013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216168410239197931893914675 324252615358796897840872013)
    ·
      refine ⟨121594730759548836690327005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324252615358796897840872013 121594730759548836690327005)
      ·
        refine ⟨45598024034830813758872627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121594730759548836690327005 45598024034830813758872627)
        ·
          refine ⟨68397036052246220638308941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45598024034830813758872627 68397036052246220638308941)
          ·
            refine ⟨25648888519592332739365853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68397036052246220638308941 25648888519592332739365853)
            ·
              refine ⟨9618333194847124777262195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25648888519592332739365853 9618333194847124777262195)
              ·
                refine ⟨14427499792270687165893293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9618333194847124777262195 14427499792270687165893293)
                ·
                  refine ⟨5410312422101507687209985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14427499792270687165893293 5410312422101507687209985)
                  ·
                    refine ⟨4057734316576130765407489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5410312422101507687209985 4057734316576130765407489)
                    ·
                      refine ⟨3043300737432098074055617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057734316576130765407489 3043300737432098074055617)
                      ·
                        rfl

theorem cell23_5926807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_5926807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926807 prefixEnd_5926807 := by exact prefixLift 5926807
  have htrace : WordTrace (prefixWord ++ tailWord_5926807) baseStart_5926807 baseEnd_5926807 := by
    simpa [prefixWord, tailWord_5926807, baseEnd_5926807] using wordTrace_append hprefix tailTrace_5926807
  have hstable : (prefixWord ++ tailWord_5926807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926807).length < 2 ^ (prefixWord ++ tailWord_5926807).sum := by decide
  have hdescent : baseEnd_5926807 < baseStart_5926807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926813 : List Nat := [1, 4, 2, 1, 2, 3, 2, 8]
def baseStart_5926813 : Nat := 118140960795 + 5926813 * 2 ^ 59
def prefixEnd_5926813 : Nat := 4983230072969 + 3 ^ 40 * 5926813 * 2
def baseEnd_5926813 : Nat := 112714956233926853725207

theorem tailTrace_5926813 : CollatzResearch.WordTrace tailWord_5926813 prefixEnd_5926813 112714956233926853725207 := by
  unfold tailWord_5926813
  simp only [CollatzResearch.WordTrace]
  refine ⟨216168629077176194918633093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144112419384784129945755395 216168629077176194918633093)
  ·
    refine ⟨40531617951970536547243705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216168629077176194918633093 40531617951970536547243705)
    ·
      refine ⟨30398713463977902410432779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40531617951970536547243705 30398713463977902410432779)
      ·
        refine ⟨45598070195966853615649169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30398713463977902410432779 45598070195966853615649169)
        ·
          refine ⟨34198552646975140211736877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45598070195966853615649169 34198552646975140211736877)
          ·
            refine ⟨12824457242615677579401329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34198552646975140211736877 12824457242615677579401329)
            ·
              refine ⟨9618342931961758184550997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12824457242615677579401329 9618342931961758184550997)
              ·
                refine ⟨112714956233926853725207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9618342931961758184550997 112714956233926853725207)
                ·
                  rfl

theorem cell23_5926813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 8].length) (baseStart_5926813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926813 prefixEnd_5926813 := by exact prefixLift 5926813
  have htrace : WordTrace (prefixWord ++ tailWord_5926813) baseStart_5926813 baseEnd_5926813 := by
    simpa [prefixWord, tailWord_5926813, baseEnd_5926813] using wordTrace_append hprefix tailTrace_5926813
  have hstable : (prefixWord ++ tailWord_5926813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926813).length < 2 ^ (prefixWord ++ tailWord_5926813).sum := by decide
  have hdescent : baseEnd_5926813 < baseStart_5926813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926816 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 6]
def baseStart_5926816 : Nat := 118140960795 + 5926816 * 2 ^ 59
def prefixEnd_5926816 : Nat := 4983230072969 + 3 ^ 40 * 5926816 * 2
def baseEnd_5926816 : Nat := 3043305358757988538843075

theorem tailTrace_5926816 : CollatzResearch.WordTrace tailWord_5926816 prefixEnd_5926816 3043305358757988538843075 := by
  unfold tailWord_5926816
  simp only [CollatzResearch.WordTrace]
  refine ⟨108084369248082663215496151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144112492330776884287328201 108084369248082663215496151)
  ·
    refine ⟨162126553872123994823244227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108084369248082663215496151 162126553872123994823244227)
    ·
      refine ⟨243189830808185992234866341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162126553872123994823244227 243189830808185992234866341)
      ·
        refine ⟨45598093276534873544037439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243189830808185992234866341 45598093276534873544037439)
        ·
          refine ⟨68397139914802310316056159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45598093276534873544037439 68397139914802310316056159)
          ·
            refine ⟨102595709872203465474084239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68397139914802310316056159 102595709872203465474084239)
            ·
              refine ⟨153893564808305198211126359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102595709872203465474084239 153893564808305198211126359)
              ·
                refine ⟨230840347212457797316689539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153893564808305198211126359 230840347212457797316689539)
                ·
                  refine ⟨346260520818686695975034309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230840347212457797316689539 346260520818686695975034309)
                  ·
                    refine ⟨64923847653503755495318933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 346260520818686695975034309 64923847653503755495318933)
                    ·
                      refine ⟨3043305358757988538843075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64923847653503755495318933 3043305358757988538843075)
                      ·
                        rfl

theorem cell23_5926816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_5926816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926816 prefixEnd_5926816 := by exact prefixLift 5926816
  have htrace : WordTrace (prefixWord ++ tailWord_5926816) baseStart_5926816 baseEnd_5926816 := by
    simpa [prefixWord, tailWord_5926816, baseEnd_5926816] using wordTrace_append hprefix tailTrace_5926816
  have hstable : (prefixWord ++ tailWord_5926816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926816).length < 2 ^ (prefixWord ++ tailWord_5926816).sum := by decide
  have hdescent : baseEnd_5926816 < baseStart_5926816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926817 : List Nat := [1, 2, 3, 4, 2, 1, 1, 3, 2, 4]
def baseStart_5926817 : Nat := 118140960795 + 5926817 * 2 ^ 59
def prefixEnd_5926817 : Nat := 4983230072969 + 3 ^ 40 * 5926817 * 2
def baseEnd_5926817 : Nat := 1014435290746214344976857

theorem tailTrace_5926817 : CollatzResearch.WordTrace tailWord_5926817 prefixEnd_5926817 1014435290746214344976857 := by
  unfold tailWord_5926817
  simp only [CollatzResearch.WordTrace]
  refine ⟨216168774969161703601778705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144112516646107802401185803 216168774969161703601778705)
  ·
    refine ⟨162126581226871277701334029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216168774969161703601778705 162126581226871277701334029)
    ·
      refine ⟨60797467960076729138000261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162126581226871277701334029 60797467960076729138000261)
      ·
        refine ⟨11399525242514386713375049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60797467960076729138000261 11399525242514386713375049)
        ·
          refine ⟨8549643931885790035031287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11399525242514386713375049 8549643931885790035031287)
          ·
            refine ⟨12824465897828685052546931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8549643931885790035031287 12824465897828685052546931)
            ·
              refine ⟨19236698846743027578820397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12824465897828685052546931 19236698846743027578820397)
              ·
                refine ⟨7213762067528635342057649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19236698846743027578820397 7213762067528635342057649)
                ·
                  refine ⟨5410321550646476506543237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7213762067528635342057649 5410321550646476506543237)
                  ·
                    refine ⟨1014435290746214344976857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5410321550646476506543237 1014435290746214344976857)
                    ·
                      rfl

theorem cell23_5926817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_5926817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926817 prefixEnd_5926817 := by exact prefixLift 5926817
  have htrace : WordTrace (prefixWord ++ tailWord_5926817) baseStart_5926817 baseEnd_5926817 := by
    simpa [prefixWord, tailWord_5926817, baseEnd_5926817] using wordTrace_append hprefix tailTrace_5926817
  have hstable : (prefixWord ++ tailWord_5926817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926817).length < 2 ^ (prefixWord ++ tailWord_5926817).sum := by decide
  have hdescent : baseEnd_5926817 < baseStart_5926817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926844 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5926844 : Nat := 118140960795 + 5926844 * 2 ^ 59
def prefixEnd_5926844 : Nat := 4983230072969 + 3 ^ 40 * 5926844 * 2
def baseEnd_5926844 : Nat := 3043319736216314429292947

theorem tailTrace_5926844 : CollatzResearch.WordTrace tailWord_5926844 prefixEnd_5926844 3043319736216314429292947 := by
  unfold tailWord_5926844
  simp only [CollatzResearch.WordTrace]
  refine ⟨108084879870031943606505793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144113173160042591475341057 108084879870031943606505793)
  ·
    refine ⟨81063659902523957704879345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108084879870031943606505793 81063659902523957704879345)
    ·
      refine ⟨60797744926892968278659509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81063659902523957704879345 60797744926892968278659509)
      ·
        refine ⟨5699788586896215776124329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60797744926892968278659509 5699788586896215776124329)
        ·
          refine ⟨4274841440172161832093247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5699788586896215776124329 4274841440172161832093247)
          ·
            refine ⟨6412262160258242748139871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4274841440172161832093247 6412262160258242748139871)
            ·
              refine ⟨9618393240387364122209807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6412262160258242748139871 9618393240387364122209807)
              ·
                refine ⟨14427589860581046183314711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9618393240387364122209807 14427589860581046183314711)
                ·
                  refine ⟨21641384790871569274972067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14427589860581046183314711 21641384790871569274972067)
                  ·
                    refine ⟨32462077186307353912458101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21641384790871569274972067 32462077186307353912458101)
                    ·
                      refine ⟨3043319736216314429292947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32462077186307353912458101 3043319736216314429292947)
                      ·
                        rfl

theorem cell23_5926844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5926844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926844 prefixEnd_5926844 := by exact prefixLift 5926844
  have htrace : WordTrace (prefixWord ++ tailWord_5926844) baseStart_5926844 baseEnd_5926844 := by
    simpa [prefixWord, tailWord_5926844, baseEnd_5926844] using wordTrace_append hprefix tailTrace_5926844
  have hstable : (prefixWord ++ tailWord_5926844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926844).length < 2 ^ (prefixWord ++ tailWord_5926844).sum := by decide
  have hdescent : baseEnd_5926844 < baseStart_5926844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926920 : List Nat := [2, 1, 3, 2, 1, 2, 1, 6, 5]
def baseStart_5926920 : Nat := 118140960795 + 5926920 * 2 ^ 59
def prefixEnd_5926920 : Nat := 4983230072969 + 3 ^ 40 * 5926920 * 2
def baseEnd_5926920 : Nat := 338150973416228459104733

theorem tailTrace_5926920 : CollatzResearch.WordTrace tailWord_5926920 prefixEnd_5926920 338150973416228459104733 := by
  unfold tailWord_5926920
  simp only [CollatzResearch.WordTrace]
  refine ⟨108086265843894276096389107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144115021125192368128518809 108086265843894276096389107)
  ·
    refine ⟨162129398765841414144583661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108086265843894276096389107 162129398765841414144583661)
    ·
      refine ⟨60798524537190530304218873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162129398765841414144583661 60798524537190530304218873)
      ·
        refine ⟨45598893402892897728164155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60798524537190530304218873 45598893402892897728164155)
        ·
          refine ⟨68398340104339346592246233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45598893402892897728164155 68398340104339346592246233)
          ·
            refine ⟨51298755078254509944184675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68398340104339346592246233 51298755078254509944184675)
            ·
              refine ⟨76948132617381764916277013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51298755078254509944184675 76948132617381764916277013)
              ·
                refine ⟨3606943716439770230450485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76948132617381764916277013 3606943716439770230450485)
                ·
                  refine ⟨338150973416228459104733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3606943716439770230450485 338150973416228459104733)
                  ·
                    rfl

theorem cell23_5926920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 5].length) (baseStart_5926920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926920 prefixEnd_5926920 := by exact prefixLift 5926920
  have htrace : WordTrace (prefixWord ++ tailWord_5926920) baseStart_5926920 baseEnd_5926920 := by
    simpa [prefixWord, tailWord_5926920, baseEnd_5926920] using wordTrace_append hprefix tailTrace_5926920
  have hstable : (prefixWord ++ tailWord_5926920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926920).length < 2 ^ (prefixWord ++ tailWord_5926920).sum := by decide
  have hdescent : baseEnd_5926920 < baseStart_5926920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926925 : List Nat := [1, 7, 1, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_5926925 : Nat := 118140960795 + 5926925 * 2 ^ 59
def prefixEnd_5926925 : Nat := 4983230072969 + 3 ^ 40 * 5926925 * 2
def baseEnd_5926925 : Nat := 3043361328149328612380075

theorem tailTrace_5926925 : CollatzResearch.WordTrace tailWord_5926925 prefixEnd_5926925 3043361328149328612380075 := by
  unfold tailWord_5926925
  simp only [CollatzResearch.WordTrace]
  refine ⟨216172714052770438046710229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144115142701846958697806819 216172714052770438046710229)
  ·
    refine ⟨5066547985611807141719771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 216172714052770438046710229 5066547985611807141719771)
    ·
      refine ⟨7599821978417710712579657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5066547985611807141719771 7599821978417710712579657)
      ·
        refine ⟨5699866483813283034434743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7599821978417710712579657 5699866483813283034434743)
        ·
          refine ⟨8549799725719924551652115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5699866483813283034434743 8549799725719924551652115)
          ·
            refine ⟨12824699588579886827478173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8549799725719924551652115 12824699588579886827478173)
            ·
              refine ⟨4809262345717457560304315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12824699588579886827478173 4809262345717457560304315)
              ·
                refine ⟨7213893518576186340456473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4809262345717457560304315 7213893518576186340456473)
                ·
                  refine ⟨5410420138932139755342355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7213893518576186340456473 5410420138932139755342355)
                  ·
                    refine ⟨8115630208398209633013533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5410420138932139755342355 8115630208398209633013533)
                    ·
                      refine ⟨3043361328149328612380075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8115630208398209633013533 3043361328149328612380075)
                      ·
                        rfl

theorem cell23_5926925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_5926925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926925 prefixEnd_5926925 := by exact prefixLift 5926925
  have htrace : WordTrace (prefixWord ++ tailWord_5926925) baseStart_5926925 baseEnd_5926925 := by
    simpa [prefixWord, tailWord_5926925, baseEnd_5926925] using wordTrace_append hprefix tailTrace_5926925
  have hstable : (prefixWord ++ tailWord_5926925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926925).length < 2 ^ (prefixWord ++ tailWord_5926925).sum := by decide
  have hdescent : baseEnd_5926925 < baseStart_5926925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5926954 : List Nat := [3, 1, 4, 1, 2, 3, 1, 3, 5]
def baseStart_5926954 : Nat := 118140960795 + 5926954 * 2 ^ 59
def prefixEnd_5926954 : Nat := 4983230072969 + 3 ^ 40 * 5926954 * 2
def baseEnd_5926954 : Nat := 338152913232034333213049

theorem tailTrace_5926954 : CollatzResearch.WordTrace tailWord_5926954 prefixEnd_5926954 338152913232034333213049 := by
  unfold tailWord_5926954
  simp only [CollatzResearch.WordTrace]
  refine ⟨54043442942416343999878979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144115847846443583999677277 54043442942416343999878979)
  ·
    refine ⟨81065164413624515999818469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54043442942416343999878979 81065164413624515999818469)
    ·
      refine ⟨15199718327554596749965963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81065164413624515999818469 15199718327554596749965963)
      ·
        refine ⟨22799577491331895124948945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15199718327554596749965963 22799577491331895124948945)
        ·
          refine ⟨17099683118498921343711709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22799577491331895124948945 17099683118498921343711709)
          ·
            refine ⟨6412381169437095503891891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17099683118498921343711709 6412381169437095503891891)
            ·
              refine ⟨9618571754155643255837837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6412381169437095503891891 9618571754155643255837837)
              ·
                refine ⟨3606964407808366220939189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9618571754155643255837837 3606964407808366220939189)
                ·
                  refine ⟨338152913232034333213049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3606964407808366220939189 338152913232034333213049)
                  ·
                    rfl

theorem cell23_5926954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 5].length) (baseStart_5926954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5926954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5926954 prefixEnd_5926954 := by exact prefixLift 5926954
  have htrace : WordTrace (prefixWord ++ tailWord_5926954) baseStart_5926954 baseEnd_5926954 := by
    simpa [prefixWord, tailWord_5926954, baseEnd_5926954] using wordTrace_append hprefix tailTrace_5926954
  have hstable : (prefixWord ++ tailWord_5926954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5926954).length < 2 ^ (prefixWord ++ tailWord_5926954).sum := by decide
  have hdescent : baseEnd_5926954 < baseStart_5926954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5926954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927031 : List Nat := [1, 1, 3, 1, 1, 7, 2, 2, 1, 4]
def baseStart_5927031 : Nat := 118140960795 + 5927031 * 2 ^ 59
def prefixEnd_5927031 : Nat := 4983230072969 + 3 ^ 40 * 5927031 * 2
def baseEnd_5927031 : Nat := 1014471919032901732551529

theorem tailTrace_5927031 : CollatzResearch.WordTrace tailWord_5927031 prefixEnd_5927031 1014471919032901732551529 := by
  unfold tailWord_5927031
  simp only [CollatzResearch.WordTrace]
  refine ⟨216176580190386418150068947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144117720126924278766712631 216176580190386418150068947)
  ·
    refine ⟨324264870285579627225103421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216176580190386418150068947 324264870285579627225103421)
    ·
      refine ⟨121599326357092360209413783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324264870285579627225103421 121599326357092360209413783)
      ·
        refine ⟨182398989535638540314120675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121599326357092360209413783 182398989535638540314120675)
        ·
          refine ⟨273598484303457810471181013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182398989535638540314120675 273598484303457810471181013)
          ·
            refine ⟨6412464475862292432918305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 273598484303457810471181013 6412464475862292432918305)
            ·
              refine ⟨4809348356896719324688729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6412464475862292432918305 4809348356896719324688729)
              ·
                refine ⟨3607011267672539493516547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4809348356896719324688729 3607011267672539493516547)
                ·
                  refine ⟨5410516901508809240274821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3607011267672539493516547 5410516901508809240274821)
                  ·
                    refine ⟨1014471919032901732551529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5410516901508809240274821 1014471919032901732551529)
                    ·
                      rfl

theorem cell23_5927031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_5927031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927031 prefixEnd_5927031 := by exact prefixLift 5927031
  have htrace : WordTrace (prefixWord ++ tailWord_5927031) baseStart_5927031 baseEnd_5927031 := by
    simpa [prefixWord, tailWord_5927031, baseEnd_5927031] using wordTrace_append hprefix tailTrace_5927031
  have hstable : (prefixWord ++ tailWord_5927031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927031).length < 2 ^ (prefixWord ++ tailWord_5927031).sum := by decide
  have hdescent : baseEnd_5927031 < baseStart_5927031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927047 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 4, 3, 2]
def baseStart_5927047 : Nat := 118140960795 + 5927047 * 2 ^ 59
def prefixEnd_5927047 : Nat := 4983230072969 + 3 ^ 40 * 5927047 * 2
def baseEnd_5927047 : Nat := 3043423972789177135054513

theorem tailTrace_5927047 : CollatzResearch.WordTrace tailWord_5927047 prefixEnd_5927047 3043423972789177135054513 := by
  unfold tailWord_5927047
  simp only [CollatzResearch.WordTrace]
  refine ⟨216177163758328452882651395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144118109172218968588434263 216177163758328452882651395)
  ·
    refine ⟨324265745637492679323977093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216177163758328452882651395 324265745637492679323977093)
    ·
      refine ⟨60799827307029877373245705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 324265745637492679323977093 60799827307029877373245705)
      ·
        refine ⟨45599870480272408029934279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60799827307029877373245705 45599870480272408029934279)
        ·
          refine ⟨68399805720408612044901419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45599870480272408029934279 68399805720408612044901419)
          ·
            refine ⟨102599708580612918067352129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68399805720408612044901419 102599708580612918067352129)
            ·
              refine ⟨76949781435459688550514097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102599708580612918067352129 76949781435459688550514097)
              ·
                refine ⟨57712336076594766412885573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76949781435459688550514097 57712336076594766412885573)
                ·
                  refine ⟨10821063014361518702416045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57712336076594766412885573 10821063014361518702416045)
                  ·
                    refine ⟨4057898630385569513406017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10821063014361518702416045 4057898630385569513406017)
                    ·
                      refine ⟨3043423972789177135054513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057898630385569513406017 3043423972789177135054513)
                      ·
                        rfl

theorem cell23_5927047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_5927047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927047 prefixEnd_5927047 := by exact prefixLift 5927047
  have htrace : WordTrace (prefixWord ++ tailWord_5927047) baseStart_5927047 baseEnd_5927047 := by
    simpa [prefixWord, tailWord_5927047, baseEnd_5927047] using wordTrace_append hprefix tailTrace_5927047
  have hstable : (prefixWord ++ tailWord_5927047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927047).length < 2 ^ (prefixWord ++ tailWord_5927047).sum := by decide
  have hdescent : baseEnd_5927047 < baseStart_5927047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927064 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 1, 5, 2]
def baseStart_5927064 : Nat := 118140960795 + 5927064 * 2 ^ 59
def prefixEnd_5927064 : Nat := 4983230072969 + 3 ^ 40 * 5927064 * 2
def baseEnd_5927064 : Nat := 3043432701960303568541935

theorem tailTrace_5927064 : CollatzResearch.WordTrace tailWord_5927064 prefixEnd_5927064 3043432701960303568541935 := by
  unfold tailWord_5927064
  simp only [CollatzResearch.WordTrace]
  refine ⟨108088891899633432393010123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144118522532844576524013497 108088891899633432393010123)
  ·
    refine ⟨162133337849450148589515185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108088891899633432393010123 162133337849450148589515185)
    ·
      refine ⟨121600003387087611442136389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162133337849450148589515185 121600003387087611442136389)
      ·
        refine ⟨22800000635078927145400573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121600003387087611442136389 22800000635078927145400573)
        ·
          refine ⟨8550000238154597679525215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22800000635078927145400573 8550000238154597679525215)
          ·
            refine ⟨12825000357231896519287823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8550000238154597679525215 12825000357231896519287823)
            ·
              refine ⟨19237500535847844778931735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12825000357231896519287823 19237500535847844778931735)
              ·
                refine ⟨28856250803771767168397603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19237500535847844778931735 28856250803771767168397603)
                ·
                  refine ⟨43284376205657650752596405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28856250803771767168397603 43284376205657650752596405)
                  ·
                    refine ⟨4057910269280404758055913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43284376205657650752596405 4057910269280404758055913)
                    ·
                      refine ⟨3043432701960303568541935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057910269280404758055913 3043432701960303568541935)
                      ·
                        rfl

theorem cell23_5927064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_5927064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927064 prefixEnd_5927064 := by exact prefixLift 5927064
  have htrace : WordTrace (prefixWord ++ tailWord_5927064) baseStart_5927064 baseEnd_5927064 := by
    simpa [prefixWord, tailWord_5927064, baseEnd_5927064] using wordTrace_append hprefix tailTrace_5927064
  have hstable : (prefixWord ++ tailWord_5927064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927064).length < 2 ^ (prefixWord ++ tailWord_5927064).sum := by decide
  have hdescent : baseEnd_5927064 < baseStart_5927064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927071 : List Nat := [1, 1, 2, 6, 1, 1, 1, 5, 1, 1, 3]
def baseStart_5927071 : Nat := 118140960795 + 5927071 * 2 ^ 59
def prefixEnd_5927071 : Nat := 4983230072969 + 3 ^ 40 * 5927071 * 2
def baseEnd_5927071 : Nat := 3043436296324885041154403

theorem tailTrace_5927071 : CollatzResearch.WordTrace tailWord_5927071 prefixEnd_5927071 3043436296324885041154403 := by
  unfold tailWord_5927071
  simp only [CollatzResearch.WordTrace]
  refine ⟨216178039110241504981525067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144118692740161003321016711 216178039110241504981525067)
  ·
    refine ⟨324267058665362257472287601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216178039110241504981525067 324267058665362257472287601)
    ·
      refine ⟨243200293999021693104215701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324267058665362257472287601 243200293999021693104215701)
      ·
        refine ⟨11400013781204141864260111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 243200293999021693104215701 11400013781204141864260111)
        ·
          refine ⟨17100020671806212796390167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11400013781204141864260111 17100020671806212796390167)
          ·
            refine ⟨25650031007709319194585251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17100020671806212796390167 25650031007709319194585251)
            ·
              refine ⟨38475046511563978791877877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25650031007709319194585251 38475046511563978791877877)
              ·
                refine ⟨3607035610459123011738551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38475046511563978791877877 3607035610459123011738551)
                ·
                  refine ⟨5410553415688684517607827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3607035610459123011738551 5410553415688684517607827)
                  ·
                    refine ⟨8115830123533026776411741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5410553415688684517607827 8115830123533026776411741)
                    ·
                      refine ⟨3043436296324885041154403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8115830123533026776411741 3043436296324885041154403)
                      ·
                        rfl

theorem cell23_5927071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_5927071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927071 prefixEnd_5927071 := by exact prefixLift 5927071
  have htrace : WordTrace (prefixWord ++ tailWord_5927071) baseStart_5927071 baseEnd_5927071 := by
    simpa [prefixWord, tailWord_5927071, baseEnd_5927071] using wordTrace_append hprefix tailTrace_5927071
  have hstable : (prefixWord ++ tailWord_5927071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927071).length < 2 ^ (prefixWord ++ tailWord_5927071).sum := by decide
  have hdescent : baseEnd_5927071 < baseStart_5927071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927074 : List Nat := [3, 3, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_5927074 : Nat := 118140960795 + 5927074 * 2 ^ 59
def prefixEnd_5927074 : Nat := 4983230072969 + 3 ^ 40 * 5927074 * 2
def baseEnd_5927074 : Nat := 1014479278922282843138963

theorem tailTrace_5927074 : CollatzResearch.WordTrace tailWord_5927074 prefixEnd_5927074 1014479278922282843138963 := by
  unfold tailWord_5927074
  simp only [CollatzResearch.WordTrace]
  refine ⟨54044537132307659123471069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144118765686153757662589517 54044537132307659123471069)
  ·
    refine ⟨20266701424615372171301651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54044537132307659123471069 20266701424615372171301651)
    ·
      refine ⟨30400052136923058256952477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20266701424615372171301651 30400052136923058256952477)
      ·
        refine ⟨11400019551346146846357179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30400052136923058256952477 11400019551346146846357179)
        ·
          refine ⟨17100029327019220269535769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11400019551346146846357179 17100029327019220269535769)
          ·
            refine ⟨12825021995264415202151827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17100029327019220269535769 12825021995264415202151827)
            ·
              refine ⟨19237532992896622803227741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12825021995264415202151827 19237532992896622803227741)
              ·
                refine ⟨7214074872336233551210403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19237532992896622803227741 7214074872336233551210403)
                ·
                  refine ⟨10821112308504350326815605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7214074872336233551210403 10821112308504350326815605)
                  ·
                    refine ⟨1014479278922282843138963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10821112308504350326815605 1014479278922282843138963)
                    ·
                      rfl

theorem cell23_5927074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_5927074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927074 prefixEnd_5927074 := by exact prefixLift 5927074
  have htrace : WordTrace (prefixWord ++ tailWord_5927074) baseStart_5927074 baseEnd_5927074 := by
    simpa [prefixWord, tailWord_5927074, baseEnd_5927074] using wordTrace_append hprefix tailTrace_5927074
  have hstable : (prefixWord ++ tailWord_5927074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927074).length < 2 ^ (prefixWord ++ tailWord_5927074).sum := by decide
  have hdescent : baseEnd_5927074 < baseStart_5927074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927077 : List Nat := [1, 3, 1, 2, 1, 3, 3, 3, 1, 1, 4]
def baseStart_5927077 : Nat := 118140960795 + 5927077 * 2 ^ 59
def prefixEnd_5927077 : Nat := 4983230072969 + 3 ^ 40 * 5927077 * 2
def baseEnd_5927077 : Nat := 3043439377208812017679375

theorem tailTrace_5927077 : CollatzResearch.WordTrace tailWord_5927077 prefixEnd_5927077 3043439377208812017679375 := by
  unfold tailWord_5927077
  simp only [CollatzResearch.WordTrace]
  refine ⟨216178257948219768006243485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144118838632146512004162323 216178257948219768006243485)
  ·
    refine ⟨81066846730582413002341307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216178257948219768006243485 81066846730582413002341307)
    ·
      refine ⟨121600270095873619503511961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81066846730582413002341307 121600270095873619503511961)
      ·
        refine ⟨91200202571905214627633971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121600270095873619503511961 91200202571905214627633971)
        ·
          refine ⟨136800303857857821941450957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91200202571905214627633971 136800303857857821941450957)
          ·
            refine ⟨51300113946696683228044109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136800303857857821941450957 51300113946696683228044109)
            ·
              refine ⟨19237542730011256210516541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51300113946696683228044109 19237542730011256210516541)
              ·
                refine ⟨7214078523754221078943703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19237542730011256210516541 7214078523754221078943703)
                ·
                  refine ⟨10821117785631331618415555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7214078523754221078943703 10821117785631331618415555)
                  ·
                    refine ⟨16231676678446997427623333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10821117785631331618415555 16231676678446997427623333)
                    ·
                      refine ⟨3043439377208812017679375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16231676678446997427623333 3043439377208812017679375)
                      ·
                        rfl

theorem cell23_5927077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_5927077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927077 prefixEnd_5927077 := by exact prefixLift 5927077
  have htrace : WordTrace (prefixWord ++ tailWord_5927077) baseStart_5927077 baseEnd_5927077 := by
    simpa [prefixWord, tailWord_5927077, baseEnd_5927077] using wordTrace_append hprefix tailTrace_5927077
  have hstable : (prefixWord ++ tailWord_5927077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927077).length < 2 ^ (prefixWord ++ tailWord_5927077).sum := by decide
  have hdescent : baseEnd_5927077 < baseStart_5927077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927090 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_5927090 : Nat := 118140960795 + 5927090 * 2 ^ 59
def prefixEnd_5927090 : Nat := 4983230072969 + 3 ^ 40 * 5927090 * 2
def baseEnd_5927090 : Nat := 3043446052457320466816815

theorem tailTrace_5927090 : CollatzResearch.WordTrace tailWord_5927090 prefixEnd_5927090 3043446052457320466816815 := by
  unfold tailWord_5927090
  simp only [CollatzResearch.WordTrace]
  refine ⟨54044683024293167806616681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144119154731448447484311149 54044683024293167806616681)
  ·
    refine ⟨40533512268219875854962511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54044683024293167806616681 40533512268219875854962511)
    ·
      refine ⟨60800268402329813782443767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40533512268219875854962511 60800268402329813782443767)
      ·
        refine ⟨91200402603494720673665651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60800268402329813782443767 91200402603494720673665651)
        ·
          refine ⟨136800603905242081010498477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91200402603494720673665651 136800603905242081010498477)
          ·
            refine ⟨51300226464465780378936929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136800603905242081010498477 51300226464465780378936929)
            ·
              refine ⟨38475169848349335284202697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51300226464465780378936929 38475169848349335284202697)
              ·
                refine ⟨28856377386262001463152023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38475169848349335284202697 28856377386262001463152023)
                ·
                  refine ⟨43284566079393002194728035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28856377386262001463152023 43284566079393002194728035)
                  ·
                    refine ⟨64926849119089503292092053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43284566079393002194728035 64926849119089503292092053)
                    ·
                      refine ⟨3043446052457320466816815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64926849119089503292092053 3043446052457320466816815)
                      ·
                        rfl

theorem cell23_5927090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_5927090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927090 prefixEnd_5927090 := by exact prefixLift 5927090
  have htrace : WordTrace (prefixWord ++ tailWord_5927090) baseStart_5927090 baseEnd_5927090 := by
    simpa [prefixWord, tailWord_5927090, baseEnd_5927090] using wordTrace_append hprefix tailTrace_5927090
  have hstable : (prefixWord ++ tailWord_5927090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927090).length < 2 ^ (prefixWord ++ tailWord_5927090).sum := by decide
  have hdescent : baseEnd_5927090 < baseStart_5927090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927114 : List Nat := [3, 1, 2, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_5927114 : Nat := 118140960795 + 5927114 * 2 ^ 59
def prefixEnd_5927114 : Nat := 4983230072969 + 3 ^ 40 * 5927114 * 2
def baseEnd_5927114 : Nat := 3043458375993028372916705

theorem tailTrace_5927114 : CollatzResearch.WordTrace tailWord_5927114 prefixEnd_5927114 3043458375993028372916705 := by
  unfold tailWord_5927114
  simp only [CollatzResearch.WordTrace]
  refine ⟨54044901862271430831335099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144119738299390482216893597 54044901862271430831335099)
  ·
    refine ⟨81067352793407146247002649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54044901862271430831335099 81067352793407146247002649)
    ·
      refine ⟨60800514595055359685251987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81067352793407146247002649 60800514595055359685251987)
      ·
        refine ⟨91200771892583039527877981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60800514595055359685251987 91200771892583039527877981)
        ·
          refine ⟨34200289459718639822954243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91200771892583039527877981 34200289459718639822954243)
          ·
            refine ⟨51300434189577959734431365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34200289459718639822954243 51300434189577959734431365)
            ·
              refine ⟨9618831410545867450205881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51300434189577959734431365 9618831410545867450205881)
              ·
                refine ⟨7214123557909400587654411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9618831410545867450205881 7214123557909400587654411)
                ·
                  refine ⟨10821185336864100881481617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7214123557909400587654411 10821185336864100881481617)
                  ·
                    refine ⟨8115889002648075661111213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10821185336864100881481617 8115889002648075661111213)
                    ·
                      refine ⟨3043458375993028372916705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8115889002648075661111213 3043458375993028372916705)
                      ·
                        rfl

theorem cell23_5927114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_5927114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927114 prefixEnd_5927114 := by exact prefixLift 5927114
  have htrace : WordTrace (prefixWord ++ tailWord_5927114) baseStart_5927114 baseEnd_5927114 := by
    simpa [prefixWord, tailWord_5927114, baseEnd_5927114] using wordTrace_append hprefix tailTrace_5927114
  have hstable : (prefixWord ++ tailWord_5927114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927114).length < 2 ^ (prefixWord ++ tailWord_5927114).sum := by decide
  have hdescent : baseEnd_5927114 < baseStart_5927114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927128 : List Nat := [2, 1, 2, 2, 4, 1, 3, 3, 1, 2, 2]
def baseStart_5927128 : Nat := 118140960795 + 5927128 * 2 ^ 59
def prefixEnd_5927128 : Nat := 4983230072969 + 3 ^ 40 * 5927128 * 2
def baseEnd_5927128 : Nat := 3043465564722191318141641

theorem tailTrace_5927128 : CollatzResearch.WordTrace tailWord_5927128 prefixEnd_5927128 3043465564722191318141641 := by
  unfold tailWord_5927128
  simp only [CollatzResearch.WordTrace]
  refine ⟨108090059035517501858175019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144120078714023335810900025 108090059035517501858175019)
  ·
    refine ⟨162135088553276252787262529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108090059035517501858175019 162135088553276252787262529)
    ·
      refine ⟨121601316414957189590446897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162135088553276252787262529 121601316414957189590446897)
      ·
        refine ⟨91200987311217892192835173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121601316414957189590446897 91200987311217892192835173)
        ·
          refine ⟨17100185120853354786156595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91200987311217892192835173 17100185120853354786156595)
          ·
            refine ⟨25650277681280032179234893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17100185120853354786156595 25650277681280032179234893)
            ·
              refine ⟨9618854130480012067213085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25650277681280032179234893 9618854130480012067213085)
              ·
                refine ⟨3607070298930004525204907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9618854130480012067213085 3607070298930004525204907)
                ·
                  refine ⟨5410605448395006787807361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3607070298930004525204907 5410605448395006787807361)
                  ·
                    refine ⟨4057954086296255090855521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5410605448395006787807361 4057954086296255090855521)
                    ·
                      refine ⟨3043465564722191318141641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4057954086296255090855521 3043465564722191318141641)
                      ·
                        rfl

theorem cell23_5927128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_5927128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927128 prefixEnd_5927128 := by exact prefixLift 5927128
  have htrace : WordTrace (prefixWord ++ tailWord_5927128) baseStart_5927128 baseEnd_5927128 := by
    simpa [prefixWord, tailWord_5927128, baseEnd_5927128] using wordTrace_append hprefix tailTrace_5927128
  have hstable : (prefixWord ++ tailWord_5927128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927128).length < 2 ^ (prefixWord ++ tailWord_5927128).sum := by decide
  have hdescent : baseEnd_5927128 < baseStart_5927128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927140 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_5927140 : Nat := 118140960795 + 5927140 * 2 ^ 59
def prefixEnd_5927140 : Nat := 4983230072969 + 3 ^ 40 * 5927140 * 2
def baseEnd_5927140 : Nat := 3043471726490045271191585

theorem tailTrace_5927140 : CollatzResearch.WordTrace tailWord_5927140 prefixEnd_5927140 3043471726490045271191585 := by
  unfold tailWord_5927140
  simp only [CollatzResearch.WordTrace]
  refine ⟨108090277873495764882893437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144120370497994353177191249 108090277873495764882893437)
  ·
    refine ⟨40533854202560911831085039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108090277873495764882893437 40533854202560911831085039)
    ·
      refine ⟨60800781303841367746627559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40533854202560911831085039 60800781303841367746627559)
      ·
        refine ⟨91201171955762051619941339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60800781303841367746627559 91201171955762051619941339)
        ·
          refine ⟨136801757933643077429912009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91201171955762051619941339 136801757933643077429912009)
          ·
            refine ⟨102601318450232308072434007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136801757933643077429912009 102601318450232308072434007)
            ·
              refine ⟨153901977675348462108651011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102601318450232308072434007 153901977675348462108651011)
              ·
                refine ⟨230852966513022693162976517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153901977675348462108651011 230852966513022693162976517)
                ·
                  refine ⟨43284931221191754968058097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230852966513022693162976517 43284931221191754968058097)
                  ·
                    refine ⟨32463698415893816226043573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43284931221191754968058097 32463698415893816226043573)
                    ·
                      refine ⟨3043471726490045271191585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32463698415893816226043573 3043471726490045271191585)
                      ·
                        rfl

theorem cell23_5927140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_5927140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927140 prefixEnd_5927140 := by exact prefixLift 5927140
  have htrace : WordTrace (prefixWord ++ tailWord_5927140) baseStart_5927140 baseEnd_5927140 := by
    simpa [prefixWord, tailWord_5927140, baseEnd_5927140] using wordTrace_append hprefix tailTrace_5927140
  have hstable : (prefixWord ++ tailWord_5927140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927140).length < 2 ^ (prefixWord ++ tailWord_5927140).sum := by decide
  have hdescent : baseEnd_5927140 < baseStart_5927140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927144 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_5927144 : Nat := 118140960795 + 5927144 * 2 ^ 59
def prefixEnd_5927144 : Nat := 4983230072969 + 3 ^ 40 * 5927144 * 2
def baseEnd_5927144 : Nat := 3043473780412663255541567

theorem tailTrace_5927144 : CollatzResearch.WordTrace tailWord_5927144 prefixEnd_5927144 3043473780412663255541567 := by
  unfold tailWord_5927144
  simp only [CollatzResearch.WordTrace]
  refine ⟨108090350819488519224466243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144120467759318025632621657 108090350819488519224466243)
  ·
    refine ⟨162135526229232778836699365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108090350819488519224466243 162135526229232778836699365)
    ·
      refine ⟨30400411167981146031881131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162135526229232778836699365 30400411167981146031881131)
      ·
        refine ⟨45600616751971719047821697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30400411167981146031881131 45600616751971719047821697)
        ·
          refine ⟨34200462563978789285866273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45600616751971719047821697 34200462563978789285866273)
          ·
            refine ⟨25650346922984091964399705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34200462563978789285866273 25650346922984091964399705)
            ·
              refine ⟨19237760192238068973299779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25650346922984091964399705 19237760192238068973299779)
              ·
                refine ⟨28856640288357103459949669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19237760192238068973299779 28856640288357103459949669)
                ·
                  refine ⟨5410620054066956898740563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28856640288357103459949669 5410620054066956898740563)
                  ·
                    refine ⟨8115930081100435348110845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5410620054066956898740563 8115930081100435348110845)
                    ·
                      refine ⟨3043473780412663255541567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8115930081100435348110845 3043473780412663255541567)
                      ·
                        rfl

theorem cell23_5927144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_5927144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927144 prefixEnd_5927144 := by exact prefixLift 5927144
  have htrace : WordTrace (prefixWord ++ tailWord_5927144) baseStart_5927144 baseEnd_5927144 := by
    simpa [prefixWord, tailWord_5927144, baseEnd_5927144] using wordTrace_append hprefix tailTrace_5927144
  have hstable : (prefixWord ++ tailWord_5927144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927144).length < 2 ^ (prefixWord ++ tailWord_5927144).sum := by decide
  have hdescent : baseEnd_5927144 < baseStart_5927144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927160 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 2, 6]
def baseStart_5927160 : Nat := 118140960795 + 5927160 * 2 ^ 59
def prefixEnd_5927160 : Nat := 4983230072969 + 3 ^ 40 * 5927160 * 2
def baseEnd_5927160 : Nat := 1014493998701045064313831

theorem tailTrace_5927160 : CollatzResearch.WordTrace tailWord_5927160 prefixEnd_5927160 1014493998701045064313831 := by
  unfold tailWord_5927160
  simp only [CollatzResearch.WordTrace]
  refine ⟨108090642603459536590757467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144120856804612715454343289 108090642603459536590757467)
  ·
    refine ⟨162135963905189304886136201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108090642603459536590757467 162135963905189304886136201)
    ·
      refine ⟨121601972928891978664602151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162135963905189304886136201 121601972928891978664602151)
      ·
        refine ⟨182402959393337967996903227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121601972928891978664602151 182402959393337967996903227)
        ·
          refine ⟨273604439090006951995354841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182402959393337967996903227 273604439090006951995354841)
          ·
            refine ⟨205203329317505213996516131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273604439090006951995354841 205203329317505213996516131)
            ·
              refine ⟨307804993976257820994774197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205203329317505213996516131 307804993976257820994774197)
              ·
                refine ⟨28856718185274170718260081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 307804993976257820994774197 28856718185274170718260081)
                ·
                  refine ⟨21642538638955628038695061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28856718185274170718260081 21642538638955628038695061)
                  ·
                    refine ⟨1014493998701045064313831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21642538638955628038695061 1014493998701045064313831)
                    ·
                      rfl

theorem cell23_5927160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_5927160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927160 prefixEnd_5927160 := by exact prefixLift 5927160
  have htrace : WordTrace (prefixWord ++ tailWord_5927160) baseStart_5927160 baseEnd_5927160 := by
    simpa [prefixWord, tailWord_5927160, baseEnd_5927160] using wordTrace_append hprefix tailTrace_5927160
  have hstable : (prefixWord ++ tailWord_5927160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927160).length < 2 ^ (prefixWord ++ tailWord_5927160).sum := by decide
  have hdescent : baseEnd_5927160 < baseStart_5927160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927201 : List Nat := [1, 2, 3, 2, 1, 1, 3, 4, 2, 2, 2]
def baseStart_5927201 : Nat := 118140960795 + 5927201 * 2 ^ 59
def prefixEnd_5927201 : Nat := 4983230072969 + 3 ^ 40 * 5927201 * 2
def baseEnd_5927201 : Nat := 3043503048809969532528805

theorem tailTrace_5927201 : CollatzResearch.WordTrace tailWord_5927201 prefixEnd_5927201 3043503048809969532528805 := by
  unfold tailWord_5927201
  simp only [CollatzResearch.WordTrace]
  refine ⟨216182780599770537183757457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144121853733180358122504971 216182780599770537183757457)
  ·
    refine ⟨162137085449827902887818093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216182780599770537183757457 162137085449827902887818093)
    ·
      refine ⟨60801407043685463582931785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162137085449827902887818093 60801407043685463582931785)
      ·
        refine ⟨45601055282764097687198839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60801407043685463582931785 45601055282764097687198839)
        ·
          refine ⟨68401582924146146530798259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45601055282764097687198839 68401582924146146530798259)
          ·
            refine ⟨102602374386219219796197389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68401582924146146530798259 102602374386219219796197389)
            ·
              refine ⟨38475890394832207423574021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102602374386219219796197389 38475890394832207423574021)
              ·
                refine ⟨7214229449031038891920129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38475890394832207423574021 7214229449031038891920129)
                ·
                  refine ⟨5410672086773279168940097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7214229449031038891920129 5410672086773279168940097)
                  ·
                    refine ⟨4058004065079959376705073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5410672086773279168940097 4058004065079959376705073)
                    ·
                      refine ⟨3043503048809969532528805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058004065079959376705073 3043503048809969532528805)
                      ·
                        rfl

theorem cell23_5927201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_5927201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927201 prefixEnd_5927201 := by exact prefixLift 5927201
  have htrace : WordTrace (prefixWord ++ tailWord_5927201) baseStart_5927201 baseEnd_5927201 := by
    simpa [prefixWord, tailWord_5927201, baseEnd_5927201] using wordTrace_append hprefix tailTrace_5927201
  have hstable : (prefixWord ++ tailWord_5927201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927201).length < 2 ^ (prefixWord ++ tailWord_5927201).sum := by decide
  have hdescent : baseEnd_5927201 < baseStart_5927201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927257 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 4, 1, 4]
def baseStart_5927257 : Nat := 118140960795 + 5927257 * 2 ^ 59
def prefixEnd_5927257 : Nat := 4983230072969 + 3 ^ 40 * 5927257 * 2
def baseEnd_5927257 : Nat := 3043531803726621313428547

theorem tailTrace_5927257 : CollatzResearch.WordTrace tailWord_5927257 prefixEnd_5927257 3043531803726621313428547 := by
  unfold tailWord_5927257
  simp only [CollatzResearch.WordTrace]
  refine ⟨216184823087567658747796025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144123215391711772498530683 216184823087567658747796025)
  ·
    refine ⟨162138617315675744060847019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216184823087567658747796025 162138617315675744060847019)
    ·
      refine ⟨243207925973513616091270529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162138617315675744060847019 243207925973513616091270529)
      ·
        refine ⟨182405944480135212068452897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243207925973513616091270529 182405944480135212068452897)
        ·
          refine ⟨136804458360101409051339673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182405944480135212068452897 136804458360101409051339673)
          ·
            refine ⟨102603343770076056788504755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136804458360101409051339673 102603343770076056788504755)
            ·
              refine ⟨153905015655114085182757133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102603343770076056788504755 153905015655114085182757133)
              ·
                refine ⟨57714380870667781943533925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153905015655114085182757133 57714380870667781943533925)
                ·
                  refine ⟨10821446413250209114412611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57714380870667781943533925 10821446413250209114412611)
                  ·
                    refine ⟨16232169619875313671618917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10821446413250209114412611 16232169619875313671618917)
                    ·
                      refine ⟨3043531803726621313428547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16232169619875313671618917 3043531803726621313428547)
                      ·
                        rfl

theorem cell23_5927257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_5927257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927257 prefixEnd_5927257 := by exact prefixLift 5927257
  have htrace : WordTrace (prefixWord ++ tailWord_5927257) baseStart_5927257 baseEnd_5927257 := by
    simpa [prefixWord, tailWord_5927257, baseEnd_5927257] using wordTrace_append hprefix tailTrace_5927257
  have hstable : (prefixWord ++ tailWord_5927257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927257).length < 2 ^ (prefixWord ++ tailWord_5927257).sum := by decide
  have hdescent : baseEnd_5927257 < baseStart_5927257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927274 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_5927274 : Nat := 118140960795 + 5927274 * 2 ^ 59
def prefixEnd_5927274 : Nat := 4983230072969 + 3 ^ 40 * 5927274 * 2
def baseEnd_5927274 : Nat := 3043540532897747746915969

theorem tailTrace_5927274 : CollatzResearch.WordTrace tailWord_5927274 prefixEnd_5927274 3043540532897747746915969 := by
  unfold tailWord_5927274
  simp only [CollatzResearch.WordTrace]
  refine ⟨54046360782126517662791219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144123628752337380434109917 54046360782126517662791219)
  ·
    refine ⟨81069541173189776494186829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54046360782126517662791219 81069541173189776494186829)
    ·
      refine ⟨30401077939946166185320061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81069541173189776494186829 30401077939946166185320061)
      ·
        refine ⟨11400404227479812319495023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30401077939946166185320061 11400404227479812319495023)
        ·
          refine ⟨17100606341219718479242535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11400404227479812319495023 17100606341219718479242535)
          ·
            refine ⟨25650909511829577718863803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17100606341219718479242535 25650909511829577718863803)
            ·
              refine ⟨38476364267744366578295705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25650909511829577718863803 38476364267744366578295705)
              ·
                refine ⟨28857273200808274933721779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38476364267744366578295705 28857273200808274933721779)
                ·
                  refine ⟨43285909801212412400582669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28857273200808274933721779 43285909801212412400582669)
                  ·
                    refine ⟨16232216175454654650218501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43285909801212412400582669 16232216175454654650218501)
                    ·
                      refine ⟨3043540532897747746915969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16232216175454654650218501 3043540532897747746915969)
                      ·
                        rfl

theorem cell23_5927274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_5927274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927274 prefixEnd_5927274 := by exact prefixLift 5927274
  have htrace : WordTrace (prefixWord ++ tailWord_5927274) baseStart_5927274 baseEnd_5927274 := by
    simpa [prefixWord, tailWord_5927274, baseEnd_5927274] using wordTrace_append hprefix tailTrace_5927274
  have hstable : (prefixWord ++ tailWord_5927274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927274).length < 2 ^ (prefixWord ++ tailWord_5927274).sum := by decide
  have hdescent : baseEnd_5927274 < baseStart_5927274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927331 : List Nat := [1, 1, 1, 4, 1, 6, 2, 1, 6]
def baseStart_5927331 : Nat := 118140960795 + 5927331 * 2 ^ 59
def prefixEnd_5927331 : Nat := 4983230072969 + 3 ^ 40 * 5927331 * 2
def baseEnd_5927331 : Nat := 338174422366117113767023

theorem tailTrace_5927331 : CollatzResearch.WordTrace tailWord_5927331 prefixEnd_5927331 338174422366117113767023 := by
  unfold tailWord_5927331
  simp only [CollatzResearch.WordTrace]
  refine ⟨216187522089299569385989847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144125014726199712923993231 216187522089299569385989847)
  ·
    refine ⟨324281283133949354078984771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216187522089299569385989847 324281283133949354078984771)
    ·
      refine ⟨486421924700924031118477157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324281283133949354078984771 486421924700924031118477157)
      ·
        refine ⟨91204110881423255834714467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 486421924700924031118477157 91204110881423255834714467)
        ·
          refine ⟨136806166322134883752071701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91204110881423255834714467 136806166322134883752071701)
          ·
            refine ⟨6412789046350072675878361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136806166322134883752071701 6412789046350072675878361)
            ·
              refine ⟨4809591784762554506908771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6412789046350072675878361 4809591784762554506908771)
              ·
                refine ⟨7214387677143831760363157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4809591784762554506908771 7214387677143831760363157)
                ·
                  refine ⟨338174422366117113767023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7214387677143831760363157 338174422366117113767023)
                  ·
                    rfl

theorem cell23_5927331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 6].length) (baseStart_5927331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927331 prefixEnd_5927331 := by exact prefixLift 5927331
  have htrace : WordTrace (prefixWord ++ tailWord_5927331) baseStart_5927331 baseEnd_5927331 := by
    simpa [prefixWord, tailWord_5927331, baseEnd_5927331] using wordTrace_append hprefix tailTrace_5927331
  have hstable : (prefixWord ++ tailWord_5927331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927331).length < 2 ^ (prefixWord ++ tailWord_5927331).sum := by decide
  have hdescent : baseEnd_5927331 < baseStart_5927331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927351 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 2, 3, 2]
def baseStart_5927351 : Nat := 118140960795 + 5927351 * 2 ^ 59
def prefixEnd_5927351 : Nat := 4983230072969 + 3 ^ 40 * 5927351 * 2
def baseEnd_5927351 : Nat := 3043580070908143945653115

theorem tailTrace_5927351 : CollatzResearch.WordTrace tailWord_5927351 prefixEnd_5927351 3043580070908143945653115 := by
  unfold tailWord_5927351
  simp only [CollatzResearch.WordTrace]
  refine ⟨216188251549227112801717907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144125501032818075201145271 216188251549227112801717907)
  ·
    refine ⟨324282377323840669202576861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216188251549227112801717907 324282377323840669202576861)
    ·
      refine ⟨121605891496440250950966323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324282377323840669202576861 121605891496440250950966323)
      ·
        refine ⟨182408837244660376426449485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121605891496440250950966323 182408837244660376426449485)
        ·
          refine ⟨68403313966747641159918557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182408837244660376426449485 68403313966747641159918557)
          ·
            refine ⟨25651242737530365434969459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68403313966747641159918557 25651242737530365434969459)
            ·
              refine ⟨38476864106295548152454189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25651242737530365434969459 38476864106295548152454189)
              ·
                refine ⟨14428824039860830557170321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38476864106295548152454189 14428824039860830557170321)
                ·
                  refine ⟨10821618029895622917877741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14428824039860830557170321 10821618029895622917877741)
                  ·
                    refine ⟨4058106761210858594204153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10821618029895622917877741 4058106761210858594204153)
                    ·
                      refine ⟨3043580070908143945653115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058106761210858594204153 3043580070908143945653115)
                      ·
                        rfl

theorem cell23_5927351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 3, 2].length) (baseStart_5927351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927351 prefixEnd_5927351 := by exact prefixLift 5927351
  have htrace : WordTrace (prefixWord ++ tailWord_5927351) baseStart_5927351 baseEnd_5927351 := by
    simpa [prefixWord, tailWord_5927351, baseEnd_5927351] using wordTrace_append hprefix tailTrace_5927351
  have hstable : (prefixWord ++ tailWord_5927351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927351).length < 2 ^ (prefixWord ++ tailWord_5927351).sum := by decide
  have hdescent : baseEnd_5927351 < baseStart_5927351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927377 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_5927377 : Nat := 118140960795 + 5927377 * 2 ^ 59
def prefixEnd_5927377 : Nat := 4983230072969 + 3 ^ 40 * 5927377 * 2
def baseEnd_5927377 : Nat := 3043593421405160843927995

theorem tailTrace_5927377 : CollatzResearch.WordTrace tailWord_5927377 prefixEnd_5927377 3043593421405160843927995 := by
  unfold tailWord_5927377
  simp only [CollatzResearch.WordTrace]
  refine ⟨216189199847132919242164385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144126133231421946161442923 216189199847132919242164385)
  ·
    refine ⟨162141899885349689431623289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216189199847132919242164385 162141899885349689431623289)
    ·
      refine ⟨121606424914012267073717467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162141899885349689431623289 121606424914012267073717467)
      ·
        refine ⟨182409637371018400610576201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121606424914012267073717467 182409637371018400610576201)
        ·
          refine ⟨136807228028263800457932151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182409637371018400610576201 136807228028263800457932151)
          ·
            refine ⟨205210842042395700686898227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136807228028263800457932151 205210842042395700686898227)
            ·
              refine ⟨307816263063593551030347341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205210842042395700686898227 307816263063593551030347341)
              ·
                refine ⟨115431098648847581636380253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307816263063593551030347341 115431098648847581636380253)
                ·
                  refine ⟨43286661993317843113642595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115431098648847581636380253 43286661993317843113642595)
                  ·
                    refine ⟨64929992989976764670463893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43286661993317843113642595 64929992989976764670463893)
                    ·
                      refine ⟨3043593421405160843927995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64929992989976764670463893 3043593421405160843927995)
                      ·
                        rfl

theorem cell23_5927377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_5927377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927377 prefixEnd_5927377 := by exact prefixLift 5927377
  have htrace : WordTrace (prefixWord ++ tailWord_5927377) baseStart_5927377 baseEnd_5927377 := by
    simpa [prefixWord, tailWord_5927377, baseEnd_5927377] using wordTrace_append hprefix tailTrace_5927377
  have hstable : (prefixWord ++ tailWord_5927377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927377).length < 2 ^ (prefixWord ++ tailWord_5927377).sum := by decide
  have hdescent : baseEnd_5927377 < baseStart_5927377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927391 : List Nat := [1, 1, 2, 3, 3, 2, 2, 3, 2, 4]
def baseStart_5927391 : Nat := 118140960795 + 5927391 * 2 ^ 59
def prefixEnd_5927391 : Nat := 4983230072969 + 3 ^ 40 * 5927391 * 2
def baseEnd_5927391 : Nat := 1014533536711441263050977

theorem tailTrace_5927391 : CollatzResearch.WordTrace tailWord_5927391 prefixEnd_5927391 1014533536711441263050977 := by
  unfold tailWord_5927391
  simp only [CollatzResearch.WordTrace]
  refine ⟨216189710469082199633174027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144126473646054799755449351 216189710469082199633174027)
  ·
    refine ⟨324284565703623299449761041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216189710469082199633174027 324284565703623299449761041)
    ·
      refine ⟨243213424277717474587320781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324284565703623299449761041 243213424277717474587320781)
      ·
        refine ⟨91205034104144052970245293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243213424277717474587320781 91205034104144052970245293)
        ·
          refine ⟨34201887789054019863841985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91205034104144052970245293 34201887789054019863841985)
          ·
            refine ⟨25651415841790514897881489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34201887789054019863841985 25651415841790514897881489)
            ·
              refine ⟨19238561881342886173411117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25651415841790514897881489 19238561881342886173411117)
              ·
                refine ⟨7214460705503582315029169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19238561881342886173411117 7214460705503582315029169)
                ·
                  refine ⟨5410845529127686736271877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7214460705503582315029169 5410845529127686736271877)
                  ·
                    refine ⟨1014533536711441263050977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5410845529127686736271877 1014533536711441263050977)
                    ·
                      rfl

theorem cell23_5927391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 4].length) (baseStart_5927391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927391 prefixEnd_5927391 := by exact prefixLift 5927391
  have htrace : WordTrace (prefixWord ++ tailWord_5927391) baseStart_5927391 baseEnd_5927391 := by
    simpa [prefixWord, tailWord_5927391, baseEnd_5927391] using wordTrace_append hprefix tailTrace_5927391
  have hstable : (prefixWord ++ tailWord_5927391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927391).length < 2 ^ (prefixWord ++ tailWord_5927391).sum := by decide
  have hdescent : baseEnd_5927391 < baseStart_5927391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927404 : List Nat := [2, 2, 1, 1, 2, 1, 7, 7]
def baseStart_5927404 : Nat := 118140960795 + 5927404 * 2 ^ 59
def prefixEnd_5927404 : Nat := 4983230072969 + 3 ^ 40 * 5927404 * 2
def baseEnd_5927404 : Nat := 112726195754919712529273

theorem tailTrace_5927404 : CollatzResearch.WordTrace tailWord_5927404 prefixEnd_5927404 112726195754919712529273 := by
  unfold tailWord_5927404
  simp only [CollatzResearch.WordTrace]
  refine ⟨108095092309017551426698633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144126789745356735235598177 108095092309017551426698633)
  ·
    refine ⟨81071319231763163570023975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108095092309017551426698633 81071319231763163570023975)
    ·
      refine ⟨121606978847644745355035963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81071319231763163570023975 121606978847644745355035963)
      ·
        refine ⟨182410468271467118032553945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121606978847644745355035963 182410468271467118032553945)
        ·
          refine ⟨136807851203600338524415459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182410468271467118032553945 136807851203600338524415459)
          ·
            refine ⟨205211776805400507786623189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136807851203600338524415459 205211776805400507786623189)
            ·
              refine ⟨4809651018876574401248981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 205211776805400507786623189 4809651018876574401248981)
              ·
                refine ⟨112726195754919712529273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4809651018876574401248981 112726195754919712529273)
                ·
                  rfl

theorem cell23_5927404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 7].length) (baseStart_5927404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927404 prefixEnd_5927404 := by exact prefixLift 5927404
  have htrace : WordTrace (prefixWord ++ tailWord_5927404) baseStart_5927404 baseEnd_5927404 := by
    simpa [prefixWord, tailWord_5927404, baseEnd_5927404] using wordTrace_append hprefix tailTrace_5927404
  have hstable : (prefixWord ++ tailWord_5927404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927404).length < 2 ^ (prefixWord ++ tailWord_5927404).sum := by decide
  have hdescent : baseEnd_5927404 < baseStart_5927404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927441 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 3, 3, 2]
def baseStart_5927441 : Nat := 118140960795 + 5927441 * 2 ^ 59
def prefixEnd_5927441 : Nat := 4983230072969 + 3 ^ 40 * 5927441 * 2
def baseEnd_5927441 : Nat := 3043626284167048593527701

theorem tailTrace_5927441 : CollatzResearch.WordTrace tailWord_5927441 prefixEnd_5927441 3043626284167048593527701 := by
  unfold tailWord_5927441
  simp only [CollatzResearch.WordTrace]
  refine ⟨216191534118901058172494177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144127689412600705448329451 216191534118901058172494177)
  ·
    refine ⟨162143650589175793629370633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216191534118901058172494177 162143650589175793629370633)
    ·
      refine ⟨121607737941881845222027975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162143650589175793629370633 121607737941881845222027975)
      ·
        refine ⟨182411606912822767833041963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121607737941881845222027975 182411606912822767833041963)
        ·
          refine ⟨273617410369234151749562945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182411606912822767833041963 273617410369234151749562945)
          ·
            refine ⟨205213057776925613812172209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273617410369234151749562945 205213057776925613812172209)
            ·
              refine ⟨153909793332694210359129157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205213057776925613812172209 153909793332694210359129157)
              ·
                refine ⟨28858086249880164442336717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153909793332694210359129157 28858086249880164442336717)
                ·
                  refine ⟨10821782343705061665876269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28858086249880164442336717 10821782343705061665876269)
                  ·
                    refine ⟨4058168378889398124703601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10821782343705061665876269 4058168378889398124703601)
                    ·
                      refine ⟨3043626284167048593527701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058168378889398124703601 3043626284167048593527701)
                      ·
                        rfl

theorem cell23_5927441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 3, 2].length) (baseStart_5927441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927441 prefixEnd_5927441 := by exact prefixLift 5927441
  have htrace : WordTrace (prefixWord ++ tailWord_5927441) baseStart_5927441 baseEnd_5927441 := by
    simpa [prefixWord, tailWord_5927441, baseEnd_5927441] using wordTrace_append hprefix tailTrace_5927441
  have hstable : (prefixWord ++ tailWord_5927441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927441).length < 2 ^ (prefixWord ++ tailWord_5927441).sum := by decide
  have hdescent : baseEnd_5927441 < baseStart_5927441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927448 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 1, 3, 3]
def baseStart_5927448 : Nat := 118140960795 + 5927448 * 2 ^ 59
def prefixEnd_5927448 : Nat := 4983230072969 + 3 ^ 40 * 5927448 * 2
def baseEnd_5927448 : Nat := 3043629878531630066140169

theorem tailTrace_5927448 : CollatzResearch.WordTrace tailWord_5927448 prefixEnd_5927448 3043629878531630066140169 := by
  unfold tailWord_5927448
  simp only [CollatzResearch.WordTrace]
  refine ⟨108095894714937849183999499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144127859619917132245332665 108095894714937849183999499)
  ·
    refine ⟨162143842072406773775999249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108095894714937849183999499 162143842072406773775999249)
    ·
      refine ⟨121607881554305080331999437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162143842072406773775999249 121607881554305080331999437)
      ·
        refine ⟨45602955582864405124499789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121607881554305080331999437 45602955582864405124499789)
        ·
          refine ⟨17101108343574151921687421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45602955582864405124499789 17101108343574151921687421)
          ·
            refine ⟨6412915628840306970632783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17101108343574151921687421 6412915628840306970632783)
            ·
              refine ⟨9619373443260460455949175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6412915628840306970632783 9619373443260460455949175)
              ·
                refine ⟨14429060164890690683923763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9619373443260460455949175 14429060164890690683923763)
                ·
                  refine ⟨21643590247336036025885645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14429060164890690683923763 21643590247336036025885645)
                  ·
                    refine ⟨8116346342751013509707117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21643590247336036025885645 8116346342751013509707117)
                    ·
                      refine ⟨3043629878531630066140169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8116346342751013509707117 3043629878531630066140169)
                      ·
                        rfl

theorem cell23_5927448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_5927448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927448 prefixEnd_5927448 := by exact prefixLift 5927448
  have htrace : WordTrace (prefixWord ++ tailWord_5927448) baseStart_5927448 baseEnd_5927448 := by
    simpa [prefixWord, tailWord_5927448, baseEnd_5927448] using wordTrace_append hprefix tailTrace_5927448
  have hstable : (prefixWord ++ tailWord_5927448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927448).length < 2 ^ (prefixWord ++ tailWord_5927448).sum := by decide
  have hdescent : baseEnd_5927448 < baseStart_5927448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927474 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_5927474 : Nat := 118140960795 + 5927474 * 2 ^ 59
def prefixEnd_5927474 : Nat := 4983230072969 + 3 ^ 40 * 5927474 * 2
def baseEnd_5927474 : Nat := 3043643229028646964415049

theorem tailTrace_5927474 : CollatzResearch.WordTrace tailWord_5927474 prefixEnd_5927474 3043643229028646964415049 := by
  unfold tailWord_5927474
  simp only [CollatzResearch.WordTrace]
  refine ⟨54048184431945376202111369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144128491818521003205630317 54048184431945376202111369)
  ·
    refine ⟨40536138323959032151583527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54048184431945376202111369 40536138323959032151583527)
    ·
      refine ⟨60804207485938548227375291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40536138323959032151583527 60804207485938548227375291)
      ·
        refine ⟨91206311228907822341062937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60804207485938548227375291 91206311228907822341062937)
        ·
          refine ⟨68404733421680866755797203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91206311228907822341062937 68404733421680866755797203)
          ·
            refine ⟨102607100132521300133695805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68404733421680866755797203 102607100132521300133695805)
            ·
              refine ⟨38477662549695487550135927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102607100132521300133695805 38477662549695487550135927)
              ·
                refine ⟨57716493824543231325203891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38477662549695487550135927 57716493824543231325203891)
                ·
                  refine ⟨86574740736814846987805837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57716493824543231325203891 86574740736814846987805837)
                  ·
                    refine ⟨32465527776305567620427189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86574740736814846987805837 32465527776305567620427189)
                    ·
                      refine ⟨3043643229028646964415049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32465527776305567620427189 3043643229028646964415049)
                      ·
                        rfl

theorem cell23_5927474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_5927474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927474 prefixEnd_5927474 := by exact prefixLift 5927474
  have htrace : WordTrace (prefixWord ++ tailWord_5927474) baseStart_5927474 baseEnd_5927474 := by
    simpa [prefixWord, tailWord_5927474, baseEnd_5927474] using wordTrace_append hprefix tailTrace_5927474
  have hstable : (prefixWord ++ tailWord_5927474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927474).length < 2 ^ (prefixWord ++ tailWord_5927474).sum := by decide
  have hdescent : baseEnd_5927474 < baseStart_5927474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927488 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 4, 2, 2]
def baseStart_5927488 : Nat := 118140960795 + 5927488 * 2 ^ 59
def prefixEnd_5927488 : Nat := 4983230072969 + 3 ^ 40 * 5927488 * 2
def baseEnd_5927488 : Nat := 3043650417757809909639985

theorem tailTrace_5927488 : CollatzResearch.WordTrace tailWord_5927488 prefixEnd_5927488 3043650417757809909639985 := by
  unfold tailWord_5927488
  simp only [CollatzResearch.WordTrace]
  refine ⟨108096624174865392599727559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144128832233153856799636745 108096624174865392599727559)
  ·
    refine ⟨162144936262298088899591339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108096624174865392599727559 162144936262298088899591339)
    ·
      refine ⟨243217404393447133349387009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162144936262298088899591339 243217404393447133349387009)
      ·
        refine ⟨182413053295085350012040257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243217404393447133349387009 182413053295085350012040257)
        ·
          refine ⟨136809789971314012509030193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182413053295085350012040257 136809789971314012509030193)
          ·
            refine ⟨102607342478485509381772645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136809789971314012509030193 102607342478485509381772645)
            ·
              refine ⟨19238876714716033009082371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102607342478485509381772645 19238876714716033009082371)
              ·
                refine ⟨28858315072074049513623557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19238876714716033009082371 28858315072074049513623557)
                ·
                  refine ⟨5410934076013884283804417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28858315072074049513623557 5410934076013884283804417)
                  ·
                    refine ⟨4058200557010413212853313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5410934076013884283804417 4058200557010413212853313)
                    ·
                      refine ⟨3043650417757809909639985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058200557010413212853313 3043650417757809909639985)
                      ·
                        rfl

theorem cell23_5927488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 4, 2, 2].length) (baseStart_5927488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927488 prefixEnd_5927488 := by exact prefixLift 5927488
  have htrace : WordTrace (prefixWord ++ tailWord_5927488) baseStart_5927488 baseEnd_5927488 := by
    simpa [prefixWord, tailWord_5927488, baseEnd_5927488] using wordTrace_append hprefix tailTrace_5927488
  have hstable : (prefixWord ++ tailWord_5927488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927488).length < 2 ^ (prefixWord ++ tailWord_5927488).sum := by decide
  have hdescent : baseEnd_5927488 < baseStart_5927488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927505 : List Nat := [1, 2, 2, 1, 3, 4, 1, 3, 2, 2, 2]
def baseStart_5927505 : Nat := 118140960795 + 5927505 * 2 ^ 59
def prefixEnd_5927505 : Nat := 4983230072969 + 3 ^ 40 * 5927505 * 2
def baseEnd_5927505 : Nat := 3043659146928936343127407

theorem tailTrace_5927505 : CollatzResearch.WordTrace tailWord_5927505 prefixEnd_5927505 3043659146928936343127407 := by
  unfold tailWord_5927505
  simp only [CollatzResearch.WordTrace]
  refine ⟨216193868390669197102823969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144129245593779464735215979 216193868390669197102823969)
  ·
    refine ⟨162145401293001897827117977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216193868390669197102823969 162145401293001897827117977)
    ·
      refine ⟨121609050969751423370338483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162145401293001897827117977 121609050969751423370338483)
      ·
        refine ⟨182413576454627135055507725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121609050969751423370338483 182413576454627135055507725)
        ·
          refine ⟨68405091170485175645815397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182413576454627135055507725 68405091170485175645815397)
          ·
            refine ⟨12825954594465970433590387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68405091170485175645815397 12825954594465970433590387)
            ·
              refine ⟨19238931891698955650385581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12825954594465970433590387 19238931891698955650385581)
              ·
                refine ⟨7214599459387108368894593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19238931891698955650385581 7214599459387108368894593)
                ·
                  refine ⟨5410949594540331276670945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7214599459387108368894593 5410949594540331276670945)
                  ·
                    refine ⟨4058212195905248457503209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5410949594540331276670945 4058212195905248457503209)
                    ·
                      refine ⟨3043659146928936343127407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058212195905248457503209 3043659146928936343127407)
                      ·
                        rfl

theorem cell23_5927505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 2, 2].length) (baseStart_5927505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927505 prefixEnd_5927505 := by exact prefixLift 5927505
  have htrace : WordTrace (prefixWord ++ tailWord_5927505) baseStart_5927505 baseEnd_5927505 := by
    simpa [prefixWord, tailWord_5927505, baseEnd_5927505] using wordTrace_append hprefix tailTrace_5927505
  have hstable : (prefixWord ++ tailWord_5927505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927505).length < 2 ^ (prefixWord ++ tailWord_5927505).sum := by decide
  have hdescent : baseEnd_5927505 < baseStart_5927505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927522 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_5927522 : Nat := 118140960795 + 5927522 * 2 ^ 59
def prefixEnd_5927522 : Nat := 4983230072969 + 3 ^ 40 * 5927522 * 2
def baseEnd_5927522 : Nat := 3043667876100062776614829

theorem tailTrace_5927522 : CollatzResearch.WordTrace tailWord_5927522 prefixEnd_5927522 3043667876100062776614829 := by
  unfold tailWord_5927522
  simp only [CollatzResearch.WordTrace]
  refine ⟨54048622107901902251548205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144129658954405072670795213 54048622107901902251548205)
  ·
    refine ⟨20268233290463213344330577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54048622107901902251548205 20268233290463213344330577)
    ·
      refine ⟨15201174967847410008247933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20268233290463213344330577 15201174967847410008247933)
      ·
        refine ⟨5700440612942778753092975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15201174967847410008247933 5700440612942778753092975)
        ·
          refine ⟨8550660919414168129639463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5700440612942778753092975 8550660919414168129639463)
          ·
            refine ⟨12825991379121252194459195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8550660919414168129639463 12825991379121252194459195)
            ·
              refine ⟨19238987068681878291688793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12825991379121252194459195 19238987068681878291688793)
              ·
                refine ⟨14429240301511408718766595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19238987068681878291688793 14429240301511408718766595)
                ·
                  refine ⟨21643860452267113078149893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14429240301511408718766595 21643860452267113078149893)
                  ·
                    refine ⟨4058223834800083702153105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21643860452267113078149893 4058223834800083702153105)
                    ·
                      refine ⟨3043667876100062776614829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058223834800083702153105 3043667876100062776614829)
                      ·
                        rfl

theorem cell23_5927522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_5927522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927522 prefixEnd_5927522 := by exact prefixLift 5927522
  have htrace : WordTrace (prefixWord ++ tailWord_5927522) baseStart_5927522 baseEnd_5927522 := by
    simpa [prefixWord, tailWord_5927522, baseEnd_5927522] using wordTrace_append hprefix tailTrace_5927522
  have hstable : (prefixWord ++ tailWord_5927522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927522).length < 2 ^ (prefixWord ++ tailWord_5927522).sum := by decide
  have hdescent : baseEnd_5927522 < baseStart_5927522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927545 : List Nat := [1, 2, 1, 3, 3, 4, 2, 2, 5]
def baseStart_5927545 : Nat := 118140960795 + 5927545 * 2 ^ 59
def prefixEnd_5927545 : Nat := 4983230072969 + 3 ^ 40 * 5927545 * 2
def baseEnd_5927545 : Nat := 338186631795012909625247

theorem tailTrace_5927545 : CollatzResearch.WordTrace tailWord_5927545 prefixEnd_5927545 338186631795012909625247 := by
  unfold tailWord_5927545
  simp only [CollatzResearch.WordTrace]
  refine ⟨216195327310524283934280089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144130218207016189289520059 216195327310524283934280089)
  ·
    refine ⟨162146495482893212950710067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216195327310524283934280089 162146495482893212950710067)
    ·
      refine ⟨243219743224339819426065101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162146495482893212950710067 243219743224339819426065101)
      ·
        refine ⟨91207403709127432284774413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243219743224339819426065101 91207403709127432284774413)
        ·
          refine ⟨34202776390922787106790405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91207403709127432284774413 34202776390922787106790405)
          ·
            refine ⟨6413020573298022582523201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34202776390922787106790405 6413020573298022582523201)
            ·
              refine ⟨4809765429973516936892401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6413020573298022582523201 4809765429973516936892401)
              ·
                refine ⟨3607324072480137702669301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4809765429973516936892401 3607324072480137702669301)
                ·
                  refine ⟨338186631795012909625247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3607324072480137702669301 338186631795012909625247)
                  ·
                    rfl

theorem cell23_5927545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 5].length) (baseStart_5927545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927545 prefixEnd_5927545 := by exact prefixLift 5927545
  have htrace : WordTrace (prefixWord ++ tailWord_5927545) baseStart_5927545 baseEnd_5927545 := by
    simpa [prefixWord, tailWord_5927545, baseEnd_5927545] using wordTrace_append hprefix tailTrace_5927545
  have hstable : (prefixWord ++ tailWord_5927545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927545).length < 2 ^ (prefixWord ++ tailWord_5927545).sum := by decide
  have hdescent : baseEnd_5927545 < baseStart_5927545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927571 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 3, 4]
def baseStart_5927571 : Nat := 118140960795 + 5927571 * 2 ^ 59
def prefixEnd_5927571 : Nat := 4983230072969 + 3 ^ 40 * 5927571 * 2
def baseEnd_5927571 : Nat := 1014564345550711028300701

theorem tailTrace_5927571 : CollatzResearch.WordTrace tailWord_5927571 prefixEnd_5927571 1014564345550711028300701 := by
  unfold tailWord_5927571
  simp only [CollatzResearch.WordTrace]
  refine ⟨216196275608430090374726567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144130850405620060249817711 216196275608430090374726567)
  ·
    refine ⟨324294413412645135562089851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216196275608430090374726567 324294413412645135562089851)
    ·
      refine ⟨486441620118967703343134777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324294413412645135562089851 486441620118967703343134777)
      ·
        refine ⟨364831215089225777507351083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486441620118967703343134777 364831215089225777507351083)
        ·
          refine ⟨547246822633838666261026625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364831215089225777507351083 547246822633838666261026625)
          ·
            refine ⟨410435116975378999695769969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547246822633838666261026625 410435116975378999695769969)
            ·
              refine ⟨307826337731534249771827477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410435116975378999695769969 307826337731534249771827477)
              ·
                refine ⟨14429359581165667958054413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 307826337731534249771827477 14429359581165667958054413)
                ·
                  refine ⟨5411009842937125484270405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14429359581165667958054413 5411009842937125484270405)
                  ·
                    refine ⟨1014564345550711028300701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5411009842937125484270405 1014564345550711028300701)
                    ·
                      rfl

theorem cell23_5927571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 4].length) (baseStart_5927571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927571 prefixEnd_5927571 := by exact prefixLift 5927571
  have htrace : WordTrace (prefixWord ++ tailWord_5927571) baseStart_5927571 baseEnd_5927571 := by
    simpa [prefixWord, tailWord_5927571, baseEnd_5927571] using wordTrace_append hprefix tailTrace_5927571
  have hstable : (prefixWord ++ tailWord_5927571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927571).length < 2 ^ (prefixWord ++ tailWord_5927571).sum := by decide
  have hdescent : baseEnd_5927571 < baseStart_5927571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927605 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 3, 4]
def baseStart_5927605 : Nat := 118140960795 + 5927605 * 2 ^ 59
def prefixEnd_5927605 : Nat := 4983230072969 + 3 ^ 40 * 5927605 * 2
def baseEnd_5927605 : Nat := 1014570164998128650625649

theorem tailTrace_5927605 : CollatzResearch.WordTrace tailWord_5927605 prefixEnd_5927605 1014570164998128650625649 := by
  unfold tailWord_5927605
  simp only [CollatzResearch.WordTrace]
  refine ⟨216197515690306914181464269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144131677126871276120976179 216197515690306914181464269)
  ·
    refine ⟨81074068383865092818049101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216197515690306914181464269 81074068383865092818049101)
    ·
      refine ⟨30402775643949409806768413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81074068383865092818049101 30402775643949409806768413)
      ·
        refine ⟨11401040866481028677538155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30402775643949409806768413 11401040866481028677538155)
        ·
          refine ⟨17101561299721543016307233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11401040866481028677538155 17101561299721543016307233)
          ·
            refine ⟨12826170974791157262230425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17101561299721543016307233 12826170974791157262230425)
            ·
              refine ⟨9619628231093367946672819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12826170974791157262230425 9619628231093367946672819)
              ·
                refine ⟨14429442346640051920009229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9619628231093367946672819 14429442346640051920009229)
                ·
                  refine ⟨5411040879990019470003461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14429442346640051920009229 5411040879990019470003461)
                  ·
                    refine ⟨1014570164998128650625649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5411040879990019470003461 1014570164998128650625649)
                    ·
                      rfl

theorem cell23_5927605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_5927605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927605 prefixEnd_5927605 := by exact prefixLift 5927605
  have htrace : WordTrace (prefixWord ++ tailWord_5927605) baseStart_5927605 baseEnd_5927605 := by
    simpa [prefixWord, tailWord_5927605, baseEnd_5927605] using wordTrace_append hprefix tailTrace_5927605
  have hstable : (prefixWord ++ tailWord_5927605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927605).length < 2 ^ (prefixWord ++ tailWord_5927605).sum := by decide
  have hdescent : baseEnd_5927605 < baseStart_5927605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927662 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_5927662 : Nat := 118140960795 + 5927662 * 2 ^ 59
def prefixEnd_5927662 : Nat := 4983230072969 + 3 ^ 40 * 5927662 * 2
def baseEnd_5927662 : Nat := 3043739763391692228864185

theorem tailTrace_5927662 : CollatzResearch.WordTrace tailWord_5927662 prefixEnd_5927662 3043739763391692228864185 := by
  unfold tailWord_5927662
  simp only [CollatzResearch.WordTrace]
  refine ⟨27024949331387551614536155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144133063100733608610859493 27024949331387551614536155)
  ·
    refine ⟨40537423997081327421804233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27024949331387551614536155 40537423997081327421804233)
    ·
      refine ⟨30403067997810995566353175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40537423997081327421804233 30403067997810995566353175)
      ·
        refine ⟨45604601996716493349529763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30403067997810995566353175 45604601996716493349529763)
        ·
          refine ⟨68406902995074740024294645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45604601996716493349529763 68406902995074740024294645)
          ·
            refine ⟨6413147155788256877277623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68406902995074740024294645 6413147155788256877277623)
            ·
              refine ⟨9619720733682385315916435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6413147155788256877277623 9619720733682385315916435)
              ·
                refine ⟨14429581100523577973874653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9619720733682385315916435 14429581100523577973874653)
                ·
                  refine ⟨5411092912696341740202995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14429581100523577973874653 5411092912696341740202995)
                  ·
                    refine ⟨8116639369044512610304493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5411092912696341740202995 8116639369044512610304493)
                    ·
                      refine ⟨3043739763391692228864185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8116639369044512610304493 3043739763391692228864185)
                      ·
                        rfl

theorem cell23_5927662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_5927662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927662 prefixEnd_5927662 := by exact prefixLift 5927662
  have htrace : WordTrace (prefixWord ++ tailWord_5927662) baseStart_5927662 baseEnd_5927662 := by
    simpa [prefixWord, tailWord_5927662, baseEnd_5927662] using wordTrace_append hprefix tailTrace_5927662
  have hstable : (prefixWord ++ tailWord_5927662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927662).length < 2 ^ (prefixWord ++ tailWord_5927662).sum := by decide
  have hdescent : baseEnd_5927662 < baseStart_5927662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927671 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 3]
def baseStart_5927671 : Nat := 118140960795 + 5927671 * 2 ^ 59
def prefixEnd_5927671 : Nat := 4983230072969 + 3 ^ 40 * 5927671 * 2
def baseEnd_5927671 : Nat := 3043744384717582693651643

theorem tailTrace_5927671 : CollatzResearch.WordTrace tailWord_5927671 prefixEnd_5927671 3043744384717582693651643 := by
  unfold tailWord_5927671
  simp only [CollatzResearch.WordTrace]
  refine ⟨216199922908067807453366867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144133281938711871635577911 216199922908067807453366867)
  ·
    refine ⟨324299884362101711180050301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216199922908067807453366867 324299884362101711180050301)
    ·
      refine ⟨121612456635788141692518863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324299884362101711180050301 121612456635788141692518863)
      ·
        refine ⟨182418684953682212538778295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121612456635788141692518863 182418684953682212538778295)
        ·
          refine ⟨273628027430523318808167443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182418684953682212538778295 273628027430523318808167443)
          ·
            refine ⟨410442041145784978212251165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273628027430523318808167443 410442041145784978212251165)
            ·
              refine ⟨153915765429669366829594187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 410442041145784978212251165 153915765429669366829594187)
              ·
                refine ⟨230873648144504050244391281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153915765429669366829594187 230873648144504050244391281)
                ·
                  refine ⟨173155236108378037683293461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230873648144504050244391281 173155236108378037683293461)
                  ·
                    refine ⟨8116651692580220516404381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 173155236108378037683293461 8116651692580220516404381)
                    ·
                      refine ⟨3043744384717582693651643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8116651692580220516404381 3043744384717582693651643)
                      ·
                        rfl

theorem cell23_5927671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_5927671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927671 prefixEnd_5927671 := by exact prefixLift 5927671
  have htrace : WordTrace (prefixWord ++ tailWord_5927671) baseStart_5927671 baseEnd_5927671 := by
    simpa [prefixWord, tailWord_5927671, baseEnd_5927671] using wordTrace_append hprefix tailTrace_5927671
  have hstable : (prefixWord ++ tailWord_5927671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927671).length < 2 ^ (prefixWord ++ tailWord_5927671).sum := by decide
  have hdescent : baseEnd_5927671 < baseStart_5927671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927682 : List Nat := [3, 4, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_5927682 : Nat := 118140960795 + 5927682 * 2 ^ 59
def prefixEnd_5927682 : Nat := 4983230072969 + 3 ^ 40 * 5927682 * 2
def baseEnd_5927682 : Nat := 1014583344334927383538031

theorem tailTrace_5927682 : CollatzResearch.WordTrace tailWord_5927682 prefixEnd_5927682 1014583344334927383538031 := by
  unfold tailWord_5927682
  simp only [CollatzResearch.WordTrace]
  refine ⟨54050081027756989083004325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144133549407351970888011533 54050081027756989083004325)
  ·
    refine ⟨10134390192704435453063311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54050081027756989083004325 10134390192704435453063311)
    ·
      refine ⟨15201585289056653179594967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10134390192704435453063311 15201585289056653179594967)
      ·
        refine ⟨22802377933584979769392451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15201585289056653179594967 22802377933584979769392451)
        ·
          refine ⟨34203566900377469654088677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22802377933584979769392451 34203566900377469654088677)
          ·
            refine ⟨6413168793820775560141627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34203566900377469654088677 6413168793820775560141627)
            ·
              refine ⟨9619753190731163340212441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6413168793820775560141627 9619753190731163340212441)
              ·
                refine ⟨7214814893048372505159331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9619753190731163340212441 7214814893048372505159331)
                ·
                  refine ⟨10822222339572558757738997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7214814893048372505159331 10822222339572558757738997)
                  ·
                    refine ⟨1014583344334927383538031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10822222339572558757738997 1014583344334927383538031)
                    ·
                      rfl

theorem cell23_5927682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_5927682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927682 prefixEnd_5927682 := by exact prefixLift 5927682
  have htrace : WordTrace (prefixWord ++ tailWord_5927682) baseStart_5927682 baseEnd_5927682 := by
    simpa [prefixWord, tailWord_5927682, baseEnd_5927682] using wordTrace_append hprefix tailTrace_5927682
  have hstable : (prefixWord ++ tailWord_5927682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927682).length < 2 ^ (prefixWord ++ tailWord_5927682).sum := by decide
  have hdescent : baseEnd_5927682 < baseStart_5927682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
