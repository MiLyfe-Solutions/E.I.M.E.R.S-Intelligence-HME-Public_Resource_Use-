import V185TrunkScan21Chunk061

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_750505 : List Nat := [1, 2, 1, 1, 1, 1, 7, 4, 3]
def baseStart_750505 : Nat := 118140960795 + 750505 * 2 ^ 59
def prefixEnd_750505 : Nat := 4983230072969 + 3 ^ 40 * 750505 * 2
def baseEnd_750505 : Nat := 171275466045640613082665

theorem tailTrace_750505 : CollatzResearch.WordTrace tailWord_750505 prefixEnd_750505 171275466045640613082665 := by
  unfold tailWord_750505
  simp only [CollatzResearch.WordTrace]
  refine ⟨27373166146056035894492969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18248777430704023929661979 27373166146056035894492969)
  ·
    refine ⟨20529874609542026920869727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27373166146056035894492969 20529874609542026920869727)
    ·
      refine ⟨30794811914313040381304591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20529874609542026920869727 30794811914313040381304591)
      ·
        refine ⟨46192217871469560571956887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30794811914313040381304591 46192217871469560571956887)
        ·
          refine ⟨69288326807204340857935331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46192217871469560571956887 69288326807204340857935331)
          ·
            refine ⟨103932490210806511286902997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69288326807204340857935331 103932490210806511286902997)
            ·
              refine ⟨2435917739315777608286789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 103932490210806511286902997 2435917739315777608286789)
              ·
                refine ⟨456734576121708301553773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2435917739315777608286789 456734576121708301553773)
                ·
                  refine ⟨171275466045640613082665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456734576121708301553773 171275466045640613082665)
                  ·
                    rfl

theorem cell21_750505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 3].length) (baseStart_750505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750505 prefixEnd_750505 := by exact prefixLift 750505
  have htrace : WordTrace (prefixWord ++ tailWord_750505) baseStart_750505 baseEnd_750505 := by
    simpa [prefixWord, tailWord_750505, baseEnd_750505] using wordTrace_append hprefix tailTrace_750505
  have hstable : (prefixWord ++ tailWord_750505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750505).length < 2 ^ (prefixWord ++ tailWord_750505).sum := by decide
  have hdescent : baseEnd_750505 < baseStart_750505 := by decide
  rcases family_descends (prefixWord ++ tailWord_750505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750519 : List Nat := [1, 1, 3, 1, 3, 1, 4, 3, 4]
def baseStart_750519 : Nat := 118140960795 + 750519 * 2 ^ 59
def prefixEnd_750519 : Nat := 4983230072969 + 3 ^ 40 * 750519 * 2
def baseEnd_750519 : Nat := 171278661036379699849303

theorem tailTrace_750519 : CollatzResearch.WordTrace tailWord_750519 prefixEnd_750519 171278661036379699849303 := by
  unfold tailWord_750519
  simp only [CollatzResearch.WordTrace]
  refine ⟨27373676768005316285502611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18249117845336877523668407 27373676768005316285502611)
  ·
    refine ⟨41060515152007974428253917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27373676768005316285502611 41060515152007974428253917)
    ·
      refine ⟨15397693182002990410595219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41060515152007974428253917 15397693182002990410595219)
      ·
        refine ⟨23096539773004485615892829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15397693182002990410595219 23096539773004485615892829)
        ·
          refine ⟨8661202414876682105959811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23096539773004485615892829 8661202414876682105959811)
          ·
            refine ⟨12991803622315023158939717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8661202414876682105959811 12991803622315023158939717)
            ·
              refine ⟨2435963179184066842301197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12991803622315023158939717 2435963179184066842301197)
              ·
                refine ⟨913486192194025065862949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2435963179184066842301197 913486192194025065862949)
                ·
                  refine ⟨171278661036379699849303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 913486192194025065862949 171278661036379699849303)
                  ·
                    rfl

theorem cell21_750519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 4].length) (baseStart_750519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750519 prefixEnd_750519 := by exact prefixLift 750519
  have htrace : WordTrace (prefixWord ++ tailWord_750519) baseStart_750519 baseEnd_750519 := by
    simpa [prefixWord, tailWord_750519, baseEnd_750519] using wordTrace_append hprefix tailTrace_750519
  have hstable : (prefixWord ++ tailWord_750519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750519).length < 2 ^ (prefixWord ++ tailWord_750519).sum := by decide
  have hdescent : baseEnd_750519 < baseStart_750519 := by decide
  rcases family_descends (prefixWord ++ tailWord_750519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750615 : List Nat := [1, 1, 3, 5, 1, 2, 3, 2, 3]
def baseStart_750615 : Nat := 118140960795 + 750615 * 2 ^ 59
def prefixEnd_750615 : Nat := 4983230072969 + 3 ^ 40 * 750615 * 2
def baseEnd_750615 : Nat := 171300569544304866249107

theorem tailTrace_750615 : CollatzResearch.WordTrace tailWord_750615 prefixEnd_750615 171300569544304866249107 := by
  unfold tailWord_750615
  simp only [CollatzResearch.WordTrace]
  refine ⟨27377178175657524680997299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18251452117105016453998199 27377178175657524680997299)
  ·
    refine ⟨41065767263486287021495949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27377178175657524680997299 41065767263486287021495949)
    ·
      refine ⟨15399662723807357633060981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41065767263486287021495949 15399662723807357633060981)
      ·
        refine ⟨1443718380356939778099467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15399662723807357633060981 1443718380356939778099467)
        ·
          refine ⟨2165577570535409667149201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443718380356939778099467 2165577570535409667149201)
          ·
            refine ⟨1624183177901557250361901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2165577570535409667149201 1624183177901557250361901)
            ·
              refine ⟨609068691713083968885713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1624183177901557250361901 609068691713083968885713)
              ·
                refine ⟨456801518784812976664285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609068691713083968885713 456801518784812976664285)
                ·
                  refine ⟨171300569544304866249107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456801518784812976664285 171300569544304866249107)
                  ·
                    rfl

theorem cell21_750615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 3].length) (baseStart_750615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750615 prefixEnd_750615 := by exact prefixLift 750615
  have htrace : WordTrace (prefixWord ++ tailWord_750615) baseStart_750615 baseEnd_750615 := by
    simpa [prefixWord, tailWord_750615, baseEnd_750615] using wordTrace_append hprefix tailTrace_750615
  have hstable : (prefixWord ++ tailWord_750615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750615).length < 2 ^ (prefixWord ++ tailWord_750615).sum := by decide
  have hdescent : baseEnd_750615 < baseStart_750615 := by decide
  rcases family_descends (prefixWord ++ tailWord_750615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750626 : List Nat := [3, 3, 1, 1, 1, 4, 2, 6]
def baseStart_750626 : Nat := 118140960795 + 750626 * 2 ^ 59
def prefixEnd_750626 : Nat := 4983230072969 + 3 ^ 40 * 750626 * 2
def baseEnd_750626 : Nat := 57101026631390430521917

theorem tailTrace_750626 : CollatzResearch.WordTrace tailWord_750626 prefixEnd_750626 57101026631390430521917 := by
  unfold tailWord_750626
  simp only [CollatzResearch.WordTrace]
  refine ⟨6844394844654418389911933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18251719585745115706431821 6844394844654418389911933)
  ·
    refine ⟨2566648066745406896216975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6844394844654418389911933 2566648066745406896216975)
    ·
      refine ⟨3849972100118110344325463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2566648066745406896216975 3849972100118110344325463)
      ·
        refine ⟨5774958150177165516488195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3849972100118110344325463 5774958150177165516488195)
        ·
          refine ⟨8662437225265748274732293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5774958150177165516488195 8662437225265748274732293)
          ·
            refine ⟨1624206979737327801512305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8662437225265748274732293 1624206979737327801512305)
            ·
              refine ⟨1218155234802995851134229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1624206979737327801512305 1218155234802995851134229)
              ·
                refine ⟨57101026631390430521917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1218155234802995851134229 57101026631390430521917)
                ·
                  rfl

theorem cell21_750626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_750626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750626 prefixEnd_750626 := by exact prefixLift 750626
  have htrace : WordTrace (prefixWord ++ tailWord_750626) baseStart_750626 baseEnd_750626 := by
    simpa [prefixWord, tailWord_750626, baseEnd_750626] using wordTrace_append hprefix tailTrace_750626
  have hstable : (prefixWord ++ tailWord_750626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750626).length < 2 ^ (prefixWord ++ tailWord_750626).sum := by decide
  have hdescent : baseEnd_750626 < baseStart_750626 := by decide
  rcases family_descends (prefixWord ++ tailWord_750626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750674 : List Nat := [3, 2, 2, 1, 3, 2, 1, 4, 3]
def baseStart_750674 : Nat := 118140960795 + 750674 * 2 ^ 59
def prefixEnd_750674 : Nat := 4983230072969 + 3 ^ 40 * 750674 * 2
def baseEnd_750674 : Nat := 171314034148133874765653

theorem tailTrace_750674 : CollatzResearch.WordTrace tailWord_750674 prefixEnd_750674 171314034148133874765653 := by
  unfold tailWord_750674
  simp only [CollatzResearch.WordTrace]
  refine ⟨6844832520610944439348769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18252886721629185171596717 6844832520610944439348769)
  ·
    refine ⟨5133624390458208329511577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6844832520610944439348769 5133624390458208329511577)
    ·
      refine ⟨3850218292843656247133683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5133624390458208329511577 3850218292843656247133683)
      ·
        refine ⟨5775327439265484370700525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3850218292843656247133683 5775327439265484370700525)
        ·
          refine ⟨2165747789724556639012697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5775327439265484370700525 2165747789724556639012697)
          ·
            refine ⟨1624310842293417479259523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2165747789724556639012697 1624310842293417479259523)
            ·
              refine ⟨2436466263440126218889285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624310842293417479259523 2436466263440126218889285)
              ·
                refine ⟨456837424395023666041741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2436466263440126218889285 456837424395023666041741)
                ·
                  refine ⟨171314034148133874765653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456837424395023666041741 171314034148133874765653)
                  ·
                    rfl

theorem cell21_750674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_750674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750674 prefixEnd_750674 := by exact prefixLift 750674
  have htrace : WordTrace (prefixWord ++ tailWord_750674) baseStart_750674 baseEnd_750674 := by
    simpa [prefixWord, tailWord_750674, baseEnd_750674] using wordTrace_append hprefix tailTrace_750674
  have hstable : (prefixWord ++ tailWord_750674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750674).length < 2 ^ (prefixWord ++ tailWord_750674).sum := by decide
  have hdescent : baseEnd_750674 < baseStart_750674 := by decide
  rcases family_descends (prefixWord ++ tailWord_750674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750792 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 5]
def baseStart_750792 : Nat := 118140960795 + 750792 * 2 ^ 59
def prefixEnd_750792 : Nat := 4983230072969 + 3 ^ 40 * 750792 * 2
def baseEnd_750792 : Nat := 171340963355791891798745

theorem tailTrace_750792 : CollatzResearch.WordTrace tailWord_750792 prefixEnd_750792 171340963355791891798745 := by
  unfold tailWord_750792
  simp only [CollatzResearch.WordTrace]
  refine ⟨13691816948008141955095315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18255755930677522606793753 13691816948008141955095315)
  ·
    refine ⟨20537725422012212932642973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13691816948008141955095315 20537725422012212932642973)
    ·
      refine ⟨7701647033254579849741115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20537725422012212932642973 7701647033254579849741115)
      ·
        refine ⟨11552470549881869774611673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7701647033254579849741115 11552470549881869774611673)
        ·
          refine ⟨8664352912411402330958755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11552470549881869774611673 8664352912411402330958755)
          ·
            refine ⟨12996529368617103496438133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8664352912411402330958755 12996529368617103496438133)
            ·
              refine ⟨1218424628307853452791075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12996529368617103496438133 1218424628307853452791075)
              ·
                refine ⟨1827636942461780179186613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218424628307853452791075 1827636942461780179186613)
                ·
                  refine ⟨171340963355791891798745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1827636942461780179186613 171340963355791891798745)
                  ·
                    rfl

theorem cell21_750792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_750792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750792 prefixEnd_750792 := by exact prefixLift 750792
  have htrace : WordTrace (prefixWord ++ tailWord_750792) baseStart_750792 baseEnd_750792 := by
    simpa [prefixWord, tailWord_750792, baseEnd_750792] using wordTrace_append hprefix tailTrace_750792
  have hstable : (prefixWord ++ tailWord_750792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750792).length < 2 ^ (prefixWord ++ tailWord_750792).sum := by decide
  have hdescent : baseEnd_750792 < baseStart_750792 := by decide
  rcases family_descends (prefixWord ++ tailWord_750792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750798 : List Nat := [4, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_750798 : Nat := 118140960795 + 750798 * 2 ^ 59
def prefixEnd_750798 : Nat := 4983230072969 + 3 ^ 40 * 750798 * 2
def baseEnd_750798 : Nat := 171342332637537214698733

theorem tailTrace_750798 : CollatzResearch.WordTrace tailWord_750798 prefixEnd_750798 171342332637537214698733 := by
  unfold tailWord_750798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3422981591749318366863631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18255901822663031289939365 3422981591749318366863631)
  ·
    refine ⟨5134472387623977550295447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3422981591749318366863631 5134472387623977550295447)
    ·
      refine ⟨7701708581435966325443171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5134472387623977550295447 7701708581435966325443171)
      ·
        refine ⟨11552562872153949488164757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7701708581435966325443171 11552562872153949488164757)
        ·
          refine ⟨541526384632216382257723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11552562872153949488164757 541526384632216382257723)
          ·
            refine ⟨812289576948324573386585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541526384632216382257723 812289576948324573386585)
            ·
              refine ⟨609217182711243430039939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812289576948324573386585 609217182711243430039939)
              ·
                refine ⟨913825774066865145059909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609217182711243430039939 913825774066865145059909)
                ·
                  refine ⟨171342332637537214698733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 913825774066865145059909 171342332637537214698733)
                  ·
                    rfl

theorem cell21_750798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_750798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750798 prefixEnd_750798 := by exact prefixLift 750798
  have htrace : WordTrace (prefixWord ++ tailWord_750798) baseStart_750798 baseEnd_750798 := by
    simpa [prefixWord, tailWord_750798, baseEnd_750798] using wordTrace_append hprefix tailTrace_750798
  have hstable : (prefixWord ++ tailWord_750798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750798).length < 2 ^ (prefixWord ++ tailWord_750798).sum := by decide
  have hdescent : baseEnd_750798 < baseStart_750798 := by decide
  rcases family_descends (prefixWord ++ tailWord_750798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750885 : List Nat := [1, 3, 1, 2, 4, 1, 1, 5, 3]
def baseStart_750885 : Nat := 118140960795 + 750885 * 2 ^ 59
def prefixEnd_750885 : Nat := 4983230072969 + 3 ^ 40 * 750885 * 2
def baseEnd_750885 : Nat := 171362187222844396748555

theorem tailTrace_750885 : CollatzResearch.WordTrace tailWord_750885 prefixEnd_750885 171362187222844396748555 := by
  unfold tailWord_750885
  simp only [CollatzResearch.WordTrace]
  refine ⟨27387025884679360793326109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18258017256452907195550739 27387025884679360793326109)
  ·
    refine ⟨10270134706754760297497291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27387025884679360793326109 10270134706754760297497291)
    ·
      refine ⟨15405202060132140446245937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10270134706754760297497291 15405202060132140446245937)
      ·
        refine ⟨11553901545099105334684453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15405202060132140446245937 11553901545099105334684453)
        ·
          refine ⟨2166356539706082250253335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11553901545099105334684453 2166356539706082250253335)
          ·
            refine ⟨3249534809559123375380003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166356539706082250253335 3249534809559123375380003)
            ·
              refine ⟨4874302214338685063070005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249534809559123375380003 4874302214338685063070005)
              ·
                refine ⟨456965832594251724662813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4874302214338685063070005 456965832594251724662813)
                ·
                  refine ⟨171362187222844396748555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456965832594251724662813 171362187222844396748555)
                  ·
                    rfl

theorem cell21_750885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_750885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750885 prefixEnd_750885 := by exact prefixLift 750885
  have htrace : WordTrace (prefixWord ++ tailWord_750885) baseStart_750885 baseEnd_750885 := by
    simpa [prefixWord, tailWord_750885, baseEnd_750885] using wordTrace_append hprefix tailTrace_750885
  have hstable : (prefixWord ++ tailWord_750885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750885).length < 2 ^ (prefixWord ++ tailWord_750885).sum := by decide
  have hdescent : baseEnd_750885 < baseStart_750885 := by decide
  rcases family_descends (prefixWord ++ tailWord_750885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750896 : List Nat := [2, 1, 1, 1, 2, 2, 12]
def baseStart_750896 : Nat := 118140960795 + 750896 * 2 ^ 59
def prefixEnd_750896 : Nat := 4983230072969 + 3 ^ 40 * 750896 * 2
def baseEnd_750896 : Nat := 19040521952523424673911

theorem tailTrace_750896 : CollatzResearch.WordTrace tailWord_750896 prefixEnd_750896 19040521952523424673911 := by
  unfold tailWord_750896
  simp only [CollatzResearch.WordTrace]
  refine ⟨13693713543819754835988271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18258284725093006447984361 13693713543819754835988271)
  ·
    refine ⟨20540570315729632253982407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13693713543819754835988271 20540570315729632253982407)
    ·
      refine ⟨30810855473594448380973611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20540570315729632253982407 30810855473594448380973611)
      ·
        refine ⟨46216283210391672571460417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30810855473594448380973611 46216283210391672571460417)
        ·
          refine ⟨34662212407793754428595313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46216283210391672571460417 34662212407793754428595313)
          ·
            refine ⟨25996659305845315821446485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34662212407793754428595313 25996659305845315821446485)
            ·
              refine ⟨19040521952523424673911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 25996659305845315821446485 19040521952523424673911)
              ·
                rfl

theorem cell21_750896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 12].length) (baseStart_750896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750896 prefixEnd_750896 := by exact prefixLift 750896
  have htrace : WordTrace (prefixWord ++ tailWord_750896) baseStart_750896 baseEnd_750896 := by
    simpa [prefixWord, tailWord_750896, baseEnd_750896] using wordTrace_append hprefix tailTrace_750896
  have hstable : (prefixWord ++ tailWord_750896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750896).length < 2 ^ (prefixWord ++ tailWord_750896).sum := by decide
  have hdescent : baseEnd_750896 < baseStart_750896 := by decide
  rcases family_descends (prefixWord ++ tailWord_750896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750899 : List Nat := [1, 1, 1, 2, 5, 2, 3, 2, 4]
def baseStart_750899 : Nat := 118140960795 + 750899 * 2 ^ 59
def prefixEnd_750899 : Nat := 4983230072969 + 3 ^ 40 * 750899 * 2
def baseEnd_750899 : Nat := 171365382213583483515193

theorem tailTrace_750899 : CollatzResearch.WordTrace tailWord_750899 prefixEnd_750899 171365382213583483515193 := by
  unfold tailWord_750899
  simp only [CollatzResearch.WordTrace]
  refine ⟨27387536506628641184335751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18258357671085760789557167 27387536506628641184335751)
  ·
    refine ⟨41081304759942961776503627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27387536506628641184335751 41081304759942961776503627)
    ·
      refine ⟨61621957139914442664755441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41081304759942961776503627 61621957139914442664755441)
      ·
        refine ⟨46216467854935831998566581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61621957139914442664755441 46216467854935831998566581)
        ·
          refine ⟨4332793861400234249865617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46216467854935831998566581 4332793861400234249865617)
          ·
            refine ⟨3249595396050175687399213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4332793861400234249865617 3249595396050175687399213)
            ·
              refine ⟨1218598273518815882774705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3249595396050175687399213 1218598273518815882774705)
              ·
                refine ⟨913948705139111912081029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218598273518815882774705 913948705139111912081029)
                ·
                  refine ⟨171365382213583483515193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 913948705139111912081029 171365382213583483515193)
                  ·
                    rfl

theorem cell21_750899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 4].length) (baseStart_750899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750899 prefixEnd_750899 := by exact prefixLift 750899
  have htrace : WordTrace (prefixWord ++ tailWord_750899) baseStart_750899 baseEnd_750899 := by
    simpa [prefixWord, tailWord_750899, baseEnd_750899] using wordTrace_append hprefix tailTrace_750899
  have hstable : (prefixWord ++ tailWord_750899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750899).length < 2 ^ (prefixWord ++ tailWord_750899).sum := by decide
  have hdescent : baseEnd_750899 < baseStart_750899 := by decide
  rcases family_descends (prefixWord ++ tailWord_750899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751006 : List Nat := [4, 3, 1, 2, 2, 9]
def baseStart_751006 : Nat := 118140960795 + 751006 * 2 ^ 59
def prefixEnd_751006 : Nat := 4983230072969 + 3 ^ 40 * 751006 * 2
def baseEnd_751006 : Nat := 6347770410050928712283

theorem tailTrace_751006 : CollatzResearch.WordTrace tailWord_751006 prefixEnd_751006 6347770410050928712283 := by
  unfold tailWord_751006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3423929889655124807310109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18260959411493998972320581 3423929889655124807310109)
  ·
    refine ⟨1283973708620671802741291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3423929889655124807310109 1283973708620671802741291)
    ·
      refine ⟨1925960562931007704111937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1283973708620671802741291 1925960562931007704111937)
      ·
        refine ⟨1444470422198255778083953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1925960562931007704111937 1444470422198255778083953)
        ·
          refine ⟨1083352816648691833562965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1444470422198255778083953 1083352816648691833562965)
          ·
            refine ⟨6347770410050928712283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1083352816648691833562965 6347770410050928712283)
            ·
              rfl

theorem cell21_751006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 9].length) (baseStart_751006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751006 prefixEnd_751006 := by exact prefixLift 751006
  have htrace : WordTrace (prefixWord ++ tailWord_751006) baseStart_751006 baseEnd_751006 := by
    simpa [prefixWord, tailWord_751006, baseEnd_751006] using wordTrace_append hprefix tailTrace_751006
  have hstable : (prefixWord ++ tailWord_751006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751006).length < 2 ^ (prefixWord ++ tailWord_751006).sum := by decide
  have hdescent : baseEnd_751006 < baseStart_751006 := by decide
  rcases family_descends (prefixWord ++ tailWord_751006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751085 : List Nat := [1, 5, 1, 3, 2, 1, 3, 1, 4]
def baseStart_751085 : Nat := 118140960795 + 751085 * 2 ^ 59
def prefixEnd_751085 : Nat := 4983230072969 + 3 ^ 40 * 751085 * 2
def baseEnd_751085 : Nat := 171407829947688493414813

theorem tailTrace_751085 : CollatzResearch.WordTrace tailWord_751085 prefixEnd_751085 171407829947688493414813 := by
  unfold tailWord_751085
  simp only [CollatzResearch.WordTrace]
  refine ⟨27394320483954794950606709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18262880322636529967071139 27394320483954794950606709)
  ·
    refine ⟨2568217545370762026619379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27394320483954794950606709 2568217545370762026619379)
    ·
      refine ⟨3852326318056143039929069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2568217545370762026619379 3852326318056143039929069)
      ·
        refine ⟨1444622369271053639973401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3852326318056143039929069 1444622369271053639973401)
        ·
          refine ⟨1083466776953290229980051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1444622369271053639973401 1083466776953290229980051)
          ·
            refine ⟨1625200165429935344970077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083466776953290229980051 1625200165429935344970077)
            ·
              refine ⟨609450062036225754363779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1625200165429935344970077 609450062036225754363779)
              ·
                refine ⟨914175093054338631545669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609450062036225754363779 914175093054338631545669)
                ·
                  refine ⟨171407829947688493414813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 914175093054338631545669 171407829947688493414813)
                  ·
                    rfl

theorem cell21_751085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_751085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751085 prefixEnd_751085 := by exact prefixLift 751085
  have htrace : WordTrace (prefixWord ++ tailWord_751085) baseStart_751085 baseEnd_751085 := by
    simpa [prefixWord, tailWord_751085, baseEnd_751085] using wordTrace_append hprefix tailTrace_751085
  have hstable : (prefixWord ++ tailWord_751085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751085).length < 2 ^ (prefixWord ++ tailWord_751085).sum := by decide
  have hdescent : baseEnd_751085 < baseStart_751085 := by decide
  rcases family_descends (prefixWord ++ tailWord_751085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751144 : List Nat := [2, 1, 5, 2, 2, 1, 1, 3, 4]
def baseStart_751144 : Nat := 118140960795 + 751144 * 2 ^ 59
def prefixEnd_751144 : Nat := 4983230072969 + 3 ^ 40 * 751144 * 2
def baseEnd_751144 : Nat := 171421294551517501931359

theorem tailTrace_751144 : CollatzResearch.WordTrace tailWord_751144 prefixEnd_751144 171421294551517501931359 := by
  unfold tailWord_751144
  simp only [CollatzResearch.WordTrace]
  refine ⟨13698236195370524013502243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18264314927160698684669657 13698236195370524013502243)
  ·
    refine ⟨20547354293055786020253365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13698236195370524013502243 20547354293055786020253365)
    ·
      refine ⟨1926314464973979939398753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20547354293055786020253365 1926314464973979939398753)
      ·
        refine ⟨1444735848730484954549065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1926314464973979939398753 1444735848730484954549065)
        ·
          refine ⟨1083551886547863715911799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1444735848730484954549065 1083551886547863715911799)
          ·
            refine ⟨1625327829821795573867699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083551886547863715911799 1625327829821795573867699)
            ·
              refine ⟨2437991744732693360801549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625327829821795573867699 2437991744732693360801549)
              ·
                refine ⟨914246904274760010300581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2437991744732693360801549 914246904274760010300581)
                ·
                  refine ⟨171421294551517501931359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 914246904274760010300581 171421294551517501931359)
                  ·
                    rfl

theorem cell21_751144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_751144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751144 prefixEnd_751144 := by exact prefixLift 751144
  have htrace : WordTrace (prefixWord ++ tailWord_751144) baseStart_751144 baseEnd_751144 := by
    simpa [prefixWord, tailWord_751144, baseEnd_751144] using wordTrace_append hprefix tailTrace_751144
  have hstable : (prefixWord ++ tailWord_751144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751144).length < 2 ^ (prefixWord ++ tailWord_751144).sum := by decide
  have hdescent : baseEnd_751144 < baseStart_751144 := by decide
  rcases family_descends (prefixWord ++ tailWord_751144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751358 : List Nat := [4, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_751358 : Nat := 118140960795 + 751358 * 2 ^ 59
def prefixEnd_751358 : Nat := 4983230072969 + 3 ^ 40 * 751358 * 2
def baseEnd_751358 : Nat := 171470132267100685364255

theorem tailTrace_751358 : CollatzResearch.WordTrace tailWord_751358 prefixEnd_751358 171470132267100685364255 := by
  unfold tailWord_751358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3425534701495720321911841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18269518407977175050196485 3425534701495720321911841)
  ·
    refine ⟨2569151026121790241433881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3425534701495720321911841 2569151026121790241433881)
    ·
      refine ⟨1926863269591342681075411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2569151026121790241433881 1926863269591342681075411)
      ·
        refine ⟨2890294904387014021613117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1926863269591342681075411 2890294904387014021613117)
        ·
          refine ⟨1083860589145130258104919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2890294904387014021613117 1083860589145130258104919)
          ·
            refine ⟨1625790883717695387157379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083860589145130258104919 1625790883717695387157379)
            ·
              refine ⟨2438686325576543080736069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625790883717695387157379 2438686325576543080736069)
              ·
                refine ⟨457253686045601827638013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2438686325576543080736069 457253686045601827638013)
                ·
                  refine ⟨171470132267100685364255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457253686045601827638013 171470132267100685364255)
                  ·
                    rfl

theorem cell21_751358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_751358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751358 prefixEnd_751358 := by exact prefixLift 751358
  have htrace : WordTrace (prefixWord ++ tailWord_751358) baseStart_751358 baseEnd_751358 := by
    simpa [prefixWord, tailWord_751358, baseEnd_751358] using wordTrace_append hprefix tailTrace_751358
  have hstable : (prefixWord ++ tailWord_751358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751358).length < 2 ^ (prefixWord ++ tailWord_751358).sum := by decide
  have hdescent : baseEnd_751358 < baseStart_751358 := by decide
  rcases family_descends (prefixWord ++ tailWord_751358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751383 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 7]
def baseStart_751383 : Nat := 118140960795 + 751383 * 2 ^ 59
def prefixEnd_751383 : Nat := 4983230072969 + 3 ^ 40 * 751383 * 2
def baseEnd_751383 : Nat := 171475837607706197447537

theorem tailTrace_751383 : CollatzResearch.WordTrace tailWord_751383 prefixEnd_751383 171475837607706197447537 := by
  unfold tailWord_751383
  simp only [CollatzResearch.WordTrace]
  refine ⟨27405189436875191844954803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18270126291250127896636535 27405189436875191844954803)
  ·
    refine ⟨41107784155312787767432205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27405189436875191844954803 41107784155312787767432205)
    ·
      refine ⟨15415419058242295412787077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41107784155312787767432205 15415419058242295412787077)
      ·
        refine ⟨2890391073420430389897577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15415419058242295412787077 2890391073420430389897577)
        ·
          refine ⟨2167793305065322792423183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2890391073420430389897577 2167793305065322792423183)
          ·
            refine ⟨3251689957597984188634775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2167793305065322792423183 3251689957597984188634775)
            ·
              refine ⟨4877534936396976282952163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3251689957597984188634775 4877534936396976282952163)
              ·
                refine ⟨7316302404595464424428245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4877534936396976282952163 7316302404595464424428245)
                ·
                  refine ⟨171475837607706197447537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7316302404595464424428245 171475837607706197447537)
                  ·
                    rfl

theorem cell21_751383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 7].length) (baseStart_751383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751383 prefixEnd_751383 := by exact prefixLift 751383
  have htrace : WordTrace (prefixWord ++ tailWord_751383) baseStart_751383 baseEnd_751383 := by
    simpa [prefixWord, tailWord_751383, baseEnd_751383] using wordTrace_append hprefix tailTrace_751383
  have hstable : (prefixWord ++ tailWord_751383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751383).length < 2 ^ (prefixWord ++ tailWord_751383).sum := by decide
  have hdescent : baseEnd_751383 < baseStart_751383 := by decide
  rcases family_descends (prefixWord ++ tailWord_751383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751417 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 5]
def baseStart_751417 : Nat := 118140960795 + 751417 * 2 ^ 59
def prefixEnd_751417 : Nat := 4983230072969 + 3 ^ 40 * 751417 * 2
def baseEnd_751417 : Nat := 171483596870929693880801

theorem tailTrace_751417 : CollatzResearch.WordTrace tailWord_751417 prefixEnd_751417 171483596870929693880801 := by
  unfold tailWord_751417
  simp only [CollatzResearch.WordTrace]
  refine ⟨27406429518752015651692505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18270953012501343767795003 27406429518752015651692505)
  ·
    refine ⟨20554822139064011738769379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27406429518752015651692505 20554822139064011738769379)
    ·
      refine ⟨30832233208596017608154069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20554822139064011738769379 30832233208596017608154069)
      ·
        refine ⟨722630465826469162691111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 30832233208596017608154069 722630465826469162691111)
        ·
          refine ⟨1083945698739703744036667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722630465826469162691111 1083945698739703744036667)
          ·
            refine ⟨1625918548109555616055001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083945698739703744036667 1625918548109555616055001)
            ·
              refine ⟨1219438911082166712041251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1625918548109555616055001 1219438911082166712041251)
              ·
                refine ⟨1829158366623250068061877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1219438911082166712041251 1829158366623250068061877)
                ·
                  refine ⟨171483596870929693880801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1829158366623250068061877 171483596870929693880801)
                  ·
                    rfl

theorem cell21_751417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_751417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751417 prefixEnd_751417 := by exact prefixLift 751417
  have htrace : WordTrace (prefixWord ++ tailWord_751417) baseStart_751417 baseEnd_751417 := by
    simpa [prefixWord, tailWord_751417, baseEnd_751417] using wordTrace_append hprefix tailTrace_751417
  have hstable : (prefixWord ++ tailWord_751417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751417).length < 2 ^ (prefixWord ++ tailWord_751417).sum := by decide
  have hdescent : baseEnd_751417 < baseStart_751417 := by decide
  rcases family_descends (prefixWord ++ tailWord_751417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751445 : List Nat := [1, 3, 2, 2, 2, 2, 4, 5]
def baseStart_751445 : Nat := 118140960795 + 751445 * 2 ^ 59
def prefixEnd_751445 : Nat := 4983230072969 + 3 ^ 40 * 751445 * 2
def baseEnd_751445 : Nat := 57163328950802622471359

theorem tailTrace_751445 : CollatzResearch.WordTrace tailWord_751445 prefixEnd_751445 57163328950802622471359 := by
  unfold tailWord_751445
  simp only [CollatzResearch.WordTrace]
  refine ⟨27407450762650576433711789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18271633841767050955807859 27407450762650576433711789)
  ·
    refine ⟨10277794035993966162641921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27407450762650576433711789 10277794035993966162641921)
    ·
      refine ⟨7708345526995474621981441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10277794035993966162641921 7708345526995474621981441)
      ·
        refine ⟨5781259145246605966486081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7708345526995474621981441 5781259145246605966486081)
        ·
          refine ⟨4335944358934954474864561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5781259145246605966486081 4335944358934954474864561)
          ·
            refine ⟨3251958269201215856148421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4335944358934954474864561 3251958269201215856148421)
            ·
              refine ⟨609742175475227973027829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3251958269201215856148421 609742175475227973027829)
              ·
                refine ⟨57163328950802622471359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 609742175475227973027829 57163328950802622471359)
                ·
                  rfl

theorem cell21_751445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 5].length) (baseStart_751445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751445 prefixEnd_751445 := by exact prefixLift 751445
  have htrace : WordTrace (prefixWord ++ tailWord_751445) baseStart_751445 baseEnd_751445 := by
    simpa [prefixWord, tailWord_751445, baseEnd_751445] using wordTrace_append hprefix tailTrace_751445
  have hstable : (prefixWord ++ tailWord_751445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751445).length < 2 ^ (prefixWord ++ tailWord_751445).sum := by decide
  have hdescent : baseEnd_751445 < baseStart_751445 := by decide
  rcases family_descends (prefixWord ++ tailWord_751445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751473 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 6]
def baseStart_751473 : Nat := 118140960795 + 751473 * 2 ^ 59
def prefixEnd_751473 : Nat := 4983230072969 + 3 ^ 40 * 751473 * 2
def baseEnd_751473 : Nat := 171496376833886040947353

theorem tailTrace_751473 : CollatzResearch.WordTrace tailWord_751473 prefixEnd_751473 171496376833886040947353 := by
  unfold tailWord_751473
  simp only [CollatzResearch.WordTrace]
  refine ⟨27408472006549137215731073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18272314671032758143820715 27408472006549137215731073)
  ·
    refine ⟨20556354004911852911798305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27408472006549137215731073 20556354004911852911798305)
    ·
      refine ⟨15417265503683889683848729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20556354004911852911798305 15417265503683889683848729)
      ·
        refine ⟨11562949127762917262886547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15417265503683889683848729 11562949127762917262886547)
        ·
          refine ⟨17344423691644375894329821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11562949127762917262886547 17344423691644375894329821)
          ·
            refine ⟨6504158884366640960373683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17344423691644375894329821 6504158884366640960373683)
            ·
              refine ⟨9756238326549961440560525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6504158884366640960373683 9756238326549961440560525)
              ·
                refine ⟨3658589372456235540210197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9756238326549961440560525 3658589372456235540210197)
                ·
                  refine ⟨171496376833886040947353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3658589372456235540210197 171496376833886040947353)
                  ·
                    rfl

theorem cell21_751473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_751473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751473 prefixEnd_751473 := by exact prefixLift 751473
  have htrace : WordTrace (prefixWord ++ tailWord_751473) baseStart_751473 baseEnd_751473 := by
    simpa [prefixWord, tailWord_751473, baseEnd_751473] using wordTrace_append hprefix tailTrace_751473
  have hstable : (prefixWord ++ tailWord_751473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751473).length < 2 ^ (prefixWord ++ tailWord_751473).sum := by decide
  have hdescent : baseEnd_751473 < baseStart_751473 := by decide
  rcases family_descends (prefixWord ++ tailWord_751473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751521 : List Nat := [1, 2, 3, 4, 3, 8]
def baseStart_751521 : Nat := 118140960795 + 751521 * 2 ^ 59
def prefixEnd_751521 : Nat := 4983230072969 + 3 ^ 40 * 751521 * 2
def baseEnd_751521 : Nat := 6352123373624023116565

theorem tailTrace_751521 : CollatzResearch.WordTrace tailWord_751521 prefixEnd_751521 6352123373624023116565 := by
  unfold tailWord_751521
  simp only [CollatzResearch.WordTrace]
  refine ⟨27410222710375241413478417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18273481806916827608985611 27410222710375241413478417)
  ·
    refine ⟨20557667032781431060108813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27410222710375241413478417 20557667032781431060108813)
    ·
      refine ⟨7709125137293036647540805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20557667032781431060108813 7709125137293036647540805)
      ·
        refine ⟨1445460963242444371413901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7709125137293036647540805 1445460963242444371413901)
        ·
          refine ⟨542047861215916639280213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1445460963242444371413901 542047861215916639280213)
          ·
            refine ⟨6352123373624023116565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 542047861215916639280213 6352123373624023116565)
            ·
              rfl

theorem cell21_751521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 8].length) (baseStart_751521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751521 prefixEnd_751521 := by exact prefixLift 751521
  have htrace : WordTrace (prefixWord ++ tailWord_751521) baseStart_751521 baseEnd_751521 := by
    simpa [prefixWord, tailWord_751521, baseEnd_751521] using wordTrace_append hprefix tailTrace_751521
  have hstable : (prefixWord ++ tailWord_751521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751521).length < 2 ^ (prefixWord ++ tailWord_751521).sum := by decide
  have hdescent : baseEnd_751521 < baseStart_751521 := by decide
  rcases family_descends (prefixWord ++ tailWord_751521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751583 : List Nat := [1, 1, 2, 3, 4, 3, 1, 2, 4]
def baseStart_751583 : Nat := 118140960795 + 751583 * 2 ^ 59
def prefixEnd_751583 : Nat := 4983230072969 + 3 ^ 40 * 751583 * 2
def baseEnd_751583 : Nat := 171521480332550294113795

theorem tailTrace_751583 : CollatzResearch.WordTrace tailWord_751583 prefixEnd_751583 171521480332550294113795 := by
  unfold tailWord_751583
  simp only [CollatzResearch.WordTrace]
  refine ⟨27412484036150626002235403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18274989357433750668156935 27412484036150626002235403)
  ·
    refine ⟨41118726054225939003353105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27412484036150626002235403 41118726054225939003353105)
    ·
      refine ⟨30839044540669454252514829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41118726054225939003353105 30839044540669454252514829)
      ·
        refine ⟨11564641702751045344693061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30839044540669454252514829 11564641702751045344693061)
        ·
          refine ⟨2168370319265821002129949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11564641702751045344693061 2168370319265821002129949)
          ·
            refine ⟨813138869724682875798731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2168370319265821002129949 813138869724682875798731)
            ·
              refine ⟨1219708304587024313698097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813138869724682875798731 1219708304587024313698097)
              ·
                refine ⟨914781228440268235273573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1219708304587024313698097 914781228440268235273573)
                ·
                  refine ⟨171521480332550294113795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 914781228440268235273573 171521480332550294113795)
                  ·
                    rfl

theorem cell21_751583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 4].length) (baseStart_751583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751583 prefixEnd_751583 := by exact prefixLift 751583
  have htrace : WordTrace (prefixWord ++ tailWord_751583) baseStart_751583 baseEnd_751583 := by
    simpa [prefixWord, tailWord_751583, baseEnd_751583] using wordTrace_append hprefix tailTrace_751583
  have hstable : (prefixWord ++ tailWord_751583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751583).length < 2 ^ (prefixWord ++ tailWord_751583).sum := by decide
  have hdescent : baseEnd_751583 < baseStart_751583 := by decide
  rcases family_descends (prefixWord ++ tailWord_751583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751614 : List Nat := [4, 2, 2, 2, 1, 1, 4, 5]
def baseStart_751614 : Nat := 118140960795 + 751614 * 2 ^ 59
def prefixEnd_751614 : Nat := 4983230072969 + 3 ^ 40 * 751614 * 2
def baseEnd_751614 : Nat := 57176184984967043032355

theorem tailTrace_751614 : CollatzResearch.WordTrace tailWord_751614 prefixEnd_751614 57176184984967043032355 := by
  unfold tailWord_751614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426701837379789787076737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18275743132692212197742597 3426701837379789787076737)
  ·
    refine ⟨2570026378034842340307553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3426701837379789787076737 2570026378034842340307553)
    ·
      refine ⟨1927519783526131755230665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2570026378034842340307553 1927519783526131755230665)
      ·
        refine ⟨1445639837644598816422999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1927519783526131755230665 1445639837644598816422999)
        ·
          refine ⟨2168459756466898224634499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445639837644598816422999 2168459756466898224634499)
          ·
            refine ⟨3252689634700347336951749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168459756466898224634499 3252689634700347336951749)
            ·
              refine ⟨609879306506315125678453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3252689634700347336951749 609879306506315125678453)
              ·
                refine ⟨57176184984967043032355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 609879306506315125678453 57176184984967043032355)
                ·
                  rfl

theorem cell21_751614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_751614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751614 prefixEnd_751614 := by exact prefixLift 751614
  have htrace : WordTrace (prefixWord ++ tailWord_751614) baseStart_751614 baseEnd_751614 := by
    simpa [prefixWord, tailWord_751614, baseEnd_751614] using wordTrace_append hprefix tailTrace_751614
  have hstable : (prefixWord ++ tailWord_751614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751614).length < 2 ^ (prefixWord ++ tailWord_751614).sum := by decide
  have hdescent : baseEnd_751614 < baseStart_751614 := by decide
  rcases family_descends (prefixWord ++ tailWord_751614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751704 : List Nat := [2, 1, 2, 2, 1, 5, 1, 4, 3]
def baseStart_751704 : Nat := 118140960795 + 751704 * 2 ^ 59
def prefixEnd_751704 : Nat := 4983230072969 + 3 ^ 40 * 751704 * 2
def baseEnd_751704 : Nat := 171549094181080972596881

theorem tailTrace_751704 : CollatzResearch.WordTrace tailWord_751704 prefixEnd_751704 171549094181080972596881 := by
  unfold tailWord_751704
  simp only [CollatzResearch.WordTrace]
  refine ⟨13708448634356131833695083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18277931512474842444926777 13708448634356131833695083)
  ·
    refine ⟨20562672951534197750542625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13708448634356131833695083 20562672951534197750542625)
    ·
      refine ⟨15422004713650648312906969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20562672951534197750542625 15422004713650648312906969)
      ·
        refine ⟨11566503535237986234680227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15422004713650648312906969 11566503535237986234680227)
        ·
          refine ⟨17349755302856979352020341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11566503535237986234680227 17349755302856979352020341)
          ·
            refine ⟨1626539559642841814251907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17349755302856979352020341 1626539559642841814251907)
            ·
              refine ⟨2439809339464262721377861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626539559642841814251907 2439809339464262721377861)
              ·
                refine ⟨457464251149549260258349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2439809339464262721377861 457464251149549260258349)
                ·
                  refine ⟨171549094181080972596881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457464251149549260258349 171549094181080972596881)
                  ·
                    rfl

theorem cell21_751704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 3].length) (baseStart_751704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751704 prefixEnd_751704 := by exact prefixLift 751704
  have htrace : WordTrace (prefixWord ++ tailWord_751704) baseStart_751704 baseEnd_751704 := by
    simpa [prefixWord, tailWord_751704, baseEnd_751704] using wordTrace_append hprefix tailTrace_751704
  have hstable : (prefixWord ++ tailWord_751704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751704).length < 2 ^ (prefixWord ++ tailWord_751704).sum := by decide
  have hdescent : baseEnd_751704 < baseStart_751704 := by decide
  rcases family_descends (prefixWord ++ tailWord_751704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751783 : List Nat := [1, 1, 6, 2, 3, 1, 2, 5]
def baseStart_751783 : Nat := 118140960795 + 751783 * 2 ^ 59
def prefixEnd_751783 : Nat := 4983230072969 + 3 ^ 40 * 751783 * 2
def baseEnd_751783 : Nat := 57189041019131463593351

theorem tailTrace_751783 : CollatzResearch.WordTrace tailWord_751783 prefixEnd_751783 57189041019131463593351 := by
  unfold tailWord_751783
  simp only [CollatzResearch.WordTrace]
  refine ⟨27419778635426060159516003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18279852423617373439677335 27419778635426060159516003)
  ·
    refine ⟨41129667953139090239274005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27419778635426060159516003 41129667953139090239274005)
    ·
      refine ⟨1927953185303394854965969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41129667953139090239274005 1927953185303394854965969)
      ·
        refine ⟨1445964888977546141224477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1927953185303394854965969 1445964888977546141224477)
        ·
          refine ⟨542236833366579802959179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1445964888977546141224477 542236833366579802959179)
          ·
            refine ⟨813355250049869704438769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542236833366579802959179 813355250049869704438769)
            ·
              refine ⟨610016437537402278329077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813355250049869704438769 610016437537402278329077)
              ·
                refine ⟨57189041019131463593351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 610016437537402278329077 57189041019131463593351)
                ·
                  rfl

theorem cell21_751783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 5].length) (baseStart_751783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751783 prefixEnd_751783 := by exact prefixLift 751783
  have htrace : WordTrace (prefixWord ++ tailWord_751783) baseStart_751783 baseEnd_751783 := by
    simpa [prefixWord, tailWord_751783, baseEnd_751783] using wordTrace_append hprefix tailTrace_751783
  have hstable : (prefixWord ++ tailWord_751783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751783).length < 2 ^ (prefixWord ++ tailWord_751783).sum := by decide
  have hdescent : baseEnd_751783 < baseStart_751783 := by decide
  rcases family_descends (prefixWord ++ tailWord_751783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751808 : List Nat := [2, 1, 1, 2, 5, 3, 7]
def baseStart_751808 : Nat := 118140960795 + 751808 * 2 ^ 59
def prefixEnd_751808 : Nat := 4983230072969 + 3 ^ 40 * 751808 * 2
def baseEnd_751808 : Nat := 19063647599777766984815

theorem tailTrace_751808 : CollatzResearch.WordTrace tailWord_751808 prefixEnd_751808 19063647599777766984815 := by
  unfold tailWord_751808
  simp only [CollatzResearch.WordTrace]
  refine ⟨13710345230167744714588039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18280460306890326286117385 13710345230167744714588039)
  ·
    refine ⟨20565517845251617071882059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13710345230167744714588039 20565517845251617071882059)
    ·
      refine ⟨30848276767877425607823089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20565517845251617071882059 30848276767877425607823089)
      ·
        refine ⟨23136207575908069205867317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30848276767877425607823089 23136207575908069205867317)
        ·
          refine ⟨2169019460241381488050061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23136207575908069205867317 2169019460241381488050061)
          ·
            refine ⟨813382297590518058018773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2169019460241381488050061 813382297590518058018773)
            ·
              refine ⟨19063647599777766984815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 813382297590518058018773 19063647599777766984815)
              ·
                rfl

theorem cell21_751808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 7].length) (baseStart_751808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751808 prefixEnd_751808 := by exact prefixLift 751808
  have htrace : WordTrace (prefixWord ++ tailWord_751808) baseStart_751808 baseEnd_751808 := by
    simpa [prefixWord, tailWord_751808, baseEnd_751808] using wordTrace_append hprefix tailTrace_751808
  have hstable : (prefixWord ++ tailWord_751808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751808).length < 2 ^ (prefixWord ++ tailWord_751808).sum := by decide
  have hdescent : baseEnd_751808 < baseStart_751808 := by decide
  rcases family_descends (prefixWord ++ tailWord_751808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751943 : List Nat := [1, 1, 4, 1, 2, 2, 2, 8]
def baseStart_751943 : Nat := 118140960795 + 751943 * 2 ^ 59
def prefixEnd_751943 : Nat := 4983230072969 + 3 ^ 40 * 751943 * 2
def baseEnd_751943 : Nat := 57201212412423222704353

theorem tailTrace_751943 : CollatzResearch.WordTrace tailWord_751943 prefixEnd_751943 57201212412423222704353 := by
  unfold tailWord_751943
  simp only [CollatzResearch.WordTrace]
  refine ⟨27425614314846407485340483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18283742876564271656893655 27425614314846407485340483)
  ·
    refine ⟨41138421472269611228010725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27425614314846407485340483 41138421472269611228010725)
    ·
      refine ⟨7713454026050552105252011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41138421472269611228010725 7713454026050552105252011)
      ·
        refine ⟨11570181039075828157878017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7713454026050552105252011 11570181039075828157878017)
        ·
          refine ⟨8677635779306871118408513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11570181039075828157878017 8677635779306871118408513)
          ·
            refine ⟨6508226834480153338806385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8677635779306871118408513 6508226834480153338806385)
            ·
              refine ⟨4881170125860115004104789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6508226834480153338806385 4881170125860115004104789)
              ·
                refine ⟨57201212412423222704353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4881170125860115004104789 57201212412423222704353)
                ·
                  rfl

theorem cell21_751943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 8].length) (baseStart_751943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_751943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_751943 prefixEnd_751943 := by exact prefixLift 751943
  have htrace : WordTrace (prefixWord ++ tailWord_751943) baseStart_751943 baseEnd_751943 := by
    simpa [prefixWord, tailWord_751943, baseEnd_751943] using wordTrace_append hprefix tailTrace_751943
  have hstable : (prefixWord ++ tailWord_751943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751943).length < 2 ^ (prefixWord ++ tailWord_751943).sum := by decide
  have hdescent : baseEnd_751943 < baseStart_751943 := by decide
  rcases family_descends (prefixWord ++ tailWord_751943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752050 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_752050 : Nat := 118140960795 + 752050 * 2 ^ 59
def prefixEnd_752050 : Nat := 4983230072969 + 3 ^ 40 * 752050 * 2
def baseEnd_752050 : Nat := 171628056095061259829507

theorem tailTrace_752050 : CollatzResearch.WordTrace tailWord_752050 prefixEnd_752050 171628056095061259829507 := by
  unfold tailWord_752050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6857379231364691189871401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18286344616972509839657069 6857379231364691189871401)
  ·
    refine ⟨5143034423523518392403551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6857379231364691189871401 5143034423523518392403551)
    ·
      refine ⟨7714551635285277588605327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5143034423523518392403551 7714551635285277588605327)
      ·
        refine ⟨11571827452927916382907991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7714551635285277588605327 11571827452927916382907991)
        ·
          refine ⟨17357741179391874574361987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11571827452927916382907991 17357741179391874574361987)
          ·
            refine ⟨26036611769087811861542981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17357741179391874574361987 26036611769087811861542981)
            ·
              refine ⟨4881864706703964724039309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26036611769087811861542981 4881864706703964724039309)
              ·
                refine ⟨1830699265013986771514741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4881864706703964724039309 1830699265013986771514741)
                ·
                  refine ⟨171628056095061259829507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1830699265013986771514741 171628056095061259829507)
                  ·
                    rfl

theorem cell21_752050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_752050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752050 prefixEnd_752050 := by exact prefixLift 752050
  have htrace : WordTrace (prefixWord ++ tailWord_752050) baseStart_752050 baseEnd_752050 := by
    simpa [prefixWord, tailWord_752050, baseEnd_752050] using wordTrace_append hprefix tailTrace_752050
  have hstable : (prefixWord ++ tailWord_752050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752050).length < 2 ^ (prefixWord ++ tailWord_752050).sum := by decide
  have hdescent : baseEnd_752050 < baseStart_752050 := by decide
  rcases family_descends (prefixWord ++ tailWord_752050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752053 : List Nat := [1, 3, 3, 2, 3, 2, 1, 6]
def baseStart_752053 : Nat := 118140960795 + 752053 * 2 ^ 59
def prefixEnd_752053 : Nat := 4983230072969 + 3 ^ 40 * 752053 * 2
def baseEnd_752053 : Nat := 57209580245311307093167

theorem tailTrace_752053 : CollatzResearch.WordTrace tailWord_752053 prefixEnd_752053 57209580245311307093167 := by
  unfold tailWord_752053
  simp only [CollatzResearch.WordTrace]
  refine ⟨27429626344447896271844813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18286417562965264181229875 27429626344447896271844813)
  ·
    refine ⟨10286109879167961101941805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27429626344447896271844813 10286109879167961101941805)
    ·
      refine ⟨3857291204687985413228177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10286109879167961101941805 3857291204687985413228177)
      ·
        refine ⟨2892968403515989059921133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3857291204687985413228177 2892968403515989059921133)
        ·
          refine ⟨1084863151318495897470425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2892968403515989059921133 1084863151318495897470425)
          ·
            refine ⟨813647363488871923102819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1084863151318495897470425 813647363488871923102819)
            ·
              refine ⟨1220471045233307884654229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813647363488871923102819 1220471045233307884654229)
              ·
                refine ⟨57209580245311307093167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1220471045233307884654229 57209580245311307093167)
                ·
                  rfl

theorem cell21_752053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 6].length) (baseStart_752053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752053 prefixEnd_752053 := by exact prefixLift 752053
  have htrace : WordTrace (prefixWord ++ tailWord_752053) baseStart_752053 baseEnd_752053 := by
    simpa [prefixWord, tailWord_752053, baseEnd_752053] using wordTrace_append hprefix tailTrace_752053
  have hstable : (prefixWord ++ tailWord_752053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752053).length < 2 ^ (prefixWord ++ tailWord_752053).sum := by decide
  have hdescent : baseEnd_752053 < baseStart_752053 := by decide
  rcases family_descends (prefixWord ++ tailWord_752053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752064 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 8]
def baseStart_752064 : Nat := 118140960795 + 752064 * 2 ^ 59
def prefixEnd_752064 : Nat := 4983230072969 + 3 ^ 40 * 752064 * 2
def baseEnd_752064 : Nat := 171631251085800346596145

theorem tailTrace_752064 : CollatzResearch.WordTrace tailWord_752064 prefixEnd_752064 171631251085800346596145 := by
  unfold tailWord_752064
  simp only [CollatzResearch.WordTrace]
  refine ⟨13715013773704022575247623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18286685031605363433663497 13715013773704022575247623)
  ·
    refine ⟨20572520660556033862871435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13715013773704022575247623 20572520660556033862871435)
    ·
      refine ⟨30858780990834050794307153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20572520660556033862871435 30858780990834050794307153)
      ·
        refine ⟨23144085743125538095730365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30858780990834050794307153 23144085743125538095730365)
        ·
          refine ⟨8679032153672076785898887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23144085743125538095730365 8679032153672076785898887)
          ·
            refine ⟨13018548230508115178848331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8679032153672076785898887 13018548230508115178848331)
            ·
              refine ⟨19527822345762172768272497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13018548230508115178848331 19527822345762172768272497)
              ·
                refine ⟨14645866759321629576204373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19527822345762172768272497 14645866759321629576204373)
                ·
                  refine ⟨171631251085800346596145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14645866759321629576204373 171631251085800346596145)
                  ·
                    rfl

theorem cell21_752064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_752064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752064 prefixEnd_752064 := by exact prefixLift 752064
  have htrace : WordTrace (prefixWord ++ tailWord_752064) baseStart_752064 baseEnd_752064 := by
    simpa [prefixWord, tailWord_752064, baseEnd_752064] using wordTrace_append hprefix tailTrace_752064
  have hstable : (prefixWord ++ tailWord_752064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752064).length < 2 ^ (prefixWord ++ tailWord_752064).sum := by decide
  have hdescent : baseEnd_752064 < baseStart_752064 := by decide
  rcases family_descends (prefixWord ++ tailWord_752064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752084 : List Nat := [2, 4, 1, 2, 2, 1, 1, 5, 3]
def baseStart_752084 : Nat := 118140960795 + 752084 * 2 ^ 59
def prefixEnd_752084 : Nat := 4983230072969 + 3 ^ 40 * 752084 * 2
def baseEnd_752084 : Nat := 171635815358284756262771

theorem tailTrace_752084 : CollatzResearch.WordTrace tailWord_752084 prefixEnd_752084 171635815358284756262771 := by
  unfold tailWord_752084
  simp only [CollatzResearch.WordTrace]
  refine ⟨13715378503667794283111653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18287171338223725710815537 13715378503667794283111653)
  ·
    refine ⟨2571633469437711428083435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13715378503667794283111653 2571633469437711428083435)
    ·
      refine ⟨3857450204156567142125153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2571633469437711428083435 3857450204156567142125153)
      ·
        refine ⟨2893087653117425356593865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3857450204156567142125153 2893087653117425356593865)
        ·
          refine ⟨2169815739838069017445399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2893087653117425356593865 2169815739838069017445399)
          ·
            refine ⟨3254723609757103526168099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169815739838069017445399 3254723609757103526168099)
            ·
              refine ⟨4882085414635655289252149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254723609757103526168099 4882085414635655289252149)
              ·
                refine ⟨457695507622092683367389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4882085414635655289252149 457695507622092683367389)
                ·
                  refine ⟨171635815358284756262771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457695507622092683367389 171635815358284756262771)
                  ·
                    rfl

theorem cell21_752084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_752084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752084 prefixEnd_752084 := by exact prefixLift 752084
  have htrace : WordTrace (prefixWord ++ tailWord_752084) baseStart_752084 baseEnd_752084 := by
    simpa [prefixWord, tailWord_752084, baseEnd_752084] using wordTrace_append hprefix tailTrace_752084
  have hstable : (prefixWord ++ tailWord_752084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752084).length < 2 ^ (prefixWord ++ tailWord_752084).sum := by decide
  have hdescent : baseEnd_752084 < baseStart_752084 := by decide
  rcases family_descends (prefixWord ++ tailWord_752084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752095 : List Nat := [1, 1, 2, 3, 3, 3, 8]
def baseStart_752095 : Nat := 118140960795 + 752095 * 2 ^ 59
def prefixEnd_752095 : Nat := 4983230072969 + 3 ^ 40 * 752095 * 2
def baseEnd_752095 : Nat := 19070925078683464619935

theorem tailTrace_752095 : CollatzResearch.WordTrace tailWord_752095 prefixEnd_752095 19070925078683464619935 := by
  unfold tailWord_752095
  simp only [CollatzResearch.WordTrace]
  refine ⟨27431158210295737444873739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18287438806863824963249159 27431158210295737444873739)
  ·
    refine ⟨41146737315443606167310609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27431158210295737444873739 41146737315443606167310609)
    ·
      refine ⟨30860052986582704625482957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41146737315443606167310609 30860052986582704625482957)
      ·
        refine ⟨11572519869968514234556109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30860052986582704625482957 11572519869968514234556109)
        ·
          refine ⟨4339694951238192837958541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11572519869968514234556109 4339694951238192837958541)
          ·
            refine ⟨1627385606714322314234453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4339694951238192837958541 1627385606714322314234453)
            ·
              refine ⟨19070925078683464619935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1627385606714322314234453 19070925078683464619935)
              ·
                rfl

theorem cell21_752095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 8].length) (baseStart_752095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752095 prefixEnd_752095 := by exact prefixLift 752095
  have htrace : WordTrace (prefixWord ++ tailWord_752095) baseStart_752095 baseEnd_752095 := by
    simpa [prefixWord, tailWord_752095, baseEnd_752095] using wordTrace_append hprefix tailTrace_752095
  have hstable : (prefixWord ++ tailWord_752095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752095).length < 2 ^ (prefixWord ++ tailWord_752095).sum := by decide
  have hdescent : baseEnd_752095 < baseStart_752095 := by decide
  rcases family_descends (prefixWord ++ tailWord_752095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752129 : List Nat := [1, 2, 4, 1, 3, 3, 2, 5]
def baseStart_752129 : Nat := 118140960795 + 752129 * 2 ^ 59
def prefixEnd_752129 : Nat := 4983230072969 + 3 ^ 40 * 752129 * 2
def baseEnd_752129 : Nat := 57215361657124892670893

theorem tailTrace_752129 : CollatzResearch.WordTrace tailWord_752129 prefixEnd_752129 57215361657124892670893 := by
  unfold tailWord_752129
  simp only [CollatzResearch.WordTrace]
  refine ⟨27432398292172561251611441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18288265528115040834407627 27432398292172561251611441)
  ·
    refine ⟨20574298719129420938708581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27432398292172561251611441 20574298719129420938708581)
    ·
      refine ⟨3857681009836766426007859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20574298719129420938708581 3857681009836766426007859)
      ·
        refine ⟨5786521514755149639011789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3857681009836766426007859 5786521514755149639011789)
        ·
          refine ⟨2169945568033181114629421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5786521514755149639011789 2169945568033181114629421)
          ·
            refine ⟨813729588012442917986033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2169945568033181114629421 813729588012442917986033)
            ·
              refine ⟨610297191009332188489525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813729588012442917986033 610297191009332188489525)
              ·
                refine ⟨57215361657124892670893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 610297191009332188489525 57215361657124892670893)
                ·
                  rfl

theorem cell21_752129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 5].length) (baseStart_752129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752129 prefixEnd_752129 := by exact prefixLift 752129
  have htrace : WordTrace (prefixWord ++ tailWord_752129) baseStart_752129 baseEnd_752129 := by
    simpa [prefixWord, tailWord_752129, baseEnd_752129] using wordTrace_append hprefix tailTrace_752129
  have hstable : (prefixWord ++ tailWord_752129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752129).length < 2 ^ (prefixWord ++ tailWord_752129).sum := by decide
  have hdescent : baseEnd_752129 < baseStart_752129 := by decide
  rcases family_descends (prefixWord ++ tailWord_752129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752157 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 6]
def baseStart_752157 : Nat := 118140960795 + 752157 * 2 ^ 59
def prefixEnd_752157 : Nat := 4983230072969 + 3 ^ 40 * 752157 * 2
def baseEnd_752157 : Nat := 171652474952852851545955

theorem tailTrace_752157 : CollatzResearch.WordTrace tailWord_752157 prefixEnd_752157 171652474952852851545955 := by
  unfold tailWord_752157
  simp only [CollatzResearch.WordTrace]
  refine ⟨27433419536071122033630725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18288946357380748022420483 27433419536071122033630725)
  ·
    refine ⟨5143766163013335381305761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27433419536071122033630725 5143766163013335381305761)
    ·
      refine ⟨3857824622260001535979321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5143766163013335381305761 3857824622260001535979321)
      ·
        refine ⟨2893368466695001151984491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3857824622260001535979321 2893368466695001151984491)
        ·
          refine ⟨4340052700042501727976737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2893368466695001151984491 4340052700042501727976737)
          ·
            refine ⟨3255039525031876295982553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4340052700042501727976737 3255039525031876295982553)
            ·
              refine ⟨2441279643773907221986915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3255039525031876295982553 2441279643773907221986915)
              ·
                refine ⟨3661919465660860832980373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2441279643773907221986915 3661919465660860832980373)
                ·
                  refine ⟨171652474952852851545955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3661919465660860832980373 171652474952852851545955)
                  ·
                    rfl

theorem cell21_752157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_752157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752157 prefixEnd_752157 := by exact prefixLift 752157
  have htrace : WordTrace (prefixWord ++ tailWord_752157) baseStart_752157 baseEnd_752157 := by
    simpa [prefixWord, tailWord_752157, baseEnd_752157] using wordTrace_append hprefix tailTrace_752157
  have hstable : (prefixWord ++ tailWord_752157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752157).length < 2 ^ (prefixWord ++ tailWord_752157).sum := by decide
  have hdescent : baseEnd_752157 < baseStart_752157 := by decide
  rcases family_descends (prefixWord ++ tailWord_752157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752160 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 5]
def baseStart_752160 : Nat := 118140960795 + 752160 * 2 ^ 59
def prefixEnd_752160 : Nat := 4983230072969 + 3 ^ 40 * 752160 * 2
def baseEnd_752160 : Nat := 171653159593725512995949

theorem tailTrace_752160 : CollatzResearch.WordTrace tailWord_752160 prefixEnd_752160 171653159593725512995949 := by
  unfold tailWord_752160
  simp only [CollatzResearch.WordTrace]
  refine ⟨13716764477530126772994967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18289019303373502363993289 13716764477530126772994967)
  ·
    refine ⟨20575146716295190159492451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13716764477530126772994967 20575146716295190159492451)
    ·
      refine ⟨30862720074442785239238677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20575146716295190159492451 30862720074442785239238677)
      ·
        refine ⟨1446690003489505558089313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30862720074442785239238677 1446690003489505558089313)
        ·
          refine ⟨1085017502617129168566985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1446690003489505558089313 1085017502617129168566985)
          ·
            refine ⟨813763126962846876425239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1085017502617129168566985 813763126962846876425239)
            ·
              refine ⟨1220644690444270314637859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813763126962846876425239 1220644690444270314637859)
              ·
                refine ⟨1830967035666405471956789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220644690444270314637859 1830967035666405471956789)
                ·
                  refine ⟨171653159593725512995949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1830967035666405471956789 171653159593725512995949)
                  ·
                    rfl

theorem cell21_752160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_752160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752160 prefixEnd_752160 := by exact prefixLift 752160
  have htrace : WordTrace (prefixWord ++ tailWord_752160) baseStart_752160 baseEnd_752160 := by
    simpa [prefixWord, tailWord_752160, baseEnd_752160] using wordTrace_append hprefix tailTrace_752160
  have hstable : (prefixWord ++ tailWord_752160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752160).length < 2 ^ (prefixWord ++ tailWord_752160).sum := by decide
  have hdescent : baseEnd_752160 < baseStart_752160 := by decide
  rcases family_descends (prefixWord ++ tailWord_752160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752216 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 6]
def baseStart_752216 : Nat := 118140960795 + 752216 * 2 ^ 59
def prefixEnd_752216 : Nat := 4983230072969 + 3 ^ 40 * 752216 * 2
def baseEnd_752216 : Nat := 171665939556681860062501

theorem tailTrace_752216 : CollatzResearch.WordTrace tailWord_752216 prefixEnd_752216 171665939556681860062501 := by
  unfold tailWord_752216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13717785721428687555014251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18290380961904916740019001 13717785721428687555014251)
  ·
    refine ⟨20576678582143031332521377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13717785721428687555014251 20576678582143031332521377)
    ·
      refine ⟨15432508936607273499391033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20576678582143031332521377 15432508936607273499391033)
      ·
        refine ⟨11574381702455455124543275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15432508936607273499391033 11574381702455455124543275)
        ·
          refine ⟨17361572553683182686814913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11574381702455455124543275 17361572553683182686814913)
          ·
            refine ⟨13021179415262387015111185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17361572553683182686814913 13021179415262387015111185)
            ·
              refine ⟨9765884561446790261333389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13021179415262387015111185 9765884561446790261333389)
              ·
                refine ⟨3662206710542546348000021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9765884561446790261333389 3662206710542546348000021)
                ·
                  refine ⟨171665939556681860062501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3662206710542546348000021 171665939556681860062501)
                  ·
                    rfl

theorem cell21_752216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_752216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752216 prefixEnd_752216 := by exact prefixLift 752216
  have htrace : WordTrace (prefixWord ++ tailWord_752216) baseStart_752216 baseEnd_752216 := by
    simpa [prefixWord, tailWord_752216, baseEnd_752216] using wordTrace_append hprefix tailTrace_752216
  have hstable : (prefixWord ++ tailWord_752216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752216).length < 2 ^ (prefixWord ++ tailWord_752216).sum := by decide
  have hdescent : baseEnd_752216 < baseStart_752216 := by decide
  rcases family_descends (prefixWord ++ tailWord_752216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752309 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 6]
def baseStart_752309 : Nat := 118140960795 + 752309 * 2 ^ 59
def prefixEnd_752309 : Nat := 4983230072969 + 3 ^ 40 * 752309 * 2
def baseEnd_752309 : Nat := 171687163423734365012311

theorem tailTrace_752309 : CollatzResearch.WordTrace tailWord_752309 prefixEnd_752309 171687163423734365012311 := by
  unfold tailWord_752309
  simp only [CollatzResearch.WordTrace]
  refine ⟨27438963431520451993163981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18292642287680301328775987 27438963431520451993163981)
  ·
    refine ⟨10289611286820169497436493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27438963431520451993163981 10289611286820169497436493)
    ·
      refine ⟨3858604232557563561538685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10289611286820169497436493 3858604232557563561538685)
      ·
        refine ⟨1446976587209086335577007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3858604232557563561538685 1446976587209086335577007)
        ·
          refine ⟨2170464880813629503365511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446976587209086335577007 2170464880813629503365511)
          ·
            refine ⟨3255697321220444255048267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170464880813629503365511 3255697321220444255048267)
            ·
              refine ⟨4883545981830666382572401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3255697321220444255048267 4883545981830666382572401)
              ·
                refine ⟨3662659486372999786929301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4883545981830666382572401 3662659486372999786929301)
                ·
                  refine ⟨171687163423734365012311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3662659486372999786929301 171687163423734365012311)
                  ·
                    rfl

theorem cell21_752309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_752309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752309 prefixEnd_752309 := by exact prefixLift 752309
  have htrace : WordTrace (prefixWord ++ tailWord_752309) baseStart_752309 baseEnd_752309 := by
    simpa [prefixWord, tailWord_752309, baseEnd_752309] using wordTrace_append hprefix tailTrace_752309
  have hstable : (prefixWord ++ tailWord_752309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752309).length < 2 ^ (prefixWord ++ tailWord_752309).sum := by decide
  have hdescent : baseEnd_752309 < baseStart_752309 := by decide
  rcases family_descends (prefixWord ++ tailWord_752309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752416 : List Nat := [2, 1, 1, 5, 1, 3, 3, 5]
def baseStart_752416 : Nat := 118140960795 + 752416 * 2 ^ 59
def prefixEnd_752416 : Nat := 4983230072969 + 3 ^ 40 * 752416 * 2
def baseEnd_752416 : Nat := 57237194093841985576253

theorem tailTrace_752416 : CollatzResearch.WordTrace tailWord_752416 prefixEnd_752416 57237194093841985576253 := by
  unfold tailWord_752416
  simp only [CollatzResearch.WordTrace]
  refine ⟨13721433021066404633654551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18295244028088539511539401 13721433021066404633654551)
  ·
    refine ⟨20582149531599606950481827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13721433021066404633654551 20582149531599606950481827)
    ·
      refine ⟨30873224297399410425722741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20582149531599606950481827 30873224297399410425722741)
      ·
        refine ⟨2894364777881194727411507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30873224297399410425722741 2894364777881194727411507)
        ·
          refine ⟨4341547166821792091117261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894364777881194727411507 4341547166821792091117261)
          ·
            refine ⟨1628080187558172034168973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4341547166821792091117261 1628080187558172034168973)
            ·
              refine ⟨610530070334314512813365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1628080187558172034168973 610530070334314512813365)
              ·
                refine ⟨57237194093841985576253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 610530070334314512813365 57237194093841985576253)
                ·
                  rfl

theorem cell21_752416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 5].length) (baseStart_752416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752416 prefixEnd_752416 := by exact prefixLift 752416
  have htrace : WordTrace (prefixWord ++ tailWord_752416) baseStart_752416 baseEnd_752416 := by
    simpa [prefixWord, tailWord_752416, baseEnd_752416] using wordTrace_append hprefix tailTrace_752416
  have hstable : (prefixWord ++ tailWord_752416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752416).length < 2 ^ (prefixWord ++ tailWord_752416).sum := by decide
  have hdescent : baseEnd_752416 < baseStart_752416 := by decide
  rcases family_descends (prefixWord ++ tailWord_752416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752436 : List Nat := [2, 5, 1, 1, 4, 1, 1, 2, 4]
def baseStart_752436 : Nat := 118140960795 + 752436 * 2 ^ 59
def prefixEnd_752436 : Nat := 4983230072969 + 3 ^ 40 * 752436 * 2
def baseEnd_752436 : Nat := 171716146554010366395385

theorem tailTrace_752436 : CollatzResearch.WordTrace tailWord_752436 prefixEnd_752436 171716146554010366395385 := by
  unfold tailWord_752436
  simp only [CollatzResearch.WordTrace]
  refine ⟨13721797751030176341518581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18295730334706901788691441 13721797751030176341518581)
  ·
    refine ⟨1286418539159079032017367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13721797751030176341518581 1286418539159079032017367)
    ·
      refine ⟨1929627808738618548026051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1286418539159079032017367 1929627808738618548026051)
      ·
        refine ⟨2894441713107927822039077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929627808738618548026051 2894441713107927822039077)
        ·
          refine ⟨542707821207736466632327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2894441713107927822039077 542707821207736466632327)
          ·
            refine ⟨814061731811604699948491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542707821207736466632327 814061731811604699948491)
            ·
              refine ⟨1221092597717407049922737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814061731811604699948491 1221092597717407049922737)
              ·
                refine ⟨915819448288055287442053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221092597717407049922737 915819448288055287442053)
                ·
                  refine ⟨171716146554010366395385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 915819448288055287442053 171716146554010366395385)
                  ·
                    rfl

theorem cell21_752436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_752436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752436 prefixEnd_752436 := by exact prefixLift 752436
  have htrace : WordTrace (prefixWord ++ tailWord_752436) baseStart_752436 baseEnd_752436 := by
    simpa [prefixWord, tailWord_752436, baseEnd_752436] using wordTrace_append hprefix tailTrace_752436
  have hstable : (prefixWord ++ tailWord_752436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752436).length < 2 ^ (prefixWord ++ tailWord_752436).sum := by decide
  have hdescent : baseEnd_752436 < baseStart_752436 := by decide
  rcases family_descends (prefixWord ++ tailWord_752436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752447 : List Nat := [1, 1, 2, 2, 5, 1, 2, 4, 3]
def baseStart_752447 : Nat := 118140960795 + 752447 * 2 ^ 59
def prefixEnd_752447 : Nat := 4983230072969 + 3 ^ 40 * 752447 * 2
def baseEnd_752447 : Nat := 171718656903876791712029

theorem tailTrace_752447 : CollatzResearch.WordTrace tailWord_752447 prefixEnd_752447 171718656903876791712029 := by
  unfold tailWord_752447
  simp only [CollatzResearch.WordTrace]
  refine ⟨27443996705020501561687595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18295997803347001041125063 27443996705020501561687595)
  ·
    refine ⟨41165995057530752342531393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27443996705020501561687595 41165995057530752342531393)
    ·
      refine ⟨30874496293148064256898545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41165995057530752342531393 30874496293148064256898545)
      ·
        refine ⟨23155872219861048192673909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30874496293148064256898545 23155872219861048192673909)
        ·
          refine ⟨2170863020611973268063179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23155872219861048192673909 2170863020611973268063179)
          ·
            refine ⟨3256294530917959902094769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170863020611973268063179 3256294530917959902094769)
            ·
              refine ⟨2442220898188469926571077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3256294530917959902094769 2442220898188469926571077)
              ·
                refine ⟨457916418410338111232077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2442220898188469926571077 457916418410338111232077)
                ·
                  refine ⟨171718656903876791712029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457916418410338111232077 171718656903876791712029)
                  ·
                    rfl

theorem cell21_752447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 3].length) (baseStart_752447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752447 prefixEnd_752447 := by exact prefixLift 752447
  have htrace : WordTrace (prefixWord ++ tailWord_752447) baseStart_752447 baseEnd_752447 := by
    simpa [prefixWord, tailWord_752447, baseEnd_752447] using wordTrace_append hprefix tailTrace_752447
  have hstable : (prefixWord ++ tailWord_752447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752447).length < 2 ^ (prefixWord ++ tailWord_752447).sum := by decide
  have hdescent : baseEnd_752447 < baseStart_752447 := by decide
  rcases family_descends (prefixWord ++ tailWord_752447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752551 : List Nat := [1, 1, 6, 1, 3, 9]
def baseStart_752551 : Nat := 118140960795 + 752551 * 2 ^ 59
def prefixEnd_752551 : Nat := 4983230072969 + 3 ^ 40 * 752551 * 2
def baseEnd_752551 : Nat := 6360829300770211925129

theorem tailTrace_752551 : CollatzResearch.WordTrace tailWord_752551 prefixEnd_752551 6360829300770211925129 := by
  unfold tailWord_752551
  simp only [CollatzResearch.WordTrace]
  refine ⟨27447789896643727323473507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18298526597762484882315671 27447789896643727323473507)
  ·
    refine ⟨41171684844965590985210261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27447789896643727323473507 41171684844965590985210261)
    ·
      refine ⟨1929922727107762077431731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41171684844965590985210261 1929922727107762077431731)
      ·
        refine ⟨2894884090661643116147597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929922727107762077431731 2894884090661643116147597)
        ·
          refine ⟨1085581533998116168555349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2894884090661643116147597 1085581533998116168555349)
          ·
            refine ⟨6360829300770211925129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1085581533998116168555349 6360829300770211925129)
            ·
              rfl

theorem cell21_752551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 9].length) (baseStart_752551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752551 prefixEnd_752551 := by exact prefixLift 752551
  have htrace : WordTrace (prefixWord ++ tailWord_752551) baseStart_752551 baseEnd_752551 := by
    simpa [prefixWord, tailWord_752551, baseEnd_752551] using wordTrace_append hprefix tailTrace_752551
  have hstable : (prefixWord ++ tailWord_752551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752551).length < 2 ^ (prefixWord ++ tailWord_752551).sum := by decide
  have hdescent : baseEnd_752551 < baseStart_752551 := by decide
  rcases family_descends (prefixWord ++ tailWord_752551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752557 : List Nat := [1, 5, 2, 3, 1, 1, 1, 4, 3]
def baseStart_752557 : Nat := 118140960795 + 752557 * 2 ^ 59
def prefixEnd_752557 : Nat := 4983230072969 + 3 ^ 40 * 752557 * 2
def baseEnd_752557 : Nat := 171743760402541044878471

theorem tailTrace_752557 : CollatzResearch.WordTrace tailWord_752557 prefixEnd_752557 171743760402541044878471 := by
  unfold tailWord_752557
  simp only [CollatzResearch.WordTrace]
  refine ⟨27448008734621990348191925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18298672489747993565461283 27448008734621990348191925)
  ·
    refine ⟨2573250818870811595142993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27448008734621990348191925 2573250818870811595142993)
    ·
      refine ⟨1929938114153108696357245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2573250818870811595142993 1929938114153108696357245)
      ·
        refine ⟨723726792807415761133967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1929938114153108696357245 723726792807415761133967)
        ·
          refine ⟨1085590189211123641700951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723726792807415761133967 1085590189211123641700951)
          ·
            refine ⟨1628385283816685462551427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085590189211123641700951 1628385283816685462551427)
            ·
              refine ⟨2442577925725028193827141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628385283816685462551427 2442577925725028193827141)
              ·
                refine ⟨457983361073442786342589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2442577925725028193827141 457983361073442786342589)
                ·
                  refine ⟨171743760402541044878471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457983361073442786342589 171743760402541044878471)
                  ·
                    rfl

theorem cell21_752557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_752557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752557 prefixEnd_752557 := by exact prefixLift 752557
  have htrace : WordTrace (prefixWord ++ tailWord_752557) baseStart_752557 baseEnd_752557 := by
    simpa [prefixWord, tailWord_752557, baseEnd_752557] using wordTrace_append hprefix tailTrace_752557
  have hstable : (prefixWord ++ tailWord_752557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752557).length < 2 ^ (prefixWord ++ tailWord_752557).sum := by decide
  have hdescent : baseEnd_752557 < baseStart_752557 := by decide
  rcases family_descends (prefixWord ++ tailWord_752557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752748 : List Nat := [2, 2, 1, 1, 3, 2, 1, 5, 4]
def baseStart_752748 : Nat := 118140960795 + 752748 * 2 ^ 59
def prefixEnd_752748 : Nat := 4983230072969 + 3 ^ 40 * 752748 * 2
def baseEnd_752748 : Nat := 171787349204767157194747

theorem tailTrace_752748 : CollatzResearch.WordTrace tailWord_752748 prefixEnd_752748 171787349204767157194747 := by
  unfold tailWord_752748
  simp only [CollatzResearch.WordTrace]
  refine ⟨13727487538465014984197449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18303316717953353312263265 13727487538465014984197449)
  ·
    refine ⟨10295615653848761238148087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13727487538465014984197449 10295615653848761238148087)
    ·
      refine ⟨15443423480773141857222131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10295615653848761238148087 15443423480773141857222131)
      ·
        refine ⟨23165135221159712785833197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15443423480773141857222131 23165135221159712785833197)
        ·
          refine ⟨8686925707934892294687449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23165135221159712785833197 8686925707934892294687449)
          ·
            refine ⟨6515194280951169221015587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8686925707934892294687449 6515194280951169221015587)
            ·
              refine ⟨9772791421426753831523381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6515194280951169221015587 9772791421426753831523381)
              ·
                refine ⟨916199195758758171705317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9772791421426753831523381 916199195758758171705317)
                ·
                  refine ⟨171787349204767157194747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 916199195758758171705317 171787349204767157194747)
                  ·
                    rfl

theorem cell21_752748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_752748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752748 prefixEnd_752748 := by exact prefixLift 752748
  have htrace : WordTrace (prefixWord ++ tailWord_752748) baseStart_752748 baseEnd_752748 := by
    simpa [prefixWord, tailWord_752748, baseEnd_752748] using wordTrace_append hprefix tailTrace_752748
  have hstable : (prefixWord ++ tailWord_752748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752748).length < 2 ^ (prefixWord ++ tailWord_752748).sum := by decide
  have hdescent : baseEnd_752748 < baseStart_752748 := by decide
  rcases family_descends (prefixWord ++ tailWord_752748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752782 : List Nat := [4, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_752782 : Nat := 118140960795 + 752782 * 2 ^ 59
def prefixEnd_752782 : Nat := 4983230072969 + 3 ^ 40 * 752782 * 2
def baseEnd_752782 : Nat := 171795108467990653628011

theorem tailTrace_752782 : CollatzResearch.WordTrace tailWord_752782 prefixEnd_752782 171795108467990653628011 := by
  unfold tailWord_752782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3432026894850856721891575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18304143439204569183421733 3432026894850856721891575)
  ·
    refine ⟨5148040342276285082837363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3432026894850856721891575 5148040342276285082837363)
    ·
      refine ⟨7722060513414427624256045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5148040342276285082837363 7722060513414427624256045)
      ·
        refine ⟨2895772692530410359096017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7722060513414427624256045 2895772692530410359096017)
        ·
          refine ⟨2171829519397807769322013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2895772692530410359096017 2171829519397807769322013)
          ·
            refine ⟨814436069774177913495755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2171829519397807769322013 814436069774177913495755)
            ·
              refine ⟨1221654104661266870243633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814436069774177913495755 1221654104661266870243633)
              ·
                refine ⟨916240578495950152682725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221654104661266870243633 916240578495950152682725)
                ·
                  refine ⟨171795108467990653628011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 916240578495950152682725 171795108467990653628011)
                  ·
                    rfl

theorem cell21_752782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_752782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752782 prefixEnd_752782 := by exact prefixLift 752782
  have htrace : WordTrace (prefixWord ++ tailWord_752782) baseStart_752782 baseEnd_752782 := by
    simpa [prefixWord, tailWord_752782, baseEnd_752782] using wordTrace_append hprefix tailTrace_752782
  have hstable : (prefixWord ++ tailWord_752782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752782).length < 2 ^ (prefixWord ++ tailWord_752782).sum := by decide
  have hdescent : baseEnd_752782 < baseStart_752782 := by decide
  rcases family_descends (prefixWord ++ tailWord_752782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752813 : List Nat := [1, 5, 2, 1, 3, 2, 2, 5]
def baseStart_752813 : Nat := 118140960795 + 752813 * 2 ^ 59
def prefixEnd_752813 : Nat := 4983230072969 + 3 ^ 40 * 752813 * 2
def baseEnd_752813 : Nat := 57267394363447162870427

theorem tailTrace_752813 : CollatzResearch.WordTrace tailWord_752813 prefixEnd_752813 57267394363447162870427 := by
  unfold tailWord_752813
  simp only [CollatzResearch.WordTrace]
  refine ⟨27457345821694546069511093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18304897214463030713007395 27457345821694546069511093)
  ·
    refine ⟨2574126170783863694016665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27457345821694546069511093 2574126170783863694016665)
    ·
      refine ⟨1930594628087897770512499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2574126170783863694016665 1930594628087897770512499)
      ·
        refine ⟨2895891942131846655768749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1930594628087897770512499 2895891942131846655768749)
        ·
          refine ⟨1085959478299442495913281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2895891942131846655768749 1085959478299442495913281)
          ·
            refine ⟨814469608724581871934961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1085959478299442495913281 814469608724581871934961)
            ·
              refine ⟨610852206543436403951221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814469608724581871934961 610852206543436403951221)
              ·
                refine ⟨57267394363447162870427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 610852206543436403951221 57267394363447162870427)
                ·
                  rfl

theorem cell21_752813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 5].length) (baseStart_752813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752813 prefixEnd_752813 := by exact prefixLift 752813
  have htrace : WordTrace (prefixWord ++ tailWord_752813) baseStart_752813 baseEnd_752813 := by
    simpa [prefixWord, tailWord_752813, baseEnd_752813] using wordTrace_append hprefix tailTrace_752813
  have hstable : (prefixWord ++ tailWord_752813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752813).length < 2 ^ (prefixWord ++ tailWord_752813).sum := by decide
  have hdescent : baseEnd_752813 < baseStart_752813 := by decide
  rcases family_descends (prefixWord ++ tailWord_752813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752931 : List Nat := [1, 1, 1, 4, 2, 4, 3, 5]
def baseStart_752931 : Nat := 118140960795 + 752931 * 2 ^ 59
def prefixEnd_752931 : Nat := 4983230072969 + 3 ^ 40 * 752931 * 2
def baseEnd_752931 : Nat := 57276370765999835214791

theorem tailTrace_752931 : CollatzResearch.WordTrace tailWord_752931 prefixEnd_752931 57276370765999835214791 := by
  unfold tailWord_752931
  simp only [CollatzResearch.WordTrace]
  refine ⟨27461649635267052222306647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18307766423511368148204431 27461649635267052222306647)
  ·
    refine ⟨41192474452900578333459971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27461649635267052222306647 41192474452900578333459971)
    ·
      refine ⟨61788711679350867500189957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41192474452900578333459971 61788711679350867500189957)
      ·
        refine ⟨11585383439878287656285617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61788711679350867500189957 11585383439878287656285617)
        ·
          refine ⟨8689037579908715742214213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11585383439878287656285617 8689037579908715742214213)
          ·
            refine ⟨1629194546232884201665165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8689037579908715742214213 1629194546232884201665165)
            ·
              refine ⟨610947954837331575624437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1629194546232884201665165 610947954837331575624437)
              ·
                refine ⟨57276370765999835214791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 610947954837331575624437 57276370765999835214791)
                ·
                  rfl

theorem cell21_752931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 5].length) (baseStart_752931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752931 prefixEnd_752931 := by exact prefixLift 752931
  have htrace : WordTrace (prefixWord ++ tailWord_752931) baseStart_752931 baseEnd_752931 := by
    simpa [prefixWord, tailWord_752931, baseEnd_752931] using wordTrace_append hprefix tailTrace_752931
  have hstable : (prefixWord ++ tailWord_752931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752931).length < 2 ^ (prefixWord ++ tailWord_752931).sum := by decide
  have hdescent : baseEnd_752931 < baseStart_752931 := by decide
  rcases family_descends (prefixWord ++ tailWord_752931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752982 : List Nat := [5, 2, 3, 1, 1, 1, 1, 7]
def baseStart_752982 : Nat := 118140960795 + 752982 * 2 ^ 59
def prefixEnd_752982 : Nat := 4983230072969 + 3 ^ 40 * 752982 * 2
def baseEnd_752982 : Nat := 57280250397611583431423

theorem tailTrace_752982 : CollatzResearch.WordTrace tailWord_752982 prefixEnd_752982 57280250397611583431423 := by
  unfold tailWord_752982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1716469359880142995775825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18309006505388191954942133 1716469359880142995775825)
  ·
    refine ⟨1287352019910107246831869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1716469359880142995775825 1287352019910107246831869)
    ·
      refine ⟨482757007466290217561951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1287352019910107246831869 482757007466290217561951)
      ·
        refine ⟨724135511199435326342927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482757007466290217561951 724135511199435326342927)
        ·
          refine ⟨1086203266799152989514391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724135511199435326342927 1086203266799152989514391)
          ·
            refine ⟨1629304900198729484271587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1086203266799152989514391 1629304900198729484271587)
            ·
              refine ⟨2443957350298094226407381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629304900198729484271587 2443957350298094226407381)
              ·
                refine ⟨57280250397611583431423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2443957350298094226407381 57280250397611583431423)
                ·
                  rfl

theorem cell21_752982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_752982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_752982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_752982 prefixEnd_752982 := by exact prefixLift 752982
  have htrace : WordTrace (prefixWord ++ tailWord_752982) baseStart_752982 baseEnd_752982 := by
    simpa [prefixWord, tailWord_752982, baseEnd_752982] using wordTrace_append hprefix tailTrace_752982
  have hstable : (prefixWord ++ tailWord_752982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752982).length < 2 ^ (prefixWord ++ tailWord_752982).sum := by decide
  have hdescent : baseEnd_752982 < baseStart_752982 := by decide
  rcases family_descends (prefixWord ++ tailWord_752982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753069 : List Nat := [1, 5, 2, 2, 1, 1, 1, 4, 4]
def baseStart_753069 : Nat := 118140960795 + 753069 * 2 ^ 59
def prefixEnd_753069 : Nat := 4983230072969 + 3 ^ 40 * 753069 * 2
def baseEnd_753069 : Nat := 171860605778141932344091

theorem tailTrace_753069 : CollatzResearch.WordTrace tailWord_753069 prefixEnd_753069 171860605778141932344091 := by
  unfold tailWord_753069
  simp only [CollatzResearch.WordTrace]
  refine ⟨27466682908767101790830261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18311121939178067860553507 27466682908767101790830261)
  ·
    refine ⟨2575001522696915792890337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27466682908767101790830261 2575001522696915792890337)
    ·
      refine ⟨1931251142022686844667753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2575001522696915792890337 1931251142022686844667753)
      ·
        refine ⟨1448438356517015133500815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1931251142022686844667753 1448438356517015133500815)
        ·
          refine ⟨2172657534775522700251223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448438356517015133500815 2172657534775522700251223)
          ·
            refine ⟨3258986302163284050376835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172657534775522700251223 3258986302163284050376835)
            ·
              refine ⟨4888479453244926075565253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3258986302163284050376835 4888479453244926075565253)
              ·
                refine ⟨916589897483423639168485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4888479453244926075565253 916589897483423639168485)
                ·
                  refine ⟨171860605778141932344091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 916589897483423639168485 171860605778141932344091)
                  ·
                    rfl

theorem cell21_753069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_753069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753069 prefixEnd_753069 := by exact prefixLift 753069
  have htrace : WordTrace (prefixWord ++ tailWord_753069) baseStart_753069 baseEnd_753069 := by
    simpa [prefixWord, tailWord_753069, baseEnd_753069] using wordTrace_append hprefix tailTrace_753069
  have hstable : (prefixWord ++ tailWord_753069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753069).length < 2 ^ (prefixWord ++ tailWord_753069).sum := by decide
  have hdescent : baseEnd_753069 < baseStart_753069 := by decide
  rcases family_descends (prefixWord ++ tailWord_753069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753114 : List Nat := [3, 1, 1, 2, 3, 2, 1, 5, 3]
def baseStart_753114 : Nat := 118140960795 + 753114 * 2 ^ 59
def prefixEnd_753114 : Nat := 4983230072969 + 3 ^ 40 * 753114 * 2
def baseEnd_753114 : Nat := 171870875391231854093999

theorem tailTrace_753114 : CollatzResearch.WordTrace tailWord_753114 prefixEnd_753114 171870875391231854093999 := by
  unfold tailWord_753114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6867081048401018619054599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18312216129069382984145597 6867081048401018619054599)
  ·
    refine ⟨10300621572601527928581899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6867081048401018619054599 10300621572601527928581899)
    ·
      refine ⟨15450932358902291892872849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10300621572601527928581899 15450932358902291892872849)
      ·
        refine ⟨11588199269176718919654637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15450932358902291892872849 11588199269176718919654637)
        ·
          refine ⟨4345574725941269594870489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11588199269176718919654637 4345574725941269594870489)
          ·
            refine ⟨3259181044455952196152867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4345574725941269594870489 3259181044455952196152867)
            ·
              refine ⟨4888771566683928294229301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3259181044455952196152867 4888771566683928294229301)
              ·
                refine ⟨458322334376618277583997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4888771566683928294229301 458322334376618277583997)
                ·
                  refine ⟨171870875391231854093999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458322334376618277583997 171870875391231854093999)
                  ·
                    rfl

theorem cell21_753114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_753114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753114 prefixEnd_753114 := by exact prefixLift 753114
  have htrace : WordTrace (prefixWord ++ tailWord_753114) baseStart_753114 baseEnd_753114 := by
    simpa [prefixWord, tailWord_753114, baseEnd_753114] using wordTrace_append hprefix tailTrace_753114
  have hstable : (prefixWord ++ tailWord_753114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753114).length < 2 ^ (prefixWord ++ tailWord_753114).sum := by decide
  have hdescent : baseEnd_753114 < baseStart_753114 := by decide
  rcases family_descends (prefixWord ++ tailWord_753114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753159 : List Nat := [1, 1, 4, 3, 2, 1, 4, 5]
def baseStart_753159 : Nat := 118140960795 + 753159 * 2 ^ 59
def prefixEnd_753159 : Nat := 4983230072969 + 3 ^ 40 * 753159 * 2
def baseEnd_753159 : Nat := 57293715001440591947969

theorem tailTrace_753159 : CollatzResearch.WordTrace tailWord_753159 prefixEnd_753159 57293715001440591947969 := by
  unfold tailWord_753159
  simp only [CollatzResearch.WordTrace]
  refine ⟨27469965478441047161606531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18313310318960698107737687 27469965478441047161606531)
  ·
    refine ⟨41204948217661570742409797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27469965478441047161606531 41204948217661570742409797)
    ·
      refine ⟨7725927790811544514201837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41204948217661570742409797 7725927790811544514201837)
      ·
        refine ⟨2897222921554329192825689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7725927790811544514201837 2897222921554329192825689)
        ·
          refine ⟨2172917191165746894619267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2897222921554329192825689 2172917191165746894619267)
          ·
            refine ⟨3259375786748620341928901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172917191165746894619267 3259375786748620341928901)
            ·
              refine ⟨611132960015366314111669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3259375786748620341928901 611132960015366314111669)
              ·
                refine ⟨57293715001440591947969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 611132960015366314111669 57293715001440591947969)
                ·
                  rfl

theorem cell21_753159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 5].length) (baseStart_753159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753159 prefixEnd_753159 := by exact prefixLift 753159
  have htrace : WordTrace (prefixWord ++ tailWord_753159) baseStart_753159 baseEnd_753159 := by
    simpa [prefixWord, tailWord_753159, baseEnd_753159] using wordTrace_append hprefix tailTrace_753159
  have hstable : (prefixWord ++ tailWord_753159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753159).length < 2 ^ (prefixWord ++ tailWord_753159).sum := by decide
  have hdescent : baseEnd_753159 < baseStart_753159 := by decide
  rcases family_descends (prefixWord ++ tailWord_753159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753182 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_753182 : Nat := 118140960795 + 753182 * 2 ^ 59
def prefixEnd_753182 : Nat := 4983230072969 + 3 ^ 40 * 753182 * 2
def baseEnd_753182 : Nat := 171886393917678846960527

theorem tailTrace_753182 : CollatzResearch.WordTrace tailWord_753182 prefixEnd_753182 171886393917678846960527 := by
  unfold tailWord_753182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3433850544669715261211725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18313869571571814726462533 3433850544669715261211725)
  ·
    refine ⟨1287693954251143222954397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3433850544669715261211725 1287693954251143222954397)
    ·
      refine ⟨482885232844178708607899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1287693954251143222954397 482885232844178708607899)
      ·
        refine ⟨724327849266268062911849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482885232844178708607899 724327849266268062911849)
        ·
          refine ⟨543245886949701047183887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724327849266268062911849 543245886949701047183887)
          ·
            refine ⟨814868830424551570775831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543245886949701047183887 814868830424551570775831)
            ·
              refine ⟨1222303245636827356163747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814868830424551570775831 1222303245636827356163747)
              ·
                refine ⟨1833454868455241034245621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1222303245636827356163747 1833454868455241034245621)
                ·
                  refine ⟨171886393917678846960527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1833454868455241034245621 171886393917678846960527)
                  ·
                    rfl

theorem cell21_753182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_753182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753182 prefixEnd_753182 := by exact prefixLift 753182
  have htrace : WordTrace (prefixWord ++ tailWord_753182) baseStart_753182 baseEnd_753182 := by
    simpa [prefixWord, tailWord_753182, baseEnd_753182] using wordTrace_append hprefix tailTrace_753182
  have hstable : (prefixWord ++ tailWord_753182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753182).length < 2 ^ (prefixWord ++ tailWord_753182).sum := by decide
  have hdescent : baseEnd_753182 < baseStart_753182 := by decide
  rcases family_descends (prefixWord ++ tailWord_753182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753294 : List Nat := [4, 1, 1, 3, 1, 3, 8]
def baseStart_753294 : Nat := 118140960795 + 753294 * 2 ^ 59
def prefixEnd_753294 : Nat := 4983230072969 + 3 ^ 40 * 753294 * 2
def baseEnd_753294 : Nat := 19101328204843504565959

theorem tailTrace_753294 : CollatzResearch.WordTrace tailWord_753294 prefixEnd_753294 19101328204843504565959 := by
  unfold tailWord_753294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3434361166618995652221367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18316592888634643478513957 3434361166618995652221367)
  ·
    refine ⟨5151541749928493478332051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3434361166618995652221367 5151541749928493478332051)
    ·
      refine ⟨7727312624892740217498077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5151541749928493478332051 7727312624892740217498077)
      ·
        refine ⟨2897742234334777581561779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7727312624892740217498077 2897742234334777581561779)
        ·
          refine ⟨4346613351502166372342669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2897742234334777581561779 4346613351502166372342669)
          ·
            refine ⟨1629980006813312389628501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4346613351502166372342669 1629980006813312389628501)
            ·
              refine ⟨19101328204843504565959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1629980006813312389628501 19101328204843504565959)
              ·
                rfl

theorem cell21_753294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 8].length) (baseStart_753294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753294 prefixEnd_753294 := by exact prefixLift 753294
  have htrace : WordTrace (prefixWord ++ tailWord_753294) baseStart_753294 baseEnd_753294 := by
    simpa [prefixWord, tailWord_753294, baseEnd_753294] using wordTrace_append hprefix tailTrace_753294
  have hstable : (prefixWord ++ tailWord_753294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753294).length < 2 ^ (prefixWord ++ tailWord_753294).sum := by decide
  have hdescent : baseEnd_753294 < baseStart_753294 := by decide
  rcases family_descends (prefixWord ++ tailWord_753294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753325 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 5]
def baseStart_753325 : Nat := 118140960795 + 753325 * 2 ^ 59
def prefixEnd_753325 : Nat := 4983230072969 + 3 ^ 40 * 753325 * 2
def baseEnd_753325 : Nat := 171919028465942376076901

theorem tailTrace_753325 : CollatzResearch.WordTrace tailWord_753325 prefixEnd_753325 171919028465942376076901 := by
  unfold tailWord_753325
  simp only [CollatzResearch.WordTrace]
  refine ⟨27476019995839657512149429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18317346663893105008099619 27476019995839657512149429)
  ·
    refine ⟨2575876874609967891764009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27476019995839657512149429 2575876874609967891764009)
    ·
      refine ⟨1931907655957475918823007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2575876874609967891764009 1931907655957475918823007)
      ·
        refine ⟨2897861483936213878234511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1931907655957475918823007 2897861483936213878234511)
        ·
          refine ⟨4346792225904320817351767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2897861483936213878234511 4346792225904320817351767)
          ·
            refine ⟨6520188338856481226027651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4346792225904320817351767 6520188338856481226027651)
            ·
              refine ⟨9780282508284721839041477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6520188338856481226027651 9780282508284721839041477)
              ·
                refine ⟨1833802970303385344820277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9780282508284721839041477 1833802970303385344820277)
                ·
                  refine ⟨171919028465942376076901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1833802970303385344820277 171919028465942376076901)
                  ·
                    rfl

theorem cell21_753325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_753325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753325 prefixEnd_753325 := by exact prefixLift 753325
  have htrace : WordTrace (prefixWord ++ tailWord_753325) baseStart_753325 baseEnd_753325 := by
    simpa [prefixWord, tailWord_753325, baseEnd_753325] using wordTrace_append hprefix tailTrace_753325
  have hstable : (prefixWord ++ tailWord_753325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753325).length < 2 ^ (prefixWord ++ tailWord_753325).sum := by decide
  have hdescent : baseEnd_753325 < baseStart_753325 := by decide
  rcases family_descends (prefixWord ++ tailWord_753325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753370 : List Nat := [3, 1, 1, 2, 2, 4, 2, 6]
def baseStart_753370 : Nat := 118140960795 + 753370 * 2 ^ 59
def prefixEnd_753370 : Nat := 4983230072969 + 3 ^ 40 * 753370 * 2
def baseEnd_753370 : Nat := 57309766026344099275603

theorem tailTrace_753370 : CollatzResearch.WordTrace tailWord_753370 prefixEnd_753370 57309766026344099275603 := by
  unfold tailWord_753370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6869415320169157549384391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18318440853784420131691709 6869415320169157549384391)
  ·
    refine ⟨10304122980253736324076587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6869415320169157549384391 10304122980253736324076587)
    ·
      refine ⟨15456184470380604486114881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10304122980253736324076587 15456184470380604486114881)
      ·
        refine ⟨11592138352785453364586161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15456184470380604486114881 11592138352785453364586161)
        ·
          refine ⟨8694103764589090023439621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11592138352785453364586161 8694103764589090023439621)
          ·
            refine ⟨1630144455860454379394929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8694103764589090023439621 1630144455860454379394929)
            ·
              refine ⟨1222608341895340784546197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1630144455860454379394929 1222608341895340784546197)
              ·
                refine ⟨57309766026344099275603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1222608341895340784546197 57309766026344099275603)
                ·
                  rfl

theorem cell21_753370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_753370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753370 prefixEnd_753370 := by exact prefixLift 753370
  have htrace : WordTrace (prefixWord ++ tailWord_753370) baseStart_753370 baseEnd_753370 := by
    simpa [prefixWord, tailWord_753370, baseEnd_753370] using wordTrace_append hprefix tailTrace_753370
  have hstable : (prefixWord ++ tailWord_753370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753370).length < 2 ^ (prefixWord ++ tailWord_753370).sum := by decide
  have hdescent : baseEnd_753370 < baseStart_753370 := by decide
  rcases family_descends (prefixWord ++ tailWord_753370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753418 : List Nat := [3, 1, 2, 2, 1, 4, 1, 4, 3]
def baseStart_753418 : Nat := 118140960795 + 753418 * 2 ^ 59
def prefixEnd_753418 : Nat := 4983230072969 + 3 ^ 40 * 753418 * 2
def baseEnd_753418 : Nat := 171940252332994881026711

theorem tailTrace_753418 : CollatzResearch.WordTrace tailWord_753418 prefixEnd_753418 171940252332994881026711 := by
  unfold tailWord_753418
  simp only [CollatzResearch.WordTrace]
  refine ⟨6869852996125683598821227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18319607989668489596856605 6869852996125683598821227)
  ·
    refine ⟨10304779494188525398231841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6869852996125683598821227 10304779494188525398231841)
    ·
      refine ⟨7728584620641394048673881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10304779494188525398231841 7728584620641394048673881)
      ·
        refine ⟨5796438465481045536505411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7728584620641394048673881 5796438465481045536505411)
        ·
          refine ⟨8694657698221568304758117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5796438465481045536505411 8694657698221568304758117)
          ·
            refine ⟨1630248318416544057142147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8694657698221568304758117 1630248318416544057142147)
            ·
              refine ⟨2445372477624816085713221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1630248318416544057142147 2445372477624816085713221)
              ·
                refine ⟨458507339554653016071229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2445372477624816085713221 458507339554653016071229)
                ·
                  refine ⟨171940252332994881026711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458507339554653016071229 171940252332994881026711)
                  ·
                    rfl

theorem cell21_753418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_753418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753418 prefixEnd_753418 := by exact prefixLift 753418
  have htrace : WordTrace (prefixWord ++ tailWord_753418) baseStart_753418 baseEnd_753418 := by
    simpa [prefixWord, tailWord_753418, baseEnd_753418] using wordTrace_append hprefix tailTrace_753418
  have hstable : (prefixWord ++ tailWord_753418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753418).length < 2 ^ (prefixWord ++ tailWord_753418).sum := by decide
  have hdescent : baseEnd_753418 < baseStart_753418 := by decide
  rcases family_descends (prefixWord ++ tailWord_753418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753477 : List Nat := [1, 3, 1, 1, 1, 2, 3, 6, 3]
def baseStart_753477 : Nat := 118140960795 + 753477 * 2 ^ 59
def prefixEnd_753477 : Nat := 4983230072969 + 3 ^ 40 * 753477 * 2
def baseEnd_753477 : Nat := 171953716936823889543257

theorem tailTrace_753477 : CollatzResearch.WordTrace tailWord_753477 prefixEnd_753477 171953716936823889543257 := by
  unfold tailWord_753477
  simp only [CollatzResearch.WordTrace]
  refine ⟨27481563891288987471682685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18321042594192658314455123 27481563891288987471682685)
  ·
    refine ⟨10305586459233370301881007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27481563891288987471682685 10305586459233370301881007)
    ·
      refine ⟨15458379688850055452821511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10305586459233370301881007 15458379688850055452821511)
      ·
        refine ⟨23187569533275083179232267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15458379688850055452821511 23187569533275083179232267)
        ·
          refine ⟨34781354299912624768848401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23187569533275083179232267 34781354299912624768848401)
          ·
            refine ⟨26086015724934468576636301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34781354299912624768848401 26086015724934468576636301)
            ·
              refine ⟨9782255896850425716238613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26086015724934468576636301 9782255896850425716238613)
              ·
                refine ⟨458543245164863705448685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9782255896850425716238613 458543245164863705448685)
                ·
                  refine ⟨171953716936823889543257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458543245164863705448685 171953716936823889543257)
                  ·
                    rfl

theorem cell21_753477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_753477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753477 prefixEnd_753477 := by exact prefixLift 753477
  have htrace : WordTrace (prefixWord ++ tailWord_753477) baseStart_753477 baseEnd_753477 := by
    simpa [prefixWord, tailWord_753477, baseEnd_753477] using wordTrace_append hprefix tailTrace_753477
  have hstable : (prefixWord ++ tailWord_753477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753477).length < 2 ^ (prefixWord ++ tailWord_753477).sum := by decide
  have hdescent : baseEnd_753477 < baseStart_753477 := by decide
  rcases family_descends (prefixWord ++ tailWord_753477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753505 : List Nat := [1, 2, 3, 1, 1, 1, 5, 7]
def baseStart_753505 : Nat := 118140960795 + 753505 * 2 ^ 59
def prefixEnd_753505 : Nat := 4983230072969 + 3 ^ 40 * 753505 * 2
def baseEnd_753505 : Nat := 57320035639434021025511

theorem tailTrace_753505 : CollatzResearch.WordTrace tailWord_753505 prefixEnd_753505 57320035639434021025511 := by
  unfold tailWord_753505
  simp only [CollatzResearch.WordTrace]
  refine ⟨27482585135187548253701969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18321723423458365502467979 27482585135187548253701969)
  ·
    refine ⟨20611938851390661190276477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27482585135187548253701969 20611938851390661190276477)
    ·
      refine ⟨7729477069271497946353679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20611938851390661190276477 7729477069271497946353679)
      ·
        refine ⟨11594215603907246919530519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7729477069271497946353679 11594215603907246919530519)
        ·
          refine ⟨17391323405860870379295779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11594215603907246919530519 17391323405860870379295779)
          ·
            refine ⟨26086985108791305568943669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17391323405860870379295779 26086985108791305568943669)
            ·
              refine ⟨2445654853949184897088469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26086985108791305568943669 2445654853949184897088469)
              ·
                refine ⟨57320035639434021025511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2445654853949184897088469 57320035639434021025511)
                ·
                  rfl

theorem cell21_753505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 7].length) (baseStart_753505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753505 prefixEnd_753505 := by exact prefixLift 753505
  have htrace : WordTrace (prefixWord ++ tailWord_753505) baseStart_753505 baseEnd_753505 := by
    simpa [prefixWord, tailWord_753505, baseEnd_753505] using wordTrace_append hprefix tailTrace_753505
  have hstable : (prefixWord ++ tailWord_753505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753505).length < 2 ^ (prefixWord ++ tailWord_753505).sum := by decide
  have hdescent : baseEnd_753505 < baseStart_753505 := by decide
  rcases family_descends (prefixWord ++ tailWord_753505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753581 : List Nat := [1, 5, 2, 13]
def baseStart_753581 : Nat := 118140960795 + 753581 * 2 ^ 59
def prefixEnd_753581 : Nat := 4983230072969 + 3 ^ 40 * 753581 * 2
def baseEnd_753581 : Nat := 707726136435155637077

theorem tailTrace_753581 : CollatzResearch.WordTrace tailWord_753581 prefixEnd_753581 707726136435155637077 := by
  unfold tailWord_753581
  simp only [CollatzResearch.WordTrace]
  refine ⟨27485357082912213233468597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18323571388608142155645731 27485357082912213233468597)
  ·
    refine ⟨2576752226523019990637681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27485357082912213233468597 2576752226523019990637681)
    ·
      refine ⟨1932564169892264992978261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2576752226523019990637681 1932564169892264992978261)
      ·
        refine ⟨707726136435155637077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1932564169892264992978261 707726136435155637077)
        ·
          rfl

theorem cell21_753581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 13].length) (baseStart_753581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753581 prefixEnd_753581 := by exact prefixLift 753581
  have htrace : WordTrace (prefixWord ++ tailWord_753581) baseStart_753581 baseEnd_753581 := by
    simpa [prefixWord, tailWord_753581, baseEnd_753581] using wordTrace_append hprefix tailTrace_753581
  have hstable : (prefixWord ++ tailWord_753581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753581).length < 2 ^ (prefixWord ++ tailWord_753581).sum := by decide
  have hdescent : baseEnd_753581 < baseStart_753581 := by decide
  rcases family_descends (prefixWord ++ tailWord_753581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753598 : List Nat := [4, 2, 1, 1, 1, 3, 3, 6]
def baseStart_753598 : Nat := 118140960795 + 753598 * 2 ^ 59
def prefixEnd_753598 : Nat := 4983230072969 + 3 ^ 40 * 753598 * 2
def baseEnd_753598 : Nat := 57327110261784856008781

theorem tailTrace_753598 : CollatzResearch.WordTrace tailWord_753598 prefixEnd_753598 57327110261784856008781 := by
  unfold tailWord_753598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435747140481328142104681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18323984749233750091224965 3435747140481328142104681)
  ·
    refine ⟨2576810355360996106578511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3435747140481328142104681 2576810355360996106578511)
    ·
      refine ⟨3865215533041494159867767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2576810355360996106578511 3865215533041494159867767)
      ·
        refine ⟨5797823299562241239801651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3865215533041494159867767 5797823299562241239801651)
        ·
          refine ⟨8696734949343361859702477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5797823299562241239801651 8696734949343361859702477)
          ·
            refine ⟨3261275606003760697388429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8696734949343361859702477 3261275606003760697388429)
            ·
              refine ⟨1222978352251410261520661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3261275606003760697388429 1222978352251410261520661)
              ·
                refine ⟨57327110261784856008781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1222978352251410261520661 57327110261784856008781)
                ·
                  rfl

theorem cell21_753598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_753598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753598 prefixEnd_753598 := by exact prefixLift 753598
  have htrace : WordTrace (prefixWord ++ tailWord_753598) baseStart_753598 baseEnd_753598 := by
    simpa [prefixWord, tailWord_753598, baseEnd_753598] using wordTrace_append hprefix tailTrace_753598
  have hstable : (prefixWord ++ tailWord_753598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753598).length < 2 ^ (prefixWord ++ tailWord_753598).sum := by decide
  have hdescent : baseEnd_753598 < baseStart_753598 := by decide
  rcases family_descends (prefixWord ++ tailWord_753598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753612 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 7]
def baseStart_753612 : Nat := 118140960795 + 753612 * 2 ^ 59
def prefixEnd_753612 : Nat := 4983230072969 + 3 ^ 40 * 753612 * 2
def baseEnd_753612 : Nat := 171984525776093654792981

theorem tailTrace_753612 : CollatzResearch.WordTrace tailWord_753612 prefixEnd_753612 171984525776093654792981 := by
  unfold tailWord_753612
  simp only [CollatzResearch.WordTrace]
  refine ⟨13743243872899952763923545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18324325163866603685231393 13743243872899952763923545)
  ·
    refine ⟨10307432904674964572942659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13743243872899952763923545 10307432904674964572942659)
    ·
      refine ⟨15461149357012446859413989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10307432904674964572942659 15461149357012446859413989)
      ·
        refine ⟨2898965504439833786140123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15461149357012446859413989 2898965504439833786140123)
        ·
          refine ⟨4348448256659750679210185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2898965504439833786140123 4348448256659750679210185)
          ·
            refine ⟨3261336192494813009407639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4348448256659750679210185 3261336192494813009407639)
            ·
              refine ⟨4892004288742219514111459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3261336192494813009407639 4892004288742219514111459)
              ·
                refine ⟨7338006433113329271167189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4892004288742219514111459 7338006433113329271167189)
                ·
                  refine ⟨171984525776093654792981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7338006433113329271167189 171984525776093654792981)
                  ·
                    rfl

theorem cell21_753612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_753612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753612 prefixEnd_753612 := by exact prefixLift 753612
  have htrace : WordTrace (prefixWord ++ tailWord_753612) baseStart_753612 baseEnd_753612 := by
    simpa [prefixWord, tailWord_753612, baseEnd_753612] using wordTrace_append hprefix tailTrace_753612
  have hstable : (prefixWord ++ tailWord_753612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753612).length < 2 ^ (prefixWord ++ tailWord_753612).sum := by decide
  have hdescent : baseEnd_753612 < baseStart_753612 := by decide
  rcases family_descends (prefixWord ++ tailWord_753612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753646 : List Nat := [4, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_753646 : Nat := 118140960795 + 753646 * 2 ^ 59
def prefixEnd_753646 : Nat := 4983230072969 + 3 ^ 40 * 753646 * 2
def baseEnd_753646 : Nat := 171992285039317151226245

theorem tailTrace_753646 : CollatzResearch.WordTrace tailWord_753646 prefixEnd_753646 171992285039317151226245 := by
  unfold tailWord_753646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435965978459591166823099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18325151885117819556389861 3435965978459591166823099)
  ·
    refine ⟨5153948967689386750234649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3435965978459591166823099 5153948967689386750234649)
    ·
      refine ⟨3865461725767040062675987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5153948967689386750234649 3865461725767040062675987)
      ·
        refine ⟨5798192588650560094013981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3865461725767040062675987 5798192588650560094013981)
        ·
          refine ⟨2174322220743960035255243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5798192588650560094013981 2174322220743960035255243)
          ·
            refine ⟨3261483331115940052882865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174322220743960035255243 3261483331115940052882865)
            ·
              refine ⟨2446112498336955039662149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3261483331115940052882865 2446112498336955039662149)
              ·
                refine ⟨458646093438179069936653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2446112498336955039662149 458646093438179069936653)
                ·
                  refine ⟨171992285039317151226245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458646093438179069936653 171992285039317151226245)
                  ·
                    rfl

theorem cell21_753646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_753646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753646 prefixEnd_753646 := by exact prefixLift 753646
  have htrace : WordTrace (prefixWord ++ tailWord_753646) baseStart_753646 baseEnd_753646 := by
    simpa [prefixWord, tailWord_753646, baseEnd_753646] using wordTrace_append hprefix tailTrace_753646
  have hstable : (prefixWord ++ tailWord_753646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753646).length < 2 ^ (prefixWord ++ tailWord_753646).sum := by decide
  have hdescent : baseEnd_753646 < baseStart_753646 := by decide
  rcases family_descends (prefixWord ++ tailWord_753646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753660 : List Nat := [2, 2, 2, 1, 2, 2, 5, 1, 4]
def baseStart_753660 : Nat := 118140960795 + 753660 * 2 ^ 59
def prefixEnd_753660 : Nat := 4983230072969 + 3 ^ 40 * 753660 * 2
def baseEnd_753660 : Nat := 171995480030056237992883

theorem tailTrace_753660 : CollatzResearch.WordTrace tailWord_753660 prefixEnd_753660 171995480030056237992883 := by
  unfold tailWord_753660
  simp only [CollatzResearch.WordTrace]
  refine ⟨13744119224813004862797217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18325492299750673150396289 13744119224813004862797217)
  ·
    refine ⟨10308089418609753647097913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13744119224813004862797217 10308089418609753647097913)
    ·
      refine ⟨7731067063957315235323435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10308089418609753647097913 7731067063957315235323435)
      ·
        refine ⟨11596600595935972852985153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7731067063957315235323435 11596600595935972852985153)
        ·
          refine ⟨8697450446951979639738865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11596600595935972852985153 8697450446951979639738865)
          ·
            refine ⟨6523087835213984729804149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8697450446951979639738865 6523087835213984729804149)
            ·
              refine ⟨611539484551311068419139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6523087835213984729804149 611539484551311068419139)
              ·
                refine ⟨917309226826966602628709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611539484551311068419139 917309226826966602628709)
                ·
                  refine ⟨171995480030056237992883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 917309226826966602628709 171995480030056237992883)
                  ·
                    rfl

theorem cell21_753660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_753660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753660 prefixEnd_753660 := by exact prefixLift 753660
  have htrace : WordTrace (prefixWord ++ tailWord_753660) baseStart_753660 baseEnd_753660 := by
    simpa [prefixWord, tailWord_753660, baseEnd_753660] using wordTrace_append hprefix tailTrace_753660
  have hstable : (prefixWord ++ tailWord_753660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753660).length < 2 ^ (prefixWord ++ tailWord_753660).sum := by decide
  have hdescent : baseEnd_753660 < baseStart_753660 := by decide
  rcases family_descends (prefixWord ++ tailWord_753660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753674 : List Nat := [3, 1, 2, 2, 4, 1, 1, 7]
def baseStart_753674 : Nat := 118140960795 + 753674 * 2 ^ 59
def prefixEnd_753674 : Nat := 4983230072969 + 3 ^ 40 * 753674 * 2
def baseEnd_753674 : Nat := 57332891673598441586507

theorem tailTrace_753674 : CollatzResearch.WordTrace tailWord_753674 prefixEnd_753674 57332891673598441586507 := by
  unfold tailWord_753674
  simp only [CollatzResearch.WordTrace]
  refine ⟨6872187267893822529151019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18325832714383526744402717 6872187267893822529151019)
  ·
    refine ⟨10308280901840733793726529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6872187267893822529151019 10308280901840733793726529)
    ·
      refine ⟨7731210676380550345294897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10308280901840733793726529 7731210676380550345294897)
      ·
        refine ⟨5798408007285412758971173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7731210676380550345294897 5798408007285412758971173)
        ·
          refine ⟨1087201501366014892307095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5798408007285412758971173 1087201501366014892307095)
          ·
            refine ⟨1630802252049022338460643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087201501366014892307095 1630802252049022338460643)
            ·
              refine ⟨2446203378073533507690965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1630802252049022338460643 2446203378073533507690965)
              ·
                refine ⟨57332891673598441586507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2446203378073533507690965 57332891673598441586507)
                ·
                  rfl

theorem cell21_753674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_753674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753674 prefixEnd_753674 := by exact prefixLift 753674
  have htrace : WordTrace (prefixWord ++ tailWord_753674) baseStart_753674 baseEnd_753674 := by
    simpa [prefixWord, tailWord_753674, baseEnd_753674] using wordTrace_append hprefix tailTrace_753674
  have hstable : (prefixWord ++ tailWord_753674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753674).length < 2 ^ (prefixWord ++ tailWord_753674).sum := by decide
  have hdescent : baseEnd_753674 < baseStart_753674 := by decide
  rcases family_descends (prefixWord ++ tailWord_753674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753899 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 7]
def baseStart_753899 : Nat := 118140960795 + 753899 * 2 ^ 59
def prefixEnd_753899 : Nat := 4983230072969 + 3 ^ 40 * 753899 * 2
def baseEnd_753899 : Nat := 172050023086244933509061

theorem tailTrace_753899 : CollatzResearch.WordTrace tailWord_753899 prefixEnd_753899 172050023086244933509061 := by
  unfold tailWord_753899
  simp only [CollatzResearch.WordTrace]
  refine ⟨27496955495760153543544751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18331303663840102362363167 27496955495760153543544751)
  ·
    refine ⟨41245433243640230315317127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27496955495760153543544751 41245433243640230315317127)
    ·
      refine ⟨61868149865460345472975691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41245433243640230315317127 61868149865460345472975691)
      ·
        refine ⟨92802224798190518209463537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61868149865460345472975691 92802224798190518209463537)
        ·
          refine ⟨69601668598642888657097653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92802224798190518209463537 69601668598642888657097653)
          ·
            refine ⟨6525156431122770811602905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69601668598642888657097653 6525156431122770811602905)
            ·
              refine ⟨4893867323342078108702179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6525156431122770811602905 4893867323342078108702179)
              ·
                refine ⟨7340800985013117163053269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893867323342078108702179 7340800985013117163053269)
                ·
                  refine ⟨172050023086244933509061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7340800985013117163053269 172050023086244933509061)
                  ·
                    rfl

theorem cell21_753899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_753899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753899 prefixEnd_753899 := by exact prefixLift 753899
  have htrace : WordTrace (prefixWord ++ tailWord_753899) baseStart_753899 baseEnd_753899 := by
    simpa [prefixWord, tailWord_753899, baseEnd_753899] using wordTrace_append hprefix tailTrace_753899
  have hstable : (prefixWord ++ tailWord_753899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753899).length < 2 ^ (prefixWord ++ tailWord_753899).sum := by decide
  have hdescent : baseEnd_753899 < baseStart_753899 := by decide
  rcases family_descends (prefixWord ++ tailWord_753899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753930 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_753930 : Nat := 118140960795 + 753930 * 2 ^ 59
def prefixEnd_753930 : Nat := 4983230072969 + 3 ^ 40 * 753930 * 2
def baseEnd_753930 : Nat := 172057097708595768492331

theorem tailTrace_753930 : CollatzResearch.WordTrace tailWord_753930 prefixEnd_753930 172057097708595768492331 := by
  unfold tailWord_753930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6874521539661961459480811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18332057439098563891948829 6874521539661961459480811)
  ·
    refine ⟨10311782309492942189221217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6874521539661961459480811 10311782309492942189221217)
    ·
      refine ⟨7733836732119706641915913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10311782309492942189221217 7733836732119706641915913)
      ·
        refine ⟨5800377549089779981436935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7733836732119706641915913 5800377549089779981436935)
        ·
          refine ⟨8700566323634669972155403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5800377549089779981436935 8700566323634669972155403)
          ·
            refine ⟨13050849485452004958233105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8700566323634669972155403 13050849485452004958233105)
            ·
              refine ⟨9788137114089003718674829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13050849485452004958233105 9788137114089003718674829)
              ·
                refine ⟨3670551417783376394503061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9788137114089003718674829 3670551417783376394503061)
                ·
                  refine ⟨172057097708595768492331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3670551417783376394503061 172057097708595768492331)
                  ·
                    rfl

theorem cell21_753930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_753930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753930 prefixEnd_753930 := by exact prefixLift 753930
  have htrace : WordTrace (prefixWord ++ tailWord_753930) baseStart_753930 baseEnd_753930 := by
    simpa [prefixWord, tailWord_753930, baseEnd_753930] using wordTrace_append hprefix tailTrace_753930
  have hstable : (prefixWord ++ tailWord_753930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753930).length < 2 ^ (prefixWord ++ tailWord_753930).sum := by decide
  have hdescent : baseEnd_753930 < baseStart_753930 := by decide
  rcases family_descends (prefixWord ++ tailWord_753930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753950 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_753950 : Nat := 118140960795 + 753950 * 2 ^ 59
def prefixEnd_753950 : Nat := 4983230072969 + 3 ^ 40 * 753950 * 2
def baseEnd_753950 : Nat := 172061661981080178158957

theorem tailTrace_753950 : CollatzResearch.WordTrace tailWord_753950 prefixEnd_753950 172061661981080178158957 := by
  unfold tailWord_753950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3437351952321923656706413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18332543745716926169100869 3437351952321923656706413)
  ·
    refine ⟨1289006982120721371264905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3437351952321923656706413 1289006982120721371264905)
    ·
      refine ⟨966755236590541028448679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1289006982120721371264905 966755236590541028448679)
      ·
        refine ⟨1450132854885811542673019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 966755236590541028448679 1450132854885811542673019)
        ·
          refine ⟨2175199282328717314009529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450132854885811542673019 2175199282328717314009529)
          ·
            refine ⟨1631399461746537985507147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2175199282328717314009529 1631399461746537985507147)
            ·
              refine ⟨2447099192619806978260721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631399461746537985507147 2447099192619806978260721)
              ·
                refine ⟨1835324394464855233695541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2447099192619806978260721 1835324394464855233695541)
                ·
                  refine ⟨172061661981080178158957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1835324394464855233695541 172061661981080178158957)
                  ·
                    rfl

theorem cell21_753950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_753950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_753950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_753950 prefixEnd_753950 := by exact prefixLift 753950
  have htrace : WordTrace (prefixWord ++ tailWord_753950) baseStart_753950 baseEnd_753950 := by
    simpa [prefixWord, tailWord_753950, baseEnd_753950] using wordTrace_append hprefix tailTrace_753950
  have hstable : (prefixWord ++ tailWord_753950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753950).length < 2 ^ (prefixWord ++ tailWord_753950).sum := by decide
  have hdescent : baseEnd_753950 < baseStart_753950 := by decide
  rcases family_descends (prefixWord ++ tailWord_753950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754012 : List Nat := [2, 2, 4, 3, 1, 2, 2, 5]
def baseStart_754012 : Nat := 118140960795 + 754012 * 2 ^ 59
def prefixEnd_754012 : Nat := 4983230072969 + 3 ^ 40 * 754012 * 2
def baseEnd_754012 : Nat := 57358603741927282708499

theorem tailTrace_754012 : CollatzResearch.WordTrace tailWord_754012 prefixEnd_754012 57358603741927282708499 := by
  unfold tailWord_754012
  simp only [CollatzResearch.WordTrace]
  refine ⟨13750538472175386921204145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18334051296233849228272193 13750538472175386921204145)
  ·
    refine ⟨10312903854131540190903109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13750538472175386921204145 10312903854131540190903109)
    ·
      refine ⟨1933669472649663785794333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10312903854131540190903109 1933669472649663785794333)
      ·
        refine ⟨725126052243623919672875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1933669472649663785794333 725126052243623919672875)
        ·
          refine ⟨1087689078365435879509313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725126052243623919672875 1087689078365435879509313)
          ·
            refine ⟨815766808774076909631985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1087689078365435879509313 815766808774076909631985)
            ·
              refine ⟨611825106580557682223989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815766808774076909631985 611825106580557682223989)
              ·
                refine ⟨57358603741927282708499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 611825106580557682223989 57358603741927282708499)
                ·
                  rfl

theorem cell21_754012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 5].length) (baseStart_754012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754012 prefixEnd_754012 := by exact prefixLift 754012
  have htrace : WordTrace (prefixWord ++ tailWord_754012) baseStart_754012 baseEnd_754012 := by
    simpa [prefixWord, tailWord_754012, baseEnd_754012] using wordTrace_append hprefix tailTrace_754012
  have hstable : (prefixWord ++ tailWord_754012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754012).length < 2 ^ (prefixWord ++ tailWord_754012).sum := by decide
  have hdescent : baseEnd_754012 < baseStart_754012 := by decide
  rcases family_descends (prefixWord ++ tailWord_754012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754026 : List Nat := [3, 1, 3, 3, 1, 1, 3, 3, 3]
def baseStart_754026 : Nat := 118140960795 + 754026 * 2 ^ 59
def prefixEnd_754026 : Nat := 4983230072969 + 3 ^ 40 * 754026 * 2
def baseEnd_754026 : Nat := 172079006216520934892135

theorem tailTrace_754026 : CollatzResearch.WordTrace tailWord_754026 prefixEnd_754026 172079006216520934892135 := by
  unfold tailWord_754026
  simp only [CollatzResearch.WordTrace]
  refine ⟨6875396891575013558354483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18334391710866702822278621 6875396891575013558354483)
  ·
    refine ⟨10313095337362520337531725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6875396891575013558354483 10313095337362520337531725)
    ·
      refine ⟨3867410751510945126574397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10313095337362520337531725 3867410751510945126574397)
      ·
        refine ⟨1450279031816604422465399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3867410751510945126574397 1450279031816604422465399)
        ·
          refine ⟨2175418547724906633698099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450279031816604422465399 2175418547724906633698099)
          ·
            refine ⟨3263127821587359950547149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175418547724906633698099 3263127821587359950547149)
            ·
              refine ⟨1223672933095259981455181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3263127821587359950547149 1223672933095259981455181)
              ·
                refine ⟨458877349910722493045693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1223672933095259981455181 458877349910722493045693)
                ·
                  refine ⟨172079006216520934892135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458877349910722493045693 172079006216520934892135)
                  ·
                    rfl

theorem cell21_754026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_754026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754026 prefixEnd_754026 := by exact prefixLift 754026
  have htrace : WordTrace (prefixWord ++ tailWord_754026) baseStart_754026 baseEnd_754026 := by
    simpa [prefixWord, tailWord_754026, baseEnd_754026] using wordTrace_append hprefix tailTrace_754026
  have hstable : (prefixWord ++ tailWord_754026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754026).length < 2 ^ (prefixWord ++ tailWord_754026).sum := by decide
  have hdescent : baseEnd_754026 < baseStart_754026 := by decide
  rcases family_descends (prefixWord ++ tailWord_754026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754037 : List Nat := [1, 3, 4, 1, 2, 1, 9]
def baseStart_754037 : Nat := 118140960795 + 754037 * 2 ^ 59
def prefixEnd_754037 : Nat := 4983230072969 + 3 ^ 40 * 754037 * 2
def baseEnd_754037 : Nat := 19120168507376373356531

theorem tailTrace_754037 : CollatzResearch.WordTrace tailWord_754037 prefixEnd_754037 19120168507376373356531 := by
  unfold tailWord_754037
  simp only [CollatzResearch.WordTrace]
  refine ⟨27501988769260203112068365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18334659179506802074712243 27501988769260203112068365)
  ·
    refine ⟨10313245788472576167025637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27501988769260203112068365 10313245788472576167025637)
    ·
      refine ⟨1933733585338608031317307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10313245788472576167025637 1933733585338608031317307)
      ·
        refine ⟨2900600378007912046975961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1933733585338608031317307 2900600378007912046975961)
        ·
          refine ⟨2175450283505934035231971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2900600378007912046975961 2175450283505934035231971)
          ·
            refine ⟨3263175425258901052847957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175450283505934035231971 3263175425258901052847957)
            ·
              refine ⟨19120168507376373356531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3263175425258901052847957 19120168507376373356531)
              ·
                rfl

theorem cell21_754037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 9].length) (baseStart_754037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754037 prefixEnd_754037 := by exact prefixLift 754037
  have htrace : WordTrace (prefixWord ++ tailWord_754037) baseStart_754037 baseEnd_754037 := by
    simpa [prefixWord, tailWord_754037, baseEnd_754037] using wordTrace_append hprefix tailTrace_754037
  have hstable : (prefixWord ++ tailWord_754037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754037).length < 2 ^ (prefixWord ++ tailWord_754037).sum := by decide
  have hdescent : baseEnd_754037 < baseStart_754037 := by decide
  rcases family_descends (prefixWord ++ tailWord_754037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754172 : List Nat := [2, 2, 2, 1, 2, 1, 1, 10]
def baseStart_754172 : Nat := 118140960795 + 754172 * 2 ^ 59
def prefixEnd_754172 : Nat := 4983230072969 + 3 ^ 40 * 754172 * 2
def baseEnd_754172 : Nat := 57370775135219041819501

theorem tailTrace_754172 : CollatzResearch.WordTrace tailWord_754172 prefixEnd_754172 57370775135219041819501 := by
  unfold tailWord_754172
  simp only [CollatzResearch.WordTrace]
  refine ⟨13753456311885560584116385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18337941749180747445488513 13753456311885560584116385)
  ·
    refine ⟨10315092233914170438087289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13753456311885560584116385 10315092233914170438087289)
    ·
      refine ⟨7736319175435627828565467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10315092233914170438087289 7736319175435627828565467)
      ·
        refine ⟨11604478763153441742848201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7736319175435627828565467 11604478763153441742848201)
        ·
          refine ⟨8703359072365081307136151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11604478763153441742848201 8703359072365081307136151)
          ·
            refine ⟨13055038608547621960704227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8703359072365081307136151 13055038608547621960704227)
            ·
              refine ⟨19582557912821432941056341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13055038608547621960704227 19582557912821432941056341)
              ·
                refine ⟨57370775135219041819501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19582557912821432941056341 57370775135219041819501)
                ·
                  rfl

theorem cell21_754172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_754172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754172 prefixEnd_754172 := by exact prefixLift 754172
  have htrace : WordTrace (prefixWord ++ tailWord_754172) baseStart_754172 baseEnd_754172 := by
    simpa [prefixWord, tailWord_754172, baseEnd_754172] using wordTrace_append hprefix tailTrace_754172
  have hstable : (prefixWord ++ tailWord_754172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754172).length < 2 ^ (prefixWord ++ tailWord_754172).sum := by decide
  have hdescent : baseEnd_754172 < baseStart_754172 := by decide
  rcases family_descends (prefixWord ++ tailWord_754172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754175 : List Nat := [1, 1, 2, 2, 1, 2, 7, 1, 4]
def baseStart_754175 : Nat := 118140960795 + 754175 * 2 ^ 59
def prefixEnd_754175 : Nat := 4983230072969 + 3 ^ 40 * 754175 * 2
def baseEnd_754175 : Nat := 172113010046529786908497

theorem tailTrace_754175 : CollatzResearch.WordTrace tailWord_754175 prefixEnd_754175 172113010046529786908497 := by
  unfold tailWord_754175
  simp only [CollatzResearch.WordTrace]
  refine ⟨27507022042760252680591979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18338014695173501787061319 27507022042760252680591979)
  ·
    refine ⟨41260533064140379020887969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27507022042760252680591979 41260533064140379020887969)
    ·
      refine ⟨30945399798105284265665977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41260533064140379020887969 30945399798105284265665977)
      ·
        refine ⟨23209049848578963199249483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30945399798105284265665977 23209049848578963199249483)
        ·
          refine ⟨34813574772868444798874225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23209049848578963199249483 34813574772868444798874225)
          ·
            refine ⟨26110181079651333599155669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34813574772868444798874225 26110181079651333599155669)
            ·
              refine ⟨611957369054328131230211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26110181079651333599155669 611957369054328131230211)
              ·
                refine ⟨917936053581492196845317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611957369054328131230211 917936053581492196845317)
                ·
                  refine ⟨172113010046529786908497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 917936053581492196845317 172113010046529786908497)
                  ·
                    rfl

theorem cell21_754175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 4].length) (baseStart_754175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754175 prefixEnd_754175 := by exact prefixLift 754175
  have htrace : WordTrace (prefixWord ++ tailWord_754175) baseStart_754175 baseEnd_754175 := by
    simpa [prefixWord, tailWord_754175, baseEnd_754175] using wordTrace_append hprefix tailTrace_754175
  have hstable : (prefixWord ++ tailWord_754175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754175).length < 2 ^ (prefixWord ++ tailWord_754175).sum := by decide
  have hdescent : baseEnd_754175 < baseStart_754175 := by decide
  rcases family_descends (prefixWord ++ tailWord_754175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754220 : List Nat := [2, 2, 1, 1, 1, 2, 1, 8, 3]
def baseStart_754220 : Nat := 118140960795 + 754220 * 2 ^ 59
def prefixEnd_754220 : Nat := 4983230072969 + 3 ^ 40 * 754220 * 2
def baseEnd_754220 : Nat := 172123279659619708658405

theorem tailTrace_754220 : CollatzResearch.WordTrace tailWord_754220 prefixEnd_754220 172123279659619708658405 := by
  unfold tailWord_754220
  simp only [CollatzResearch.WordTrace]
  refine ⟨13754331663798612682990057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18339108885064816910653409 13754331663798612682990057)
  ·
    refine ⟨10315748747848959512242543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13754331663798612682990057 10315748747848959512242543)
    ·
      refine ⟨15473623121773439268363815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10315748747848959512242543 15473623121773439268363815)
      ·
        refine ⟨23210434682660158902545723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15473623121773439268363815 23210434682660158902545723)
        ·
          refine ⟨34815652023990238353818585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23210434682660158902545723 34815652023990238353818585)
          ·
            refine ⟨26111739017992678765363939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34815652023990238353818585 26111739017992678765363939)
            ·
              refine ⟨39167608526989018148045909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26111739017992678765363939 39167608526989018148045909)
              ·
                refine ⟨458995412425652556422413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 39167608526989018148045909 458995412425652556422413)
                ·
                  refine ⟨172123279659619708658405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458995412425652556422413 172123279659619708658405)
                  ·
                    rfl

theorem cell21_754220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_754220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754220 prefixEnd_754220 := by exact prefixLift 754220
  have htrace : WordTrace (prefixWord ++ tailWord_754220) baseStart_754220 baseEnd_754220 := by
    simpa [prefixWord, tailWord_754220, baseEnd_754220] using wordTrace_append hprefix tailTrace_754220
  have hstable : (prefixWord ++ tailWord_754220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754220).length < 2 ^ (prefixWord ++ tailWord_754220).sum := by decide
  have hdescent : baseEnd_754220 < baseStart_754220 := by decide
  rcases family_descends (prefixWord ++ tailWord_754220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754268 : List Nat := [2, 2, 4, 1, 3, 1, 2, 2, 4]
def baseStart_754268 : Nat := 118140960795 + 754268 * 2 ^ 59
def prefixEnd_754268 : Nat := 4983230072969 + 3 ^ 40 * 754268 * 2
def baseEnd_754268 : Nat := 172134233913582291858307

theorem tailTrace_754268 : CollatzResearch.WordTrace tailWord_754268 prefixEnd_754268 172134233913582291858307 := by
  unfold tailWord_754268
  simp only [CollatzResearch.WordTrace]
  refine ⟨13755207015711664781863729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18340276020948886375818305 13755207015711664781863729)
  ·
    refine ⟨10316405261783748586397797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13755207015711664781863729 10316405261783748586397797)
    ·
      refine ⟨1934325986584452859949587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10316405261783748586397797 1934325986584452859949587)
      ·
        refine ⟨2901488979876679289924381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1934325986584452859949587 2901488979876679289924381)
        ·
          refine ⟨1088058367453754733721643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2901488979876679289924381 1088058367453754733721643)
          ·
            refine ⟨1632087551180632100582465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088058367453754733721643 1632087551180632100582465)
            ·
              refine ⟨1224065663385474075436849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1632087551180632100582465 1224065663385474075436849)
              ·
                refine ⟨918049247539105556577637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224065663385474075436849 918049247539105556577637)
                ·
                  refine ⟨172134233913582291858307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 918049247539105556577637 172134233913582291858307)
                  ·
                    rfl

theorem cell21_754268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_754268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754268 prefixEnd_754268 := by exact prefixLift 754268
  have htrace : WordTrace (prefixWord ++ tailWord_754268) baseStart_754268 baseEnd_754268 := by
    simpa [prefixWord, tailWord_754268, baseEnd_754268] using wordTrace_append hprefix tailTrace_754268
  have hstable : (prefixWord ++ tailWord_754268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754268).length < 2 ^ (prefixWord ++ tailWord_754268).sum := by decide
  have hdescent : baseEnd_754268 < baseStart_754268 := by decide
  rcases family_descends (prefixWord ++ tailWord_754268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754279 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 5]
def baseStart_754279 : Nat := 118140960795 + 754279 * 2 ^ 59
def prefixEnd_754279 : Nat := 4983230072969 + 3 ^ 40 * 754279 * 2
def baseEnd_754279 : Nat := 172136744263448717174951

theorem tailTrace_754279 : CollatzResearch.WordTrace tailWord_754279 prefixEnd_754279 172136744263448717174951 := by
  unfold tailWord_754279
  simp only [CollatzResearch.WordTrace]
  refine ⟨27510815234383478442377891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18340543489588985628251927 27510815234383478442377891)
  ·
    refine ⟨41266222851575217663566837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27510815234383478442377891 41266222851575217663566837)
    ·
      refine ⟨3868708392335176655959391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41266222851575217663566837 3868708392335176655959391)
      ·
        refine ⟨5803062588502764983939087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868708392335176655959391 5803062588502764983939087)
        ·
          refine ⟨8704593882754147475908631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5803062588502764983939087 8704593882754147475908631)
          ·
            refine ⟨13056890824131221213862947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8704593882754147475908631 13056890824131221213862947)
            ·
              refine ⟨19585336236196831820794421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13056890824131221213862947 19585336236196831820794421)
              ·
                refine ⟨1836125272143452983199477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19585336236196831820794421 1836125272143452983199477)
                ·
                  refine ⟨172136744263448717174951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1836125272143452983199477 172136744263448717174951)
                  ·
                    rfl

theorem cell21_754279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 5].length) (baseStart_754279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754279 prefixEnd_754279 := by exact prefixLift 754279
  have htrace : WordTrace (prefixWord ++ tailWord_754279) baseStart_754279 baseEnd_754279 := by
    simpa [prefixWord, tailWord_754279, baseEnd_754279] using wordTrace_append hprefix tailTrace_754279
  have hstable : (prefixWord ++ tailWord_754279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754279).length < 2 ^ (prefixWord ++ tailWord_754279).sum := by decide
  have hdescent : baseEnd_754279 < baseStart_754279 := by decide
  rcases family_descends (prefixWord ++ tailWord_754279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754355 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 5]
def baseStart_754355 : Nat := 118140960795 + 754355 * 2 ^ 59
def prefixEnd_754355 : Nat := 4983230072969 + 3 ^ 40 * 754355 * 2
def baseEnd_754355 : Nat := 172154088498889473908129

theorem tailTrace_754355 : CollatzResearch.WordTrace tailWord_754355 prefixEnd_754355 172154088498889473908129 := by
  unfold tailWord_754355
  simp only [CollatzResearch.WordTrace]
  refine ⟨27513587182108143422144519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18342391454738762281429679 27513587182108143422144519)
  ·
    refine ⟨41270380773162215133216779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27513587182108143422144519 41270380773162215133216779)
    ·
      refine ⟨61905571159743322699825169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41270380773162215133216779 61905571159743322699825169)
      ·
        refine ⟨46429178369807492024868877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61905571159743322699825169 46429178369807492024868877)
        ·
          refine ⟨17410941888677809509325829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46429178369807492024868877 17410941888677809509325829)
          ·
            refine ⟨3264551604127089282998593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17410941888677809509325829 3264551604127089282998593)
            ·
              refine ⟨2448413703095316962248945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3264551604127089282998593 2448413703095316962248945)
              ·
                refine ⟨1836310277321487721686709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2448413703095316962248945 1836310277321487721686709)
                ·
                  refine ⟨172154088498889473908129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1836310277321487721686709 172154088498889473908129)
                  ·
                    rfl

theorem cell21_754355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 5].length) (baseStart_754355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754355 prefixEnd_754355 := by exact prefixLift 754355
  have htrace : WordTrace (prefixWord ++ tailWord_754355) baseStart_754355 baseEnd_754355 := by
    simpa [prefixWord, tailWord_754355, baseEnd_754355] using wordTrace_append hprefix tailTrace_754355
  have hstable : (prefixWord ++ tailWord_754355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754355).length < 2 ^ (prefixWord ++ tailWord_754355).sum := by decide
  have hdescent : baseEnd_754355 < baseStart_754355 := by decide
  rcases family_descends (prefixWord ++ tailWord_754355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754403 : List Nat := [1, 1, 1, 7, 1, 2, 1, 3, 4]
def baseStart_754403 : Nat := 118140960795 + 754403 * 2 ^ 59
def prefixEnd_754403 : Nat := 4983230072969 + 3 ^ 40 * 754403 * 2
def baseEnd_754403 : Nat := 172165042752852057108031

theorem tailTrace_754403 : CollatzResearch.WordTrace tailWord_754403 prefixEnd_754403 172165042752852057108031 := by
  unfold tailWord_754403
  simp only [CollatzResearch.WordTrace]
  refine ⟨27515337885934247619891863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18343558590622831746594575 27515337885934247619891863)
  ·
    refine ⟨41273006828901371429837795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27515337885934247619891863 41273006828901371429837795)
    ·
      refine ⟨61909510243352057144756693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41273006828901371429837795 61909510243352057144756693)
      ·
        refine ⟨1451004146328563839330235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 61909510243352057144756693 1451004146328563839330235)
        ·
          refine ⟨2176506219492845758995353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451004146328563839330235 2176506219492845758995353)
          ·
            refine ⟨1632379664619634319246515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2176506219492845758995353 1632379664619634319246515)
            ·
              refine ⟨2448569496929451478869773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632379664619634319246515 2448569496929451478869773)
              ·
                refine ⟨918213561348544304576165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2448569496929451478869773 918213561348544304576165)
                ·
                  refine ⟨172165042752852057108031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 918213561348544304576165 172165042752852057108031)
                  ·
                    rfl

theorem cell21_754403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 4].length) (baseStart_754403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754403 prefixEnd_754403 := by exact prefixLift 754403
  have htrace : WordTrace (prefixWord ++ tailWord_754403) baseStart_754403 baseEnd_754403 := by
    simpa [prefixWord, tailWord_754403, baseEnd_754403] using wordTrace_append hprefix tailTrace_754403
  have hstable : (prefixWord ++ tailWord_754403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754403).length < 2 ^ (prefixWord ++ tailWord_754403).sum := by decide
  have hdescent : baseEnd_754403 < baseStart_754403 := by decide
  rcases family_descends (prefixWord ++ tailWord_754403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754493 : List Nat := [1, 4, 1, 4, 2, 1, 8]
def baseStart_754493 : Nat := 118140960795 + 754493 * 2 ^ 59
def prefixEnd_754493 : Nat := 4983230072969 + 3 ^ 40 * 754493 * 2
def baseEnd_754493 : Nat := 19131731331003544511983

theorem tailTrace_754493 : CollatzResearch.WordTrace tailWord_754493 prefixEnd_754493 19131731331003544511983 := by
  unfold tailWord_754493
  simp only [CollatzResearch.WordTrace]
  refine ⟨27518620455608192990668133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18345746970405461993778755 27518620455608192990668133)
  ·
    refine ⟨5159741335426536185750275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27518620455608192990668133 5159741335426536185750275)
    ·
      refine ⟨7739612003139804278625413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5159741335426536185750275 7739612003139804278625413)
      ·
        refine ⟨1451177250588713302242265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7739612003139804278625413 1451177250588713302242265)
        ·
          refine ⟨1088382937941534976681699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1451177250588713302242265 1088382937941534976681699)
          ·
            refine ⟨1632574406912302465022549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088382937941534976681699 1632574406912302465022549)
            ·
              refine ⟨19131731331003544511983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1632574406912302465022549 19131731331003544511983)
              ·
                rfl

theorem cell21_754493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 8].length) (baseStart_754493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754493 prefixEnd_754493 := by exact prefixLift 754493
  have htrace : WordTrace (prefixWord ++ tailWord_754493) baseStart_754493 baseEnd_754493 := by
    simpa [prefixWord, tailWord_754493, baseEnd_754493] using wordTrace_append hprefix tailTrace_754493
  have hstable : (prefixWord ++ tailWord_754493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754493).length < 2 ^ (prefixWord ++ tailWord_754493).sum := by decide
  have hdescent : baseEnd_754493 < baseStart_754493 := by decide
  rcases family_descends (prefixWord ++ tailWord_754493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754524 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 5]
def baseStart_754524 : Nat := 118140960795 + 754524 * 2 ^ 59
def prefixEnd_754524 : Nat := 4983230072969 + 3 ^ 40 * 754524 * 2
def baseEnd_754524 : Nat := 172192656601382735591117

theorem tailTrace_754524 : CollatzResearch.WordTrace tailWord_754524 prefixEnd_754524 172192656601382735591117 := by
  unfold tailWord_754524
  simp only [CollatzResearch.WordTrace]
  refine ⟨13759875559247942642523313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18346500745663923523364417 13759875559247942642523313)
  ·
    refine ⟨10319906669435956981892485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13759875559247942642523313 10319906669435956981892485)
    ·
      refine ⟨1934982500519241934104841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10319906669435956981892485 1934982500519241934104841)
      ·
        refine ⟨1451236875389431450578631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1934982500519241934104841 1451236875389431450578631)
        ·
          refine ⟨2176855313084147175867947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451236875389431450578631 2176855313084147175867947)
          ·
            refine ⟨3265282969626220763801921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176855313084147175867947 3265282969626220763801921)
            ·
              refine ⟨2448962227219665572851441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3265282969626220763801921 2448962227219665572851441)
              ·
                refine ⟨1836721670414749179638581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2448962227219665572851441 1836721670414749179638581)
                ·
                  refine ⟨172192656601382735591117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1836721670414749179638581 172192656601382735591117)
                  ·
                    rfl

theorem cell21_754524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_754524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754524 prefixEnd_754524 := by exact prefixLift 754524
  have htrace : WordTrace (prefixWord ++ tailWord_754524) baseStart_754524 baseEnd_754524 := by
    simpa [prefixWord, tailWord_754524, baseEnd_754524] using wordTrace_append hprefix tailTrace_754524
  have hstable : (prefixWord ++ tailWord_754524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754524).length < 2 ^ (prefixWord ++ tailWord_754524).sum := by decide
  have hdescent : baseEnd_754524 < baseStart_754524 := by decide
  rcases family_descends (prefixWord ++ tailWord_754524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754558 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_754558 : Nat := 118140960795 + 754558 * 2 ^ 59
def prefixEnd_754558 : Nat := 4983230072969 + 3 ^ 40 * 754558 * 2
def baseEnd_754558 : Nat := 172200415864606232024381

theorem tailTrace_754558 : CollatzResearch.WordTrace tailWord_754558 prefixEnd_754558 172200415864606232024381 := by
  unfold tailWord_754558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3440123900046588636473041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18347327466915139394522885 3440123900046588636473041)
  ·
    refine ⟨2580092925034941477354781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3440123900046588636473041 2580092925034941477354781)
    ·
      refine ⟨967534846888103054008043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2580092925034941477354781 967534846888103054008043)
      ·
        refine ⟨1451302270332154581012065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 967534846888103054008043 1451302270332154581012065)
        ·
          refine ⟨1088476702749115935759049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1451302270332154581012065 1088476702749115935759049)
          ·
            refine ⟨816357527061836951819287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1088476702749115935759049 816357527061836951819287)
            ·
              refine ⟨1224536290592755427728931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816357527061836951819287 1224536290592755427728931)
              ·
                refine ⟨1836804435889133141593397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1224536290592755427728931 1836804435889133141593397)
                ·
                  refine ⟨172200415864606232024381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1836804435889133141593397 172200415864606232024381)
                  ·
                    rfl

theorem cell21_754558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_754558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754558 prefixEnd_754558 := by exact prefixLift 754558
  have htrace : WordTrace (prefixWord ++ tailWord_754558) baseStart_754558 baseEnd_754558 := by
    simpa [prefixWord, tailWord_754558, baseEnd_754558] using wordTrace_append hprefix tailTrace_754558
  have hstable : (prefixWord ++ tailWord_754558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754558).length < 2 ^ (prefixWord ++ tailWord_754558).sum := by decide
  have hdescent : baseEnd_754558 < baseStart_754558 := by decide
  rcases family_descends (prefixWord ++ tailWord_754558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754617 : List Nat := [1, 2, 1, 4, 2, 2, 4, 2, 3]
def baseStart_754617 : Nat := 118140960795 + 754617 * 2 ^ 59
def prefixEnd_754617 : Nat := 4983230072969 + 3 ^ 40 * 754617 * 2
def baseEnd_754617 : Nat := 172213880468435240540927

theorem tailTrace_754617 : CollatzResearch.WordTrace tailWord_754617 prefixEnd_754617 172213880468435240540927 := by
  unfold tailWord_754617
  simp only [CollatzResearch.WordTrace]
  refine ⟨27523143107158962168182105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18348762071439308112121403 27523143107158962168182105)
  ·
    refine ⟨20642357330369221626136579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27523143107158962168182105 20642357330369221626136579)
    ·
      refine ⟨30963535995553832439204869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20642357330369221626136579 30963535995553832439204869)
      ·
        refine ⟨5805662999166343582350913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30963535995553832439204869 5805662999166343582350913)
        ·
          refine ⟨4354247249374757686763185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5805662999166343582350913 4354247249374757686763185)
          ·
            refine ⟨3265685437031068265072389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4354247249374757686763185 3265685437031068265072389)
            ·
              refine ⟨612316019443325299701073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3265685437031068265072389 612316019443325299701073)
              ·
                refine ⟨459237014582493974775805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612316019443325299701073 459237014582493974775805)
                ·
                  refine ⟨172213880468435240540927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459237014582493974775805 172213880468435240540927)
                  ·
                    rfl

theorem cell21_754617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 3].length) (baseStart_754617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754617 prefixEnd_754617 := by exact prefixLift 754617
  have htrace : WordTrace (prefixWord ++ tailWord_754617) baseStart_754617 baseEnd_754617 := by
    simpa [prefixWord, tailWord_754617, baseEnd_754617] using wordTrace_append hprefix tailTrace_754617
  have hstable : (prefixWord ++ tailWord_754617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754617).length < 2 ^ (prefixWord ++ tailWord_754617).sum := by decide
  have hdescent : baseEnd_754617 < baseStart_754617 := by decide
  rcases family_descends (prefixWord ++ tailWord_754617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754786 : List Nat := [3, 3, 2, 2, 1, 1, 4, 2, 3]
def baseStart_754786 : Nat := 118140960795 + 754786 * 2 ^ 59
def prefixEnd_754786 : Nat := 4983230072969 + 3 ^ 40 * 754786 * 2
def baseEnd_754786 : Nat := 172252448570928502223915

theorem tailTrace_754786 : CollatzResearch.WordTrace tailWord_754786 prefixEnd_754786 172252448570928502223915 := by
  unfold tailWord_754786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6882326760886676007771053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18352871362364469354056141 6882326760886676007771053)
  ·
    refine ⟨2580872535332503502914145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6882326760886676007771053 2580872535332503502914145)
    ·
      refine ⟨1935654401499377627185609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2580872535332503502914145 1935654401499377627185609)
      ·
        refine ⟨1451740801124533220389207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1935654401499377627185609 1451740801124533220389207)
        ·
          refine ⟨2177611201686799830583811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451740801124533220389207 2177611201686799830583811)
          ·
            refine ⟨3266416802530199745875717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177611201686799830583811 3266416802530199745875717)
            ·
              refine ⟨612453150474412452351697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3266416802530199745875717 612453150474412452351697)
              ·
                refine ⟨459339862855809339263773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612453150474412452351697 459339862855809339263773)
                ·
                  refine ⟨172252448570928502223915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459339862855809339263773 172252448570928502223915)
                  ·
                    rfl

theorem cell21_754786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_754786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754786 prefixEnd_754786 := by exact prefixLift 754786
  have htrace : WordTrace (prefixWord ++ tailWord_754786) baseStart_754786 baseEnd_754786 := by
    simpa [prefixWord, tailWord_754786, baseEnd_754786] using wordTrace_append hprefix tailTrace_754786
  have hstable : (prefixWord ++ tailWord_754786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754786).length < 2 ^ (prefixWord ++ tailWord_754786).sum := by decide
  have hdescent : baseEnd_754786 < baseStart_754786 := by decide
  rcases family_descends (prefixWord ++ tailWord_754786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754797 : List Nat := [1, 5, 1, 1, 2, 4, 1, 6]
def baseStart_754797 : Nat := 118140960795 + 754797 * 2 ^ 59
def prefixEnd_754797 : Nat := 4983230072969 + 3 ^ 40 * 754797 * 2
def baseEnd_754797 : Nat := 57418319640264975846853

theorem tailTrace_754797 : CollatzResearch.WordTrace tailWord_754797 prefixEnd_754797 57418319640264975846853 := by
  unfold tailWord_754797
  simp only [CollatzResearch.WordTrace]
  refine ⟨27529708246506852909734645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18353138831004568606489763 27529708246506852909734645)
  ·
    refine ⟨2580910148110017460287623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27529708246506852909734645 2580910148110017460287623)
    ·
      refine ⟨3871365222165026190431435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2580910148110017460287623 3871365222165026190431435)
      ·
        refine ⟨5807047833247539285647153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3871365222165026190431435 5807047833247539285647153)
        ·
          refine ⟨4355285874935654464235365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5807047833247539285647153 4355285874935654464235365)
          ·
            refine ⟨816616101550435212044131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4355285874935654464235365 816616101550435212044131)
            ·
              refine ⟨1224924152325652818066197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816616101550435212044131 1224924152325652818066197)
              ·
                refine ⟨57418319640264975846853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1224924152325652818066197 57418319640264975846853)
                ·
                  rfl

theorem cell21_754797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 6].length) (baseStart_754797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754797 prefixEnd_754797 := by exact prefixLift 754797
  have htrace : WordTrace (prefixWord ++ tailWord_754797) baseStart_754797 baseEnd_754797 := by
    simpa [prefixWord, tailWord_754797, baseEnd_754797] using wordTrace_append hprefix tailTrace_754797
  have hstable : (prefixWord ++ tailWord_754797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754797).length < 2 ^ (prefixWord ++ tailWord_754797).sum := by decide
  have hdescent : baseEnd_754797 < baseStart_754797 := by decide
  rcases family_descends (prefixWord ++ tailWord_754797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754842 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_754842 : Nat := 118140960795 + 754842 * 2 ^ 59
def prefixEnd_754842 : Nat := 4983230072969 + 3 ^ 40 * 754842 * 2
def baseEnd_754842 : Nat := 172265228533884849290467

theorem tailTrace_754842 : CollatzResearch.WordTrace tailWord_754842 prefixEnd_754842 172265228533884849290467 := by
  unfold tailWord_754842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6882837382835956398780695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18354233020895883730081853 6882837382835956398780695)
  ·
    refine ⟨10324256074253934598171043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6882837382835956398780695 10324256074253934598171043)
    ·
      refine ⟨15486384111380901897256565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10324256074253934598171043 15486384111380901897256565)
      ·
        refine ⟨1451848510441959552867803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15486384111380901897256565 1451848510441959552867803)
        ·
          refine ⟨2177772765662939329301705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451848510441959552867803 2177772765662939329301705)
          ·
            refine ⟨1633329574247204496976279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2177772765662939329301705 1633329574247204496976279)
            ·
              refine ⟨2449994361370806745464419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633329574247204496976279 2449994361370806745464419)
              ·
                refine ⟨3674991542056210118196629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449994361370806745464419 3674991542056210118196629)
                ·
                  refine ⟨172265228533884849290467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3674991542056210118196629 172265228533884849290467)
                  ·
                    rfl

theorem cell21_754842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_754842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754842 prefixEnd_754842 := by exact prefixLift 754842
  have htrace : WordTrace (prefixWord ++ tailWord_754842) baseStart_754842 baseEnd_754842 := by
    simpa [prefixWord, tailWord_754842, baseEnd_754842] using wordTrace_append hprefix tailTrace_754842
  have hstable : (prefixWord ++ tailWord_754842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754842).length < 2 ^ (prefixWord ++ tailWord_754842).sum := by decide
  have hdescent : baseEnd_754842 < baseStart_754842 := by decide
  rcases family_descends (prefixWord ++ tailWord_754842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754873 : List Nat := [1, 2, 1, 4, 1, 5, 2, 5]
def baseStart_754873 : Nat := 118140960795 + 754873 * 2 ^ 59
def prefixEnd_754873 : Nat := 4983230072969 + 3 ^ 40 * 754873 * 2
def baseEnd_754873 : Nat := 57424101052078561424579

theorem tailTrace_754873 : CollatzResearch.WordTrace tailWord_754873 prefixEnd_754873 57424101052078561424579 := by
  unfold tailWord_754873
  simp only [CollatzResearch.WordTrace]
  refine ⟨27532480194231517889501273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18354986796154345259667515 27532480194231517889501273)
  ·
    refine ⟨20649360145673638417125955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27532480194231517889501273 20649360145673638417125955)
    ·
      refine ⟨30974040218510457625688933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20649360145673638417125955 30974040218510457625688933)
      ·
        refine ⟨5807632540970710804816675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30974040218510457625688933 5807632540970710804816675)
        ·
          refine ⟨8711448811456066207225013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5807632540970710804816675 8711448811456066207225013)
          ·
            refine ⟨816698326074006206927345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8711448811456066207225013 816698326074006206927345)
            ·
              refine ⟨612523744555504655195509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816698326074006206927345 612523744555504655195509)
              ·
                refine ⟨57424101052078561424579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 612523744555504655195509 57424101052078561424579)
                ·
                  rfl

theorem cell21_754873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 5].length) (baseStart_754873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754873 prefixEnd_754873 := by exact prefixLift 754873
  have htrace : WordTrace (prefixWord ++ tailWord_754873) baseStart_754873 baseEnd_754873 := by
    simpa [prefixWord, tailWord_754873, baseEnd_754873] using wordTrace_append hprefix tailTrace_754873
  have hstable : (prefixWord ++ tailWord_754873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754873).length < 2 ^ (prefixWord ++ tailWord_754873).sum := by decide
  have hdescent : baseEnd_754873 < baseStart_754873 := by decide
  rcases family_descends (prefixWord ++ tailWord_754873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754904 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 5]
def baseStart_754904 : Nat := 118140960795 + 754904 * 2 ^ 59
def prefixEnd_754904 : Nat := 4983230072969 + 3 ^ 40 * 754904 * 2
def baseEnd_754904 : Nat := 172279377778586519257007

theorem tailTrace_754904 : CollatzResearch.WordTrace tailWord_754904 prefixEnd_754904 172279377778586519257007 := by
  unfold tailWord_754904
  simp only [CollatzResearch.WordTrace]
  refine ⟨13766805428559605091939883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18355740571412806789253177 13766805428559605091939883)
  ·
    refine ⟨20650208142839407637909825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13766805428559605091939883 20650208142839407637909825)
    ·
      refine ⟨15487656107129555728432369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20650208142839407637909825 15487656107129555728432369)
      ·
        refine ⟨11615742080347166796324277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15487656107129555728432369 11615742080347166796324277)
        ·
          refine ⟨1088975820032546887155401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11615742080347166796324277 1088975820032546887155401)
          ·
            refine ⟨816731865024410165366551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1088975820032546887155401 816731865024410165366551)
            ·
              refine ⟨1225097797536615248049827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816731865024410165366551 1225097797536615248049827)
              ·
                refine ⟨1837646696304922872074741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225097797536615248049827 1837646696304922872074741)
                ·
                  refine ⟨172279377778586519257007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1837646696304922872074741 172279377778586519257007)
                  ·
                    rfl

theorem cell21_754904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_754904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754904 prefixEnd_754904 := by exact prefixLift 754904
  have htrace : WordTrace (prefixWord ++ tailWord_754904) baseStart_754904 baseEnd_754904 := by
    simpa [prefixWord, tailWord_754904, baseEnd_754904] using wordTrace_append hprefix tailTrace_754904
  have hstable : (prefixWord ++ tailWord_754904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754904).length < 2 ^ (prefixWord ++ tailWord_754904).sum := by decide
  have hdescent : baseEnd_754904 < baseStart_754904 := by decide
  rcases family_descends (prefixWord ++ tailWord_754904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754960 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 12]
def baseStart_754960 : Nat := 118140960795 + 754960 * 2 ^ 59
def prefixEnd_754960 : Nat := 4983230072969 + 3 ^ 40 * 754960 * 2
def baseEnd_754960 : Nat := 172292157741542866323559

theorem tailTrace_754960 : CollatzResearch.WordTrace tailWord_754960 prefixEnd_754960 172292157741542866323559 := by
  unfold tailWord_754960
  simp only [CollatzResearch.WordTrace]
  refine ⟨13767826672458165873959167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18357102229944221165278889 13767826672458165873959167)
  ·
    refine ⟨20651740008687248810938751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13767826672458165873959167 20651740008687248810938751)
    ·
      refine ⟨30977610013030873216408127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20651740008687248810938751 30977610013030873216408127)
      ·
        refine ⟨46466415019546309824612191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30977610013030873216408127 46466415019546309824612191)
        ·
          refine ⟨69699622529319464736918287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46466415019546309824612191 69699622529319464736918287)
          ·
            refine ⟨104549433793979197105377431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69699622529319464736918287 104549433793979197105377431)
            ·
              refine ⟨156824150690968795658066147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104549433793979197105377431 156824150690968795658066147)
              ·
                refine ⟨235236226036453193487099221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156824150690968795658066147 235236226036453193487099221)
                ·
                  refine ⟨172292157741542866323559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 235236226036453193487099221 172292157741542866323559)
                  ·
                    rfl

theorem cell21_754960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_754960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_754960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_754960 prefixEnd_754960 := by exact prefixLift 754960
  have htrace : WordTrace (prefixWord ++ tailWord_754960) baseStart_754960 baseEnd_754960 := by
    simpa [prefixWord, tailWord_754960, baseEnd_754960] using wordTrace_append hprefix tailTrace_754960
  have hstable : (prefixWord ++ tailWord_754960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754960).length < 2 ^ (prefixWord ++ tailWord_754960).sum := by decide
  have hdescent : baseEnd_754960 < baseStart_754960 := by decide
  rcases family_descends (prefixWord ++ tailWord_754960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755014 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_755014 : Nat := 118140960795 + 755014 * 2 ^ 59
def prefixEnd_755014 : Nat := 4983230072969 + 3 ^ 40 * 755014 * 2
def baseEnd_755014 : Nat := 172304481277250772423449

theorem tailTrace_755014 : CollatzResearch.WordTrace tailWord_755014 prefixEnd_755014 172304481277250772423449 := by
  unfold tailWord_755014
  simp only [CollatzResearch.WordTrace]
  refine ⟨860550715210021842824503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18358415257813799313589397 860550715210021842824503)
  ·
    refine ⟨1290826072815032764236755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 860550715210021842824503 1290826072815032764236755)
    ·
      refine ⟨1936239109222549146355133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1290826072815032764236755 1936239109222549146355133)
      ·
        refine ⟨726089665958455929883175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1936239109222549146355133 726089665958455929883175)
        ·
          refine ⟨1089134498937683894824763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726089665958455929883175 1089134498937683894824763)
          ·
            refine ⟨1633701748406525842237145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089134498937683894824763 1633701748406525842237145)
            ·
              refine ⟨1225276311304894381677859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1633701748406525842237145 1225276311304894381677859)
              ·
                refine ⟨1837914466957341572516789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225276311304894381677859 1837914466957341572516789)
                ·
                  refine ⟨172304481277250772423449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1837914466957341572516789 172304481277250772423449)
                  ·
                    rfl

theorem cell21_755014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_755014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755014 prefixEnd_755014 := by exact prefixLift 755014
  have htrace : WordTrace (prefixWord ++ tailWord_755014) baseStart_755014 baseEnd_755014 := by
    simpa [prefixWord, tailWord_755014, baseEnd_755014] using wordTrace_append hprefix tailTrace_755014
  have hstable : (prefixWord ++ tailWord_755014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755014).length < 2 ^ (prefixWord ++ tailWord_755014).sum := by decide
  have hdescent : baseEnd_755014 < baseStart_755014 := by decide
  rcases family_descends (prefixWord ++ tailWord_755014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755053 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 6]
def baseStart_755053 : Nat := 118140960795 + 755053 * 2 ^ 59
def prefixEnd_755053 : Nat := 4983230072969 + 3 ^ 40 * 755053 * 2
def baseEnd_755053 : Nat := 172313381608595371273369

theorem tailTrace_755053 : CollatzResearch.WordTrace tailWord_755053 prefixEnd_755053 172313381608595371273369 := by
  unfold tailWord_755053
  simp only [CollatzResearch.WordTrace]
  refine ⟨27539045333579408631053813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18359363555719605754035875 27539045333579408631053813)
  ·
    refine ⟨2581785500023069559161295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27539045333579408631053813 2581785500023069559161295)
    ·
      refine ⟨3872678250034604338741943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2581785500023069559161295 3872678250034604338741943)
      ·
        refine ⟨5809017375051906508112915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3872678250034604338741943 5809017375051906508112915)
        ·
          refine ⟨8713526062577859762169373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5809017375051906508112915 8713526062577859762169373)
          ·
            refine ⟨3267572273466697410813515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8713526062577859762169373 3267572273466697410813515)
            ·
              refine ⟨4901358410200046116220273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3267572273466697410813515 4901358410200046116220273)
              ·
                refine ⟨3676018807650034587165205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4901358410200046116220273 3676018807650034587165205)
                ·
                  refine ⟨172313381608595371273369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3676018807650034587165205 172313381608595371273369)
                  ·
                    rfl

theorem cell21_755053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_755053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755053 prefixEnd_755053 := by exact prefixLift 755053
  have htrace : WordTrace (prefixWord ++ tailWord_755053) baseStart_755053 baseEnd_755053 := by
    simpa [prefixWord, tailWord_755053, baseEnd_755053] using wordTrace_append hprefix tailTrace_755053
  have hstable : (prefixWord ++ tailWord_755053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755053).length < 2 ^ (prefixWord ++ tailWord_755053).sum := by decide
  have hdescent : baseEnd_755053 < baseStart_755053 := by decide
  rcases family_descends (prefixWord ++ tailWord_755053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755073 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 5]
def baseStart_755073 : Nat := 118140960795 + 755073 * 2 ^ 59
def prefixEnd_755073 : Nat := 4983230072969 + 3 ^ 40 * 755073 * 2
def baseEnd_755073 : Nat := 172317945881079780939995

theorem tailTrace_755073 : CollatzResearch.WordTrace tailWord_755073 prefixEnd_755073 172317945881079780939995 := by
  unfold tailWord_755073
  simp only [CollatzResearch.WordTrace]
  refine ⟨27539774793506952046781873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18359849862337968031187915 27539774793506952046781873)
  ·
    refine ⟨20654831095130214035086405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27539774793506952046781873 20654831095130214035086405)
    ·
      refine ⟨3872780830336915131578701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20654831095130214035086405 3872780830336915131578701)
      ·
        refine ⟨1452292811376343174342013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3872780830336915131578701 1452292811376343174342013)
        ·
          refine ⟨544609804266128690378255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1452292811376343174342013 544609804266128690378255)
          ·
            refine ⟨816914706399193035567383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544609804266128690378255 816914706399193035567383)
            ·
              refine ⟨1225372059598789553351075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816914706399193035567383 1225372059598789553351075)
              ·
                refine ⟨1838058089398184330026613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225372059598789553351075 1838058089398184330026613)
                ·
                  refine ⟨172317945881079780939995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1838058089398184330026613 172317945881079780939995)
                  ·
                    rfl

theorem cell21_755073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 5].length) (baseStart_755073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755073 prefixEnd_755073 := by exact prefixLift 755073
  have htrace : WordTrace (prefixWord ++ tailWord_755073) baseStart_755073 baseEnd_755073 := by
    simpa [prefixWord, tailWord_755073, baseEnd_755073] using wordTrace_append hprefix tailTrace_755073
  have hstable : (prefixWord ++ tailWord_755073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755073).length < 2 ^ (prefixWord ++ tailWord_755073).sum := by decide
  have hdescent : baseEnd_755073 < baseStart_755073 := by decide
  rcases family_descends (prefixWord ++ tailWord_755073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755098 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_755098 : Nat := 118140960795 + 755098 * 2 ^ 59
def prefixEnd_755098 : Nat := 4983230072969 + 3 ^ 40 * 755098 * 2
def baseEnd_755098 : Nat := 172323651221685293023277

theorem tailTrace_755098 : CollatzResearch.WordTrace tailWord_755098 prefixEnd_755098 172323651221685293023277 := by
  unfold tailWord_755098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6885171654604095329110487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18360457745610920877627965 6885171654604095329110487)
  ·
    refine ⟨10327757481906142993665731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6885171654604095329110487 10327757481906142993665731)
    ·
      refine ⟨15491636222859214490498597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10327757481906142993665731 15491636222859214490498597)
      ·
        refine ⟨2904681791786102716968487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15491636222859214490498597 2904681791786102716968487)
        ·
          refine ⟨4357022687679154075452731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2904681791786102716968487 4357022687679154075452731)
          ·
            refine ⟨6535534031518731113179097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357022687679154075452731 6535534031518731113179097)
            ·
              refine ⟨4901650523639048334884323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6535534031518731113179097 4901650523639048334884323)
              ·
                refine ⟨7352475785458572502326485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4901650523639048334884323 7352475785458572502326485)
                ·
                  refine ⟨172323651221685293023277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7352475785458572502326485 172323651221685293023277)
                  ·
                    rfl

theorem cell21_755098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_755098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755098 prefixEnd_755098 := by exact prefixLift 755098
  have htrace : WordTrace (prefixWord ++ tailWord_755098) baseStart_755098 baseEnd_755098 := by
    simpa [prefixWord, tailWord_755098, baseEnd_755098] using wordTrace_append hprefix tailTrace_755098
  have hstable : (prefixWord ++ tailWord_755098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755098).length < 2 ^ (prefixWord ++ tailWord_755098).sum := by decide
  have hdescent : baseEnd_755098 < baseStart_755098 := by decide
  rcases family_descends (prefixWord ++ tailWord_755098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755219 : List Nat := [1, 1, 1, 2, 1, 7, 1, 7]
def baseStart_755219 : Nat := 118140960795 + 755219 * 2 ^ 59
def prefixEnd_755219 : Nat := 4983230072969 + 3 ^ 40 * 755219 * 2
def baseEnd_755219 : Nat := 57450421690071990502121

theorem tailTrace_755219 : CollatzResearch.WordTrace tailWord_755219 prefixEnd_755219 57450421690071990502121 := by
  unfold tailWord_755219
  simp only [CollatzResearch.WordTrace]
  refine ⟨27545099850978018981596711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18363399900652012654397807 27545099850978018981596711)
  ·
    refine ⟨41317649776467028472395067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27545099850978018981596711 41317649776467028472395067)
    ·
      refine ⟨61976474664700542708592601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41317649776467028472395067 61976474664700542708592601)
      ·
        refine ⟨46482355998525407031444451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61976474664700542708592601 46482355998525407031444451)
        ·
          refine ⟨69723533997788110547166677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46482355998525407031444451 69723533997788110547166677)
          ·
            refine ⟨1634145328073158840949219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 69723533997788110547166677 1634145328073158840949219)
            ·
              refine ⟨2451217992109738261423829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634145328073158840949219 2451217992109738261423829)
              ·
                refine ⟨57450421690071990502121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2451217992109738261423829 57450421690071990502121)
                ·
                  rfl

theorem cell21_755219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 7].length) (baseStart_755219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755219 prefixEnd_755219 := by exact prefixLift 755219
  have htrace : WordTrace (prefixWord ++ tailWord_755219) baseStart_755219 baseEnd_755219 := by
    simpa [prefixWord, tailWord_755219, baseEnd_755219] using wordTrace_append hprefix tailTrace_755219
  have hstable : (prefixWord ++ tailWord_755219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755219).length < 2 ^ (prefixWord ++ tailWord_755219).sum := by decide
  have hdescent : baseEnd_755219 < baseStart_755219 := by decide
  rcases family_descends (prefixWord ++ tailWord_755219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755301 : List Nat := [1, 3, 1, 3, 3, 3, 2, 2, 3]
def baseStart_755301 : Nat := 118140960795 + 755301 * 2 ^ 59
def prefixEnd_755301 : Nat := 4983230072969 + 3 ^ 40 * 755301 * 2
def baseEnd_755301 : Nat := 172369978587402051139529

theorem tailTrace_755301 : CollatzResearch.WordTrace tailWord_755301 prefixEnd_755301 172369978587402051139529 := by
  unfold tailWord_755301
  simp only [CollatzResearch.WordTrace]
  refine ⟨27548090636680946986081757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18365393757787297990721171 27548090636680946986081757)
  ·
    refine ⟨10330533988755355119780659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27548090636680946986081757 10330533988755355119780659)
    ·
      refine ⟨15495800983133032679670989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10330533988755355119780659 15495800983133032679670989)
      ·
        refine ⟨5810925368674887254876621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15495800983133032679670989 5810925368674887254876621)
        ·
          refine ⟨2179097013253082720578733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5810925368674887254876621 2179097013253082720578733)
          ·
            refine ⟨817161379969906020217025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2179097013253082720578733 817161379969906020217025)
            ·
              refine ⟨612871034977429515162769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817161379969906020217025 612871034977429515162769)
              ·
                refine ⟨459653276233072136372077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612871034977429515162769 459653276233072136372077)
                ·
                  refine ⟨172369978587402051139529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459653276233072136372077 172369978587402051139529)
                  ·
                    rfl

theorem cell21_755301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_755301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755301 prefixEnd_755301 := by exact prefixLift 755301
  have htrace : WordTrace (prefixWord ++ tailWord_755301) baseStart_755301 baseEnd_755301 := by
    simpa [prefixWord, tailWord_755301, baseEnd_755301] using wordTrace_append hprefix tailTrace_755301
  have hstable : (prefixWord ++ tailWord_755301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755301).length < 2 ^ (prefixWord ++ tailWord_755301).sum := by decide
  have hdescent : baseEnd_755301 < baseStart_755301 := by decide
  rcases family_descends (prefixWord ++ tailWord_755301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755312 : List Nat := [2, 1, 1, 1, 6, 3, 1, 6]
def baseStart_755312 : Nat := 118140960795 + 755312 * 2 ^ 59
def prefixEnd_755312 : Nat := 4983230072969 + 3 ^ 40 * 755312 * 2
def baseEnd_755312 : Nat := 57457496312422825485391

theorem tailTrace_755312 : CollatzResearch.WordTrace tailWord_755312 prefixEnd_755312 57457496312422825485391 := by
  unfold tailWord_755312
  simp only [CollatzResearch.WordTrace]
  refine ⟨13774245919820547932366095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18365661226427397243154793 13774245919820547932366095)
  ·
    refine ⟨20661368879730821898549143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13774245919820547932366095 20661368879730821898549143)
    ·
      refine ⟨30992053319596232847823715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20661368879730821898549143 30992053319596232847823715)
      ·
        refine ⟨46488079979394349271735573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30992053319596232847823715 46488079979394349271735573)
        ·
          refine ⟨2179128749034110122112605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46488079979394349271735573 2179128749034110122112605)
          ·
            refine ⟨817173280887791295792227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2179128749034110122112605 817173280887791295792227)
            ·
              refine ⟨1225759921331686943688341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817173280887791295792227 1225759921331686943688341)
              ·
                refine ⟨57457496312422825485391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1225759921331686943688341 57457496312422825485391)
                ·
                  rfl

theorem cell21_755312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 6].length) (baseStart_755312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755312 prefixEnd_755312 := by exact prefixLift 755312
  have htrace : WordTrace (prefixWord ++ tailWord_755312) baseStart_755312 baseEnd_755312 := by
    simpa [prefixWord, tailWord_755312, baseEnd_755312] using wordTrace_append hprefix tailTrace_755312
  have hstable : (prefixWord ++ tailWord_755312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755312).length < 2 ^ (prefixWord ++ tailWord_755312).sum := by decide
  have hdescent : baseEnd_755312 < baseStart_755312 := by decide
  rcases family_descends (prefixWord ++ tailWord_755312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755340 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 6]
def baseStart_755340 : Nat := 118140960795 + 755340 * 2 ^ 59
def prefixEnd_755340 : Nat := 4983230072969 + 3 ^ 40 * 755340 * 2
def baseEnd_755340 : Nat := 172378878918746649989449

theorem tailTrace_755340 : CollatzResearch.WordTrace tailWord_755340 prefixEnd_755340 172378878918746649989449 := by
  unfold tailWord_755340
  simp only [CollatzResearch.WordTrace]
  refine ⟨13774756541769828323375737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18366342055693104431167649 13774756541769828323375737)
  ·
    refine ⟨10331067406327371242531803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13774756541769828323375737 10331067406327371242531803)
    ·
      refine ⟨15496601109491056863797705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10331067406327371242531803 15496601109491056863797705)
      ·
        refine ⟨11622450832118292647848279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15496601109491056863797705 11622450832118292647848279)
        ·
          refine ⟨17433676248177438971772419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11622450832118292647848279 17433676248177438971772419)
          ·
            refine ⟨26150514372266158457658629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17433676248177438971772419 26150514372266158457658629)
            ·
              refine ⟨4903221444799904710810993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26150514372266158457658629 4903221444799904710810993)
              ·
                refine ⟨3677416083599928533108245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4903221444799904710810993 3677416083599928533108245)
                ·
                  refine ⟨172378878918746649989449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3677416083599928533108245 172378878918746649989449)
                  ·
                    rfl

theorem cell21_755340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_755340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755340 prefixEnd_755340 := by exact prefixLift 755340
  have htrace : WordTrace (prefixWord ++ tailWord_755340) baseStart_755340 baseEnd_755340 := by
    simpa [prefixWord, tailWord_755340, baseEnd_755340] using wordTrace_append hprefix tailTrace_755340
  have hstable : (prefixWord ++ tailWord_755340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755340).length < 2 ^ (prefixWord ++ tailWord_755340).sum := by decide
  have hdescent : baseEnd_755340 < baseStart_755340 := by decide
  rcases family_descends (prefixWord ++ tailWord_755340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755388 : List Nat := [2, 2, 2, 3, 1, 2, 4, 5]
def baseStart_755388 : Nat := 118140960795 + 755388 * 2 ^ 59
def prefixEnd_755388 : Nat := 4983230072969 + 3 ^ 40 * 755388 * 2
def baseEnd_755388 : Nat := 57463277724236411063117

theorem tailTrace_755388 : CollatzResearch.WordTrace tailWord_755388 prefixEnd_755388 57463277724236411063117 := by
  unfold tailWord_755388
  simp only [CollatzResearch.WordTrace]
  refine ⟨13775631893682880422249409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18367509191577173896332545 13775631893682880422249409)
  ·
    refine ⟨10331723920262160316687057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13775631893682880422249409 10331723920262160316687057)
    ·
      refine ⟨7748792940196620237515293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10331723920262160316687057 7748792940196620237515293)
      ·
        refine ⟨2905797352573732589068235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7748792940196620237515293 2905797352573732589068235)
        ·
          refine ⟨4358696028860598883602353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905797352573732589068235 4358696028860598883602353)
          ·
            refine ⟨3269022021645449162701765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4358696028860598883602353 3269022021645449162701765)
            ·
              refine ⟨612941629058521718006581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3269022021645449162701765 612941629058521718006581)
              ·
                refine ⟨57463277724236411063117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 612941629058521718006581 57463277724236411063117)
                ·
                  rfl

theorem cell21_755388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 5].length) (baseStart_755388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755388 prefixEnd_755388 := by exact prefixLift 755388
  have htrace : WordTrace (prefixWord ++ tailWord_755388) baseStart_755388 baseEnd_755388 := by
    simpa [prefixWord, tailWord_755388, baseEnd_755388] using wordTrace_append hprefix tailTrace_755388
  have hstable : (prefixWord ++ tailWord_755388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755388).length < 2 ^ (prefixWord ++ tailWord_755388).sum := by decide
  have hdescent : baseEnd_755388 < baseStart_755388 := by decide
  rcases family_descends (prefixWord ++ tailWord_755388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755405 : List Nat := [1, 6, 2, 1, 1, 3, 7]
def baseStart_755405 : Nat := 118140960795 + 755405 * 2 ^ 59
def prefixEnd_755405 : Nat := 4983230072969 + 3 ^ 40 * 755405 * 2
def baseEnd_755405 : Nat := 19154856978257886822887

theorem tailTrace_755405 : CollatzResearch.WordTrace tailWord_755405 prefixEnd_755405 19154856978257886822887 := by
  unfold tailWord_755405
  simp only [CollatzResearch.WordTrace]
  refine ⟨27551883828304172747867669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18367922552202781831911779 27551883828304172747867669)
  ·
    refine ⟨1291494554451758097556297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27551883828304172747867669 1291494554451758097556297)
    ·
      refine ⟨968620915838818573167223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1291494554451758097556297 968620915838818573167223)
      ·
        refine ⟨1452931373758227859750835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968620915838818573167223 1452931373758227859750835)
        ·
          refine ⟨2179397060637341789626253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452931373758227859750835 2179397060637341789626253)
          ·
            refine ⟨817273897739003171109845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2179397060637341789626253 817273897739003171109845)
            ·
              refine ⟨19154856978257886822887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 817273897739003171109845 19154856978257886822887)
              ·
                rfl

theorem cell21_755405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 7].length) (baseStart_755405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755405 prefixEnd_755405 := by exact prefixLift 755405
  have htrace : WordTrace (prefixWord ++ tailWord_755405) baseStart_755405 baseEnd_755405 := by
    simpa [prefixWord, tailWord_755405, baseEnd_755405] using wordTrace_append hprefix tailTrace_755405
  have hstable : (prefixWord ++ tailWord_755405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755405).length < 2 ^ (prefixWord ++ tailWord_755405).sum := by decide
  have hdescent : baseEnd_755405 < baseStart_755405 := by decide
  rcases family_descends (prefixWord ++ tailWord_755405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755416 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 6]
def baseStart_755416 : Nat := 118140960795 + 755416 * 2 ^ 59
def prefixEnd_755416 : Nat := 4983230072969 + 3 ^ 40 * 755416 * 2
def baseEnd_755416 : Nat := 172396223154187406722627

theorem tailTrace_755416 : CollatzResearch.WordTrace tailWord_755416 prefixEnd_755416 172396223154187406722627 := by
  unfold tailWord_755416
  simp only [CollatzResearch.WordTrace]
  refine ⟨13776142515632160813259051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18368190020842881084345401 13776142515632160813259051)
  ·
    refine ⟨20664213773448241219888577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13776142515632160813259051 20664213773448241219888577)
    ·
      refine ⟨15498160330086180914916433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20664213773448241219888577 15498160330086180914916433)
      ·
        refine ⟨11623620247564635686187325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15498160330086180914916433 11623620247564635686187325)
        ·
          refine ⟨4358857592836738382320247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11623620247564635686187325 4358857592836738382320247)
          ·
            refine ⟨6538286389255107573480371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358857592836738382320247 6538286389255107573480371)
            ·
              refine ⟨9807429583882661360220557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6538286389255107573480371 9807429583882661360220557)
              ·
                refine ⟨3677786093955998010082709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9807429583882661360220557 3677786093955998010082709)
                ·
                  refine ⟨172396223154187406722627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3677786093955998010082709 172396223154187406722627)
                  ·
                    rfl

theorem cell21_755416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_755416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755416 prefixEnd_755416 := by exact prefixLift 755416
  have htrace : WordTrace (prefixWord ++ tailWord_755416) baseStart_755416 baseEnd_755416 := by
    simpa [prefixWord, tailWord_755416, baseEnd_755416] using wordTrace_append hprefix tailTrace_755416
  have hstable : (prefixWord ++ tailWord_755416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755416).length < 2 ^ (prefixWord ++ tailWord_755416).sum := by decide
  have hdescent : baseEnd_755416 < baseStart_755416 := by decide
  rcases family_descends (prefixWord ++ tailWord_755416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755462 : List Nat := [6, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_755462 : Nat := 118140960795 + 755462 * 2 ^ 59
def prefixEnd_755462 : Nat := 4983230072969 + 3 ^ 40 * 755462 * 2
def baseEnd_755462 : Nat := 172406720980901548955867

theorem tailTrace_755462 : CollatzResearch.WordTrace tailWord_755462 prefixEnd_755462 172406720980901548955867 := by
  unfold tailWord_755462
  simp only [CollatzResearch.WordTrace]
  refine ⟨861061337159302233834145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18369308526065114321795093 861061337159302233834145)
  ·
    refine ⟨645796002869476675375609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 861061337159302233834145 645796002869476675375609)
    ·
      refine ⟨484347002152107506531707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 645796002869476675375609 484347002152107506531707)
      ·
        refine ⟨726520503228161259797561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484347002152107506531707 726520503228161259797561)
        ·
          refine ⟨544890377421120944848171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726520503228161259797561 544890377421120944848171)
          ·
            refine ⟨817335566131681417272257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544890377421120944848171 817335566131681417272257)
            ·
              refine ⟨613001674598761062954193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817335566131681417272257 613001674598761062954193)
              ·
                refine ⟨459751255949070797215645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613001674598761062954193 459751255949070797215645)
                ·
                  refine ⟨172406720980901548955867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459751255949070797215645 172406720980901548955867)
                  ·
                    rfl

theorem cell21_755462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_755462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755462 prefixEnd_755462 := by exact prefixLift 755462
  have htrace : WordTrace (prefixWord ++ tailWord_755462) baseStart_755462 baseEnd_755462 := by
    simpa [prefixWord, tailWord_755462, baseEnd_755462] using wordTrace_append hprefix tailTrace_755462
  have hstable : (prefixWord ++ tailWord_755462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755462).length < 2 ^ (prefixWord ++ tailWord_755462).sum := by decide
  have hdescent : baseEnd_755462 < baseStart_755462 := by decide
  rcases family_descends (prefixWord ++ tailWord_755462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755602 : List Nat := [3, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_755602 : Nat := 118140960795 + 755602 * 2 ^ 59
def prefixEnd_755602 : Nat := 4983230072969 + 3 ^ 40 * 755602 * 2
def baseEnd_755602 : Nat := 172438670888292416622247

theorem tailTrace_755602 : CollatzResearch.WordTrace tailWord_755602 prefixEnd_755602 172438670888292416622247 := by
  unfold tailWord_755602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6889767252147618848197265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18372712672393650261859373 6889767252147618848197265)
  ·
    refine ⟨5167325439110714136147949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6889767252147618848197265 5167325439110714136147949)
    ·
      refine ⟨1937747039666517801055481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5167325439110714136147949 1937747039666517801055481)
      ·
        refine ⟨1453310279749888350791611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1937747039666517801055481 1453310279749888350791611)
        ·
          refine ⟨2179965419624832526187417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1453310279749888350791611 2179965419624832526187417)
          ·
            refine ⟨1634974064718624394640563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2179965419624832526187417 1634974064718624394640563)
            ·
              refine ⟨2452461097077936591960845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634974064718624394640563 2452461097077936591960845)
              ·
                refine ⟨919672911404226221985317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2452461097077936591960845 919672911404226221985317)
                ·
                  refine ⟨172438670888292416622247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 919672911404226221985317 172438670888292416622247)
                  ·
                    rfl

theorem cell21_755602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_755602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755602 prefixEnd_755602 := by exact prefixLift 755602
  have htrace : WordTrace (prefixWord ++ tailWord_755602) baseStart_755602 baseEnd_755602 := by
    simpa [prefixWord, tailWord_755602, baseEnd_755602] using wordTrace_append hprefix tailTrace_755602
  have hstable : (prefixWord ++ tailWord_755602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755602).length < 2 ^ (prefixWord ++ tailWord_755602).sum := by decide
  have hdescent : baseEnd_755602 < baseStart_755602 := by decide
  rcases family_descends (prefixWord ++ tailWord_755602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755740 : List Nat := [2, 2, 3, 1, 3, 3, 1, 3, 3]
def baseStart_755740 : Nat := 118140960795 + 755740 * 2 ^ 59
def prefixEnd_755740 : Nat := 4983230072969 + 3 ^ 40 * 755740 * 2
def baseEnd_755740 : Nat := 172470164368434843321965

theorem tailTrace_755740 : CollatzResearch.WordTrace tailWord_755740 prefixEnd_755740 172470164368434843321965 := by
  unfold tailWord_755740
  simp only [CollatzResearch.WordTrace]
  refine ⟨13782051141045262480656337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18376068188060349974208449 13782051141045262480656337)
  ·
    refine ⟨10336538355783946860492253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13782051141045262480656337 10336538355783946860492253)
    ·
      refine ⟨3876201883418980072684595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10336538355783946860492253 3876201883418980072684595)
      ·
        refine ⟨5814302825128470109026893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3876201883418980072684595 5814302825128470109026893)
        ·
          refine ⟨2180363559423176290885085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5814302825128470109026893 2180363559423176290885085)
          ·
            refine ⟨817636334783691109081907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2180363559423176290885085 817636334783691109081907)
            ·
              refine ⟨1226454502175536663622861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817636334783691109081907 1226454502175536663622861)
              ·
                refine ⟨459920438315826248858573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1226454502175536663622861 459920438315826248858573)
                ·
                  refine ⟨172470164368434843321965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459920438315826248858573 172470164368434843321965)
                  ·
                    rfl

theorem cell21_755740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_755740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755740 prefixEnd_755740 := by exact prefixLift 755740
  have htrace : WordTrace (prefixWord ++ tailWord_755740) baseStart_755740 baseEnd_755740 := by
    simpa [prefixWord, tailWord_755740, baseEnd_755740] using wordTrace_append hprefix tailTrace_755740
  have hstable : (prefixWord ++ tailWord_755740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755740).length < 2 ^ (prefixWord ++ tailWord_755740).sum := by decide
  have hdescent : baseEnd_755740 < baseStart_755740 := by decide
  rcases family_descends (prefixWord ++ tailWord_755740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755779 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 8]
def baseStart_755779 : Nat := 118140960795 + 755779 * 2 ^ 59
def prefixEnd_755779 : Nat := 4983230072969 + 3 ^ 40 * 755779 * 2
def baseEnd_755779 : Nat := 172479064699779442171885

theorem tailTrace_755779 : CollatzResearch.WordTrace tailWord_755779 prefixEnd_755779 172479064699779442171885 := by
  unfold tailWord_755779
  simp only [CollatzResearch.WordTrace]
  refine ⟨27565524728949234621982391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18377016485966156414654927 27565524728949234621982391)
  ·
    refine ⟨41348287093423851932973587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27565524728949234621982391 41348287093423851932973587)
    ·
      refine ⟨62022430640135777899460381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41348287093423851932973587 62022430640135777899460381)
      ·
        refine ⟨23258411490050916712297643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62022430640135777899460381 23258411490050916712297643)
        ·
          refine ⟨34887617235076375068446465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23258411490050916712297643 34887617235076375068446465)
          ·
            refine ⟨26165712926307281301334849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34887617235076375068446465 26165712926307281301334849)
            ·
              refine ⟨19624284694730460976001137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26165712926307281301334849 19624284694730460976001137)
              ·
                refine ⟨14718213521047845732000853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19624284694730460976001137 14718213521047845732000853)
                ·
                  refine ⟨172479064699779442171885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14718213521047845732000853 172479064699779442171885)
                  ·
                    rfl

theorem cell21_755779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_755779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755779 prefixEnd_755779 := by exact prefixLift 755779
  have htrace : WordTrace (prefixWord ++ tailWord_755779) baseStart_755779 baseEnd_755779 := by
    simpa [prefixWord, tailWord_755779, baseEnd_755779] using wordTrace_append hprefix tailTrace_755779
  have hstable : (prefixWord ++ tailWord_755779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755779).length < 2 ^ (prefixWord ++ tailWord_755779).sum := by decide
  have hdescent : baseEnd_755779 < baseStart_755779 := by decide
  rcases family_descends (prefixWord ++ tailWord_755779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755813 : List Nat := [1, 3, 1, 3, 2, 3, 2, 2, 4]
def baseStart_755813 : Nat := 118140960795 + 755813 * 2 ^ 59
def prefixEnd_755813 : Nat := 4983230072969 + 3 ^ 40 * 755813 * 2
def baseEnd_755813 : Nat := 172486823963002938605149

theorem tailTrace_755813 : CollatzResearch.WordTrace tailWord_755813 prefixEnd_755813 172486823963002938605149 := by
  unfold tailWord_755813
  simp only [CollatzResearch.WordTrace]
  refine ⟨27566764810826058428720093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18377843207217372285813395 27566764810826058428720093)
  ·
    refine ⟨10337536804059771910770035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27566764810826058428720093 10337536804059771910770035)
    ·
      refine ⟨15506305206089657866155053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10337536804059771910770035 15506305206089657866155053)
      ·
        refine ⟨5814864452283621699808145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15506305206089657866155053 5814864452283621699808145)
        ·
          refine ⟨4361148339212716274856109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5814864452283621699808145 4361148339212716274856109)
          ·
            refine ⟨1635430627204768603071041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4361148339212716274856109 1635430627204768603071041)
            ·
              refine ⟨1226572970403576452303281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1635430627204768603071041 1226572970403576452303281)
              ·
                refine ⟨919929727802682339227461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226572970403576452303281 919929727802682339227461)
                ·
                  refine ⟨172486823963002938605149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 919929727802682339227461 172486823963002938605149)
                  ·
                    rfl

theorem cell21_755813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_755813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755813 prefixEnd_755813 := by exact prefixLift 755813
  have htrace : WordTrace (prefixWord ++ tailWord_755813) baseStart_755813 baseEnd_755813 := by
    simpa [prefixWord, tailWord_755813, baseEnd_755813] using wordTrace_append hprefix tailTrace_755813
  have hstable : (prefixWord ++ tailWord_755813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755813).length < 2 ^ (prefixWord ++ tailWord_755813).sum := by decide
  have hdescent : baseEnd_755813 < baseStart_755813 := by decide
  rcases family_descends (prefixWord ++ tailWord_755813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755872 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 6]
def baseStart_755872 : Nat := 118140960795 + 755872 * 2 ^ 59
def prefixEnd_755872 : Nat := 4983230072969 + 3 ^ 40 * 755872 * 2
def baseEnd_755872 : Nat := 172500288566831947121695

theorem tailTrace_755872 : CollatzResearch.WordTrace tailWord_755872 prefixEnd_755872 172500288566831947121695 := by
  unfold tailWord_755872
  simp only [CollatzResearch.WordTrace]
  refine ⟨13784458358806155752558935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18379277811741541003411913 13784458358806155752558935)
  ·
    refine ⟨20676687538209233628838403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13784458358806155752558935 20676687538209233628838403)
    ·
      refine ⟨31015031307313850443257605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20676687538209233628838403 31015031307313850443257605)
      ·
        refine ⟨5815318370121346958110801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31015031307313850443257605 5815318370121346958110801)
        ·
          refine ⟨4361488777591010218583101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5815318370121346958110801 4361488777591010218583101)
          ·
            refine ⟨1635558291596628831968663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4361488777591010218583101 1635558291596628831968663)
            ·
              refine ⟨2453337437394943247952995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635558291596628831968663 2453337437394943247952995)
              ·
                refine ⟨3680006156092414871929493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2453337437394943247952995 3680006156092414871929493)
                ·
                  refine ⟨172500288566831947121695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3680006156092414871929493 172500288566831947121695)
                  ·
                    rfl

theorem cell21_755872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_755872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755872 prefixEnd_755872 := by exact prefixLift 755872
  have htrace : WordTrace (prefixWord ++ tailWord_755872) baseStart_755872 baseEnd_755872 := by
    simpa [prefixWord, tailWord_755872, baseEnd_755872] using wordTrace_append hprefix tailTrace_755872
  have hstable : (prefixWord ++ tailWord_755872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755872).length < 2 ^ (prefixWord ++ tailWord_755872).sum := by decide
  have hdescent : baseEnd_755872 < baseStart_755872 := by decide
  rcases family_descends (prefixWord ++ tailWord_755872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755906 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_755906 : Nat := 118140960795 + 755906 * 2 ^ 59
def prefixEnd_755906 : Nat := 4983230072969 + 3 ^ 40 * 755906 * 2
def baseEnd_755906 : Nat := 172508047830055443554959

theorem tailTrace_755906 : CollatzResearch.WordTrace tailWord_755906 prefixEnd_755906 172508047830055443554959 := by
  unfold tailWord_755906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892539199872283827963893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18380104532992756874570381 6892539199872283827963893)
  ·
    refine ⟨646175549988026608871615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6892539199872283827963893 646175549988026608871615)
    ·
      refine ⟨969263324982039913307423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 646175549988026608871615 969263324982039913307423)
      ·
        refine ⟨1453894987473059869961135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969263324982039913307423 1453894987473059869961135)
        ·
          refine ⟨2180842481209589804941703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1453894987473059869961135 2180842481209589804941703)
          ·
            refine ⟨3271263721814384707412555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180842481209589804941703 3271263721814384707412555)
            ·
              refine ⟨4906895582721577061118833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271263721814384707412555 4906895582721577061118833)
              ·
                refine ⟨3680171687041182795839125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4906895582721577061118833 3680171687041182795839125)
                ·
                  refine ⟨172508047830055443554959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3680171687041182795839125 172508047830055443554959)
                  ·
                    rfl

theorem cell21_755906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_755906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755906 prefixEnd_755906 := by exact prefixLift 755906
  have htrace : WordTrace (prefixWord ++ tailWord_755906) baseStart_755906 baseEnd_755906 := by
    simpa [prefixWord, tailWord_755906, baseEnd_755906] using wordTrace_append hprefix tailTrace_755906
  have hstable : (prefixWord ++ tailWord_755906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755906).length < 2 ^ (prefixWord ++ tailWord_755906).sum := by decide
  have hdescent : baseEnd_755906 < baseStart_755906 := by decide
  rcases family_descends (prefixWord ++ tailWord_755906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755948 : List Nat := [2, 2, 1, 1, 2, 3, 3, 3, 4]
def baseStart_755948 : Nat := 118140960795 + 755948 * 2 ^ 59
def prefixEnd_755948 : Nat := 4983230072969 + 3 ^ 40 * 755948 * 2
def baseEnd_755948 : Nat := 172517632802272703854873

theorem tailTrace_755948 : CollatzResearch.WordTrace tailWord_755948 prefixEnd_755948 172517632802272703854873 := by
  unfold tailWord_755948
  simp only [CollatzResearch.WordTrace]
  refine ⟨13785844332668488242442249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18381125776891317656589665 13785844332668488242442249)
  ·
    refine ⟨10339383249501366181831687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13785844332668488242442249 10339383249501366181831687)
    ·
      refine ⟨15509074874252049272747531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10339383249501366181831687 15509074874252049272747531)
      ·
        refine ⟨23263612311378073909121297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15509074874252049272747531 23263612311378073909121297)
        ·
          refine ⟨17447709233533555431840973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23263612311378073909121297 17447709233533555431840973)
          ·
            refine ⟨6542890962575083286940365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17447709233533555431840973 6542890962575083286940365)
            ·
              refine ⟨2453584110965656232602637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6542890962575083286940365 2453584110965656232602637)
              ·
                refine ⟨920094041612121087225989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2453584110965656232602637 920094041612121087225989)
                ·
                  refine ⟨172517632802272703854873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 920094041612121087225989 172517632802272703854873)
                  ·
                    rfl

theorem cell21_755948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_755948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755948 prefixEnd_755948 := by exact prefixLift 755948
  have htrace : WordTrace (prefixWord ++ tailWord_755948) baseStart_755948 baseEnd_755948 := by
    simpa [prefixWord, tailWord_755948, baseEnd_755948] using wordTrace_append hprefix tailTrace_755948
  have hstable : (prefixWord ++ tailWord_755948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755948).length < 2 ^ (prefixWord ++ tailWord_755948).sum := by decide
  have hdescent : baseEnd_755948 < baseStart_755948 := by decide
  rcases family_descends (prefixWord ++ tailWord_755948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755962 : List Nat := [3, 1, 1, 1, 1, 5, 2, 7]
def baseStart_755962 : Nat := 118140960795 + 755962 * 2 ^ 59
def prefixEnd_755962 : Nat := 4983230072969 + 3 ^ 40 * 755962 * 2
def baseEnd_755962 : Nat := 57506942597670596873837

theorem tailTrace_755962 : CollatzResearch.WordTrace tailWord_755962 prefixEnd_755962 57506942597670596873837 := by
  unfold tailWord_755962
  simp only [CollatzResearch.WordTrace]
  refine ⟨6893049821821564218973535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18381466191524171250596093 6893049821821564218973535)
  ·
    refine ⟨10339574732732346328460303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6893049821821564218973535 10339574732732346328460303)
    ·
      refine ⟨15509362099098519492690455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10339574732732346328460303 15509362099098519492690455)
      ·
        refine ⟨23264043148647779239035683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15509362099098519492690455 23264043148647779239035683)
        ·
          refine ⟨34896064722971668858553525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23264043148647779239035683 34896064722971668858553525)
          ·
            refine ⟨3271506067778593955489393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34896064722971668858553525 3271506067778593955489393)
            ·
              refine ⟨2453629550833945466617045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3271506067778593955489393 2453629550833945466617045)
              ·
                refine ⟨57506942597670596873837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2453629550833945466617045 57506942597670596873837)
                ·
                  rfl

theorem cell21_755962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_755962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_755962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_755962 prefixEnd_755962 := by exact prefixLift 755962
  have htrace : WordTrace (prefixWord ++ tailWord_755962) baseStart_755962 baseEnd_755962 := by
    simpa [prefixWord, tailWord_755962, baseEnd_755962] using wordTrace_append hprefix tailTrace_755962
  have hstable : (prefixWord ++ tailWord_755962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755962).length < 2 ^ (prefixWord ++ tailWord_755962).sum := by decide
  have hdescent : baseEnd_755962 < baseStart_755962 := by decide
  rcases family_descends (prefixWord ++ tailWord_755962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756013 : List Nat := [1, 5, 3, 1, 2, 1, 3, 5]
def baseStart_756013 : Nat := 118140960795 + 756013 * 2 ^ 59
def prefixEnd_756013 : Nat := 4983230072969 + 3 ^ 40 * 756013 * 2
def baseEnd_756013 : Nat := 57510822229282345090469

theorem tailTrace_756013 : CollatzResearch.WordTrace tailWord_756013 prefixEnd_756013 57510822229282345090469 := by
  unfold tailWord_756013
  simp only [CollatzResearch.WordTrace]
  refine ⟨27574059410101492586000693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18382706273400995057333795 27574059410101492586000693)
  ·
    refine ⟨2585068069697014929937565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27574059410101492586000693 2585068069697014929937565)
    ·
      refine ⟨969400526136380598726587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2585068069697014929937565 969400526136380598726587)
      ·
        refine ⟨1454100789204570898089881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969400526136380598726587 1454100789204570898089881)
        ·
          refine ⟨1090575591903428173567411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1454100789204570898089881 1090575591903428173567411)
          ·
            refine ⟨1635863387855142260351117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090575591903428173567411 1635863387855142260351117)
            ·
              refine ⟨613448770445678347631669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1635863387855142260351117 613448770445678347631669)
              ·
                refine ⟨57510822229282345090469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 613448770445678347631669 57510822229282345090469)
                ·
                  rfl

theorem cell21_756013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 5].length) (baseStart_756013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756013 prefixEnd_756013 := by exact prefixLift 756013
  have htrace : WordTrace (prefixWord ++ tailWord_756013) baseStart_756013 baseEnd_756013 := by
    simpa [prefixWord, tailWord_756013, baseEnd_756013] using wordTrace_append hprefix tailTrace_756013
  have hstable : (prefixWord ++ tailWord_756013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756013).length < 2 ^ (prefixWord ++ tailWord_756013).sum := by decide
  have hdescent : baseEnd_756013 < baseStart_756013 := by decide
  rcases family_descends (prefixWord ++ tailWord_756013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756069 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 5]
def baseStart_756069 : Nat := 118140960795 + 756069 * 2 ^ 59
def prefixEnd_756069 : Nat := 4983230072969 + 3 ^ 40 * 756069 * 2
def baseEnd_756069 : Nat := 172545246650803382337959

theorem tailTrace_756069 : CollatzResearch.WordTrace tailWord_756069 prefixEnd_756069 172545246650803382337959 := by
  unfold tailWord_756069
  simp only [CollatzResearch.WordTrace]
  refine ⟨27576101897898614150039261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18384067931932409433359507 27576101897898614150039261)
  ·
    refine ⟨10341038211711980306264723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27576101897898614150039261 10341038211711980306264723)
    ·
      refine ⟨15511557317567970459397085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10341038211711980306264723 15511557317567970459397085)
      ·
        refine ⟨5816833994087988922273907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15511557317567970459397085 5816833994087988922273907)
        ·
          refine ⟨8725250991131983383410861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5816833994087988922273907 8725250991131983383410861)
          ·
            refine ⟨3271969121674493768779073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8725250991131983383410861 3271969121674493768779073)
            ·
              refine ⟨2453976841255870326584305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3271969121674493768779073 2453976841255870326584305)
              ·
                refine ⟨1840482630941902744938229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2453976841255870326584305 1840482630941902744938229)
                ·
                  refine ⟨172545246650803382337959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1840482630941902744938229 172545246650803382337959)
                  ·
                    rfl

theorem cell21_756069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_756069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756069 prefixEnd_756069 := by exact prefixLift 756069
  have htrace : WordTrace (prefixWord ++ tailWord_756069) baseStart_756069 baseEnd_756069 := by
    simpa [prefixWord, tailWord_756069, baseEnd_756069] using wordTrace_append hprefix tailTrace_756069
  have hstable : (prefixWord ++ tailWord_756069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756069).length < 2 ^ (prefixWord ++ tailWord_756069).sum := by decide
  have hdescent : baseEnd_756069 < baseStart_756069 := by decide
  rcases family_descends (prefixWord ++ tailWord_756069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756072 : List Nat := [2, 1, 4, 2, 2, 3, 2, 5]
def baseStart_756072 : Nat := 118140960795 + 756072 * 2 ^ 59
def prefixEnd_756072 : Nat := 4983230072969 + 3 ^ 40 * 756072 * 2
def baseEnd_756072 : Nat := 57515310430558681262651

theorem tailTrace_756072 : CollatzResearch.WordTrace tailWord_756072 prefixEnd_756072 57515310430558681262651 := by
  unfold tailWord_756072
  simp only [CollatzResearch.WordTrace]
  refine ⟨13788105658443872831199235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18384140877925163774932313 13788105658443872831199235)
  ·
    refine ⟨20682158487665809246798853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13788105658443872831199235 20682158487665809246798853)
    ·
      refine ⟨3877904716437339233774785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20682158487665809246798853 3877904716437339233774785)
      ·
        refine ⟨2908428537328004425331089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3877904716437339233774785 2908428537328004425331089)
        ·
          refine ⟨2181321402996003318998317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2908428537328004425331089 2181321402996003318998317)
          ·
            refine ⟨817995526123501244624369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2181321402996003318998317 817995526123501244624369)
            ·
              refine ⟨613496644592625933468277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817995526123501244624369 613496644592625933468277)
              ·
                refine ⟨57515310430558681262651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 613496644592625933468277 57515310430558681262651)
                ·
                  rfl

theorem cell21_756072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 5].length) (baseStart_756072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756072 prefixEnd_756072 := by exact prefixLift 756072
  have htrace : WordTrace (prefixWord ++ tailWord_756072) baseStart_756072 baseEnd_756072 := by
    simpa [prefixWord, tailWord_756072, baseEnd_756072] using wordTrace_append hprefix tailTrace_756072
  have hstable : (prefixWord ++ tailWord_756072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756072).length < 2 ^ (prefixWord ++ tailWord_756072).sum := by decide
  have hdescent : baseEnd_756072 < baseStart_756072 := by decide
  rcases family_descends (prefixWord ++ tailWord_756072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756100 : List Nat := [2, 3, 2, 1, 1, 2, 2, 4, 4]
def baseStart_756100 : Nat := 118140960795 + 756100 * 2 ^ 59
def prefixEnd_756100 : Nat := 4983230072969 + 3 ^ 40 * 756100 * 2
def baseEnd_756100 : Nat := 172552321273154217321229

theorem tailTrace_756100 : CollatzResearch.WordTrace tailWord_756100 prefixEnd_756100 172552321273154217321229 := by
  unfold tailWord_756100
  simp only [CollatzResearch.WordTrace]
  refine ⟨13788616280393153222208877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18384821707190870962945169 13788616280393153222208877)
  ·
    refine ⟨5170731105147432458328329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13788616280393153222208877 5170731105147432458328329)
    ·
      refine ⟨3878048328860574343746247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5170731105147432458328329 3878048328860574343746247)
      ·
        refine ⟨5817072493290861515619371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3878048328860574343746247 5817072493290861515619371)
        ·
          refine ⟨8725608739936292273429057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5817072493290861515619371 8725608739936292273429057)
          ·
            refine ⟨6544206554952219205071793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8725608739936292273429057 6544206554952219205071793)
            ·
              refine ⟨4908154916214164403803845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6544206554952219205071793 4908154916214164403803845)
              ·
                refine ⟨920279046790155825713221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4908154916214164403803845 920279046790155825713221)
                ·
                  refine ⟨172552321273154217321229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 920279046790155825713221 172552321273154217321229)
                  ·
                    rfl

theorem cell21_756100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_756100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756100 prefixEnd_756100 := by exact prefixLift 756100
  have htrace : WordTrace (prefixWord ++ tailWord_756100) baseStart_756100 baseEnd_756100 := by
    simpa [prefixWord, tailWord_756100, baseEnd_756100] using wordTrace_append hprefix tailTrace_756100
  have hstable : (prefixWord ++ tailWord_756100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756100).length < 2 ^ (prefixWord ++ tailWord_756100).sum := by decide
  have hdescent : baseEnd_756100 < baseStart_756100 := by decide
  rcases family_descends (prefixWord ++ tailWord_756100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756103 : List Nat := [1, 1, 4, 2, 2, 1, 5, 2, 3]
def baseStart_756103 : Nat := 118140960795 + 756103 * 2 ^ 59
def prefixEnd_756103 : Nat := 4983230072969 + 3 ^ 40 * 756103 * 2
def baseEnd_756103 : Nat := 172553005914026878771223

theorem tailTrace_756103 : CollatzResearch.WordTrace tailWord_756103 prefixEnd_756103 172553005914026878771223 := by
  unfold tailWord_756103
  simp only [CollatzResearch.WordTrace]
  refine ⟨27577341979775437956776963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18384894653183625304517975 27577341979775437956776963)
  ·
    refine ⟨41366012969663156935165445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27577341979775437956776963 41366012969663156935165445)
    ·
      refine ⟨7756127431811841925343521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41366012969663156935165445 7756127431811841925343521)
      ·
        refine ⟨5817095573858881444007641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7756127431811841925343521 5817095573858881444007641)
        ·
          refine ⟨4362821680394161083005731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5817095573858881444007641 4362821680394161083005731)
          ·
            refine ⟨6544232520591241624508597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4362821680394161083005731 6544232520591241624508597)
            ·
              refine ⟨613521798805428902297681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6544232520591241624508597 613521798805428902297681)
              ·
                refine ⟨460141349104071676723261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613521798805428902297681 460141349104071676723261)
                ·
                  refine ⟨172553005914026878771223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460141349104071676723261 172553005914026878771223)
                  ·
                    rfl

theorem cell21_756103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 3].length) (baseStart_756103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756103 prefixEnd_756103 := by exact prefixLift 756103
  have htrace : WordTrace (prefixWord ++ tailWord_756103) baseStart_756103 baseEnd_756103 := by
    simpa [prefixWord, tailWord_756103, baseEnd_756103] using wordTrace_append hprefix tailTrace_756103
  have hstable : (prefixWord ++ tailWord_756103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756103).length < 2 ^ (prefixWord ++ tailWord_756103).sum := by decide
  have hdescent : baseEnd_756103 < baseStart_756103 := by decide
  rcases family_descends (prefixWord ++ tailWord_756103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756148 : List Nat := [2, 5, 2, 2, 1, 9]
def baseStart_756148 : Nat := 118140960795 + 756148 * 2 ^ 59
def prefixEnd_756148 : Nat := 4983230072969 + 3 ^ 40 * 756148 * 2
def baseEnd_756148 : Nat := 6391232426930251871153

theorem tailTrace_756148 : CollatzResearch.WordTrace tailWord_756148 prefixEnd_756148 6391232426930251871153 := by
  unfold tailWord_756148
  simp only [CollatzResearch.WordTrace]
  refine ⟨13789491632306205321082549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18385988843074940428110065 13789491632306205321082549)
  ·
    refine ⟨1292764840528706748851489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13789491632306205321082549 1292764840528706748851489)
    ·
      refine ⟨969573630396530061638617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1292764840528706748851489 969573630396530061638617)
      ·
        refine ⟨727180222797397546228963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 969573630396530061638617 727180222797397546228963)
        ·
          refine ⟨1090770334196096319343445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727180222797397546228963 1090770334196096319343445)
          ·
            refine ⟨6391232426930251871153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1090770334196096319343445 6391232426930251871153)
            ·
              rfl

theorem cell21_756148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 9].length) (baseStart_756148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756148 prefixEnd_756148 := by exact prefixLift 756148
  have htrace : WordTrace (prefixWord ++ tailWord_756148) baseStart_756148 baseEnd_756148 := by
    simpa [prefixWord, tailWord_756148, baseEnd_756148] using wordTrace_append hprefix tailTrace_756148
  have hstable : (prefixWord ++ tailWord_756148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756148).length < 2 ^ (prefixWord ++ tailWord_756148).sum := by decide
  have hdescent : baseEnd_756148 < baseStart_756148 := by decide
  rcases family_descends (prefixWord ++ tailWord_756148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756204 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 7]
def baseStart_756204 : Nat := 118140960795 + 756204 * 2 ^ 59
def prefixEnd_756204 : Nat := 4983230072969 + 3 ^ 40 * 756204 * 2
def baseEnd_756204 : Nat := 172576055490073147587683

theorem tailTrace_756204 : CollatzResearch.WordTrace tailWord_756204 prefixEnd_756204 172576055490073147587683 := by
  unfold tailWord_756204
  simp only [CollatzResearch.WordTrace]
  refine ⟨13790512876204766103101833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18387350501606354804135777 13790512876204766103101833)
  ·
    refine ⟨10342884657153574577326375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13790512876204766103101833 10342884657153574577326375)
    ·
      refine ⟨15514326985730361865989563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10342884657153574577326375 15514326985730361865989563)
      ·
        refine ⟨23271490478595542798984345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15514326985730361865989563 23271490478595542798984345)
        ·
          refine ⟨17453617858946657099238259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23271490478595542798984345 17453617858946657099238259)
          ·
            refine ⟨26180426788419985648857389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17453617858946657099238259 26180426788419985648857389)
            ·
              refine ⟨9817660045657494618321521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26180426788419985648857389 9817660045657494618321521)
              ·
                refine ⟨7363245034243120963741141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9817660045657494618321521 7363245034243120963741141)
                ·
                  refine ⟨172576055490073147587683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7363245034243120963741141 172576055490073147587683)
                  ·
                    rfl

theorem cell21_756204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_756204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756204 prefixEnd_756204 := by exact prefixLift 756204
  have htrace : WordTrace (prefixWord ++ tailWord_756204) baseStart_756204 baseEnd_756204 := by
    simpa [prefixWord, tailWord_756204, baseEnd_756204] using wordTrace_append hprefix tailTrace_756204
  have hstable : (prefixWord ++ tailWord_756204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756204).length < 2 ^ (prefixWord ++ tailWord_756204).sum := by decide
  have hdescent : baseEnd_756204 < baseStart_756204 := by decide
  rcases family_descends (prefixWord ++ tailWord_756204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756210 : List Nat := [3, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_756210 : Nat := 118140960795 + 756210 * 2 ^ 59
def prefixEnd_756210 : Nat := 4983230072969 + 3 ^ 40 * 756210 * 2
def baseEnd_756210 : Nat := 172577424771818470487671

theorem tailTrace_756210 : CollatzResearch.WordTrace tailWord_756210 prefixEnd_756210 172577424771818470487671 := by
  unfold tailWord_756210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6895311147596948807730521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18387496393591863487281389 6895311147596948807730521)
  ·
    refine ⟨5171483360697711605797891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6895311147596948807730521 5171483360697711605797891)
    ·
      refine ⟨7757225041046567408696837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5171483360697711605797891 7757225041046567408696837)
      ·
        refine ⟨1454479695196231389130657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7757225041046567408696837 1454479695196231389130657)
        ·
          refine ⟨1090859771397173541847993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1454479695196231389130657 1090859771397173541847993)
          ·
            refine ⟨818144828547880156385995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1090859771397173541847993 818144828547880156385995)
            ·
              refine ⟨1227217242821820234578993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818144828547880156385995 1227217242821820234578993)
              ·
                refine ⟨920412932116365175934245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227217242821820234578993 920412932116365175934245)
                ·
                  refine ⟨172577424771818470487671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 920412932116365175934245 172577424771818470487671)
                  ·
                    rfl

theorem cell21_756210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_756210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756210 prefixEnd_756210 := by exact prefixLift 756210
  have htrace : WordTrace (prefixWord ++ tailWord_756210) baseStart_756210 baseEnd_756210 := by
    simpa [prefixWord, tailWord_756210, baseEnd_756210] using wordTrace_append hprefix tailTrace_756210
  have hstable : (prefixWord ++ tailWord_756210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756210).length < 2 ^ (prefixWord ++ tailWord_756210).sum := by decide
  have hdescent : baseEnd_756210 < baseStart_756210 := by decide
  rcases family_descends (prefixWord ++ tailWord_756210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756221 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 5]
def baseStart_756221 : Nat := 118140960795 + 756221 * 2 ^ 59
def prefixEnd_756221 : Nat := 4983230072969 + 3 ^ 40 * 756221 * 2
def baseEnd_756221 : Nat := 172579935121684895804315

theorem tailTrace_756221 : CollatzResearch.WordTrace tailWord_756221 prefixEnd_756221 172579935121684895804315 := by
  unfold tailWord_756221
  simp only [CollatzResearch.WordTrace]
  refine ⟨27581645793347944109572517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18387763862231962739715011 27581645793347944109572517)
  ·
    refine ⟨5171558586252739520544847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27581645793347944109572517 5171558586252739520544847)
    ·
      refine ⟨7757337879379109280817271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5171558586252739520544847 7757337879379109280817271)
      ·
        refine ⟨11636006819068663921225907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7757337879379109280817271 11636006819068663921225907)
        ·
          refine ⟨17454010228602995881838861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11636006819068663921225907 17454010228602995881838861)
          ·
            refine ⟨6545253835726123455689573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17454010228602995881838861 6545253835726123455689573)
            ·
              refine ⟨1227235094198648147941795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6545253835726123455689573 1227235094198648147941795)
              ·
                refine ⟨1840852641297972221912693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227235094198648147941795 1840852641297972221912693)
                ·
                  refine ⟨172579935121684895804315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1840852641297972221912693 172579935121684895804315)
                  ·
                    rfl

theorem cell21_756221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_756221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756221 prefixEnd_756221 := by exact prefixLift 756221
  have htrace : WordTrace (prefixWord ++ tailWord_756221) baseStart_756221 baseEnd_756221 := by
    simpa [prefixWord, tailWord_756221, baseEnd_756221] using wordTrace_append hprefix tailTrace_756221
  have hstable : (prefixWord ++ tailWord_756221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756221).length < 2 ^ (prefixWord ++ tailWord_756221).sum := by decide
  have hdescent : baseEnd_756221 < baseStart_756221 := by decide
  rcases family_descends (prefixWord ++ tailWord_756221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756249 : List Nat := [1, 2, 1, 2, 1, 1, 2, 11]
def baseStart_756249 : Nat := 118140960795 + 756249 * 2 ^ 59
def prefixEnd_756249 : Nat := 4983230072969 + 3 ^ 40 * 756249 * 2
def baseEnd_756249 : Nat := 57528775034387689779197

theorem tailTrace_756249 : CollatzResearch.WordTrace tailWord_756249 prefixEnd_756249 57528775034387689779197 := by
  unfold tailWord_756249
  simp only [CollatzResearch.WordTrace]
  refine ⟨27582667037246504891591801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18388444691497669927727867 27582667037246504891591801)
  ·
    refine ⟨20687000277934878668693851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27582667037246504891591801 20687000277934878668693851)
    ·
      refine ⟨31030500416902318003040777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20687000277934878668693851 31030500416902318003040777)
      ·
        refine ⟨23272875312676738502280583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31030500416902318003040777 23272875312676738502280583)
        ·
          refine ⟨34909312969015107753420875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23272875312676738502280583 34909312969015107753420875)
          ·
            refine ⟨52363969453522661630131313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34909312969015107753420875 52363969453522661630131313)
            ·
              refine ⟨39272977090141996222598485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52363969453522661630131313 39272977090141996222598485)
              ·
                refine ⟨57528775034387689779197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 39272977090141996222598485 57528775034387689779197)
                ·
                  rfl

theorem cell21_756249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 11].length) (baseStart_756249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756249 prefixEnd_756249 := by exact prefixLift 756249
  have htrace : WordTrace (prefixWord ++ tailWord_756249) baseStart_756249 baseEnd_756249 := by
    simpa [prefixWord, tailWord_756249, baseEnd_756249] using wordTrace_append hprefix tailTrace_756249
  have hstable : (prefixWord ++ tailWord_756249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756249).length < 2 ^ (prefixWord ++ tailWord_756249).sum := by decide
  have hdescent : baseEnd_756249 < baseStart_756249 := by decide
  rcases family_descends (prefixWord ++ tailWord_756249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756266 : List Nat := [3, 1, 4, 1, 1, 2, 9]
def baseStart_756266 : Nat := 118140960795 + 756266 * 2 ^ 59
def prefixEnd_756266 : Nat := 4983230072969 + 3 ^ 40 * 756266 * 2
def baseEnd_756266 : Nat := 19176689414974979728247

theorem tailTrace_756266 : CollatzResearch.WordTrace tailWord_756266 prefixEnd_756266 19176689414974979728247 := by
  unfold tailWord_756266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6895821769546229198740163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18388858052123277863307101 6895821769546229198740163)
  ·
    refine ⟨10343732654319343798110245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6895821769546229198740163 10343732654319343798110245)
    ·
      refine ⟨1939449872684876962145671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10343732654319343798110245 1939449872684876962145671)
      ·
        refine ⟨2909174809027315443218507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1939449872684876962145671 2909174809027315443218507)
        ·
          refine ⟨4363762213540973164827761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909174809027315443218507 4363762213540973164827761)
          ·
            refine ⟨3272821660155729873620821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4363762213540973164827761 3272821660155729873620821)
            ·
              refine ⟨19176689414974979728247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3272821660155729873620821 19176689414974979728247)
              ·
                rfl

theorem cell21_756266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 9].length) (baseStart_756266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756266 prefixEnd_756266 := by exact prefixLift 756266
  have htrace : WordTrace (prefixWord ++ tailWord_756266) baseStart_756266 baseEnd_756266 := by
    simpa [prefixWord, tailWord_756266, baseEnd_756266] using wordTrace_append hprefix tailTrace_756266
  have hstable : (prefixWord ++ tailWord_756266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756266).length < 2 ^ (prefixWord ++ tailWord_756266).sum := by decide
  have hdescent : baseEnd_756266 < baseStart_756266 := by decide
  rcases family_descends (prefixWord ++ tailWord_756266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756286 : List Nat := [4, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_756286 : Nat := 118140960795 + 756286 * 2 ^ 59
def prefixEnd_756286 : Nat := 4983230072969 + 3 ^ 40 * 756286 * 2
def baseEnd_756286 : Nat := 172594769007259227220849

theorem tailTrace_756286 : CollatzResearch.WordTrace tailWord_756286 prefixEnd_756286 172594769007259227220849 := by
  unfold tailWord_756286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3448002067264057526336089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18389344358741640140459141 3448002067264057526336089)
  ·
    refine ⟨2586001550448043144752067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3448002067264057526336089 2586001550448043144752067)
    ·
      refine ⟨3879002325672064717128101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2586001550448043144752067 3879002325672064717128101)
      ·
        refine ⟨727312936063512134461519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3879002325672064717128101 727312936063512134461519)
        ·
          refine ⟨1090969404095268201692279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727312936063512134461519 1090969404095268201692279)
          ·
            refine ⟨1636454106142902302538419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090969404095268201692279 1636454106142902302538419)
            ·
              refine ⟨2454681159214353453807629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636454106142902302538419 2454681159214353453807629)
              ·
                refine ⟨920505434705382545177861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2454681159214353453807629 920505434705382545177861)
                ·
                  refine ⟨172594769007259227220849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 920505434705382545177861 172594769007259227220849)
                  ·
                    rfl

theorem cell21_756286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_756286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756286 prefixEnd_756286 := by exact prefixLift 756286
  have htrace : WordTrace (prefixWord ++ tailWord_756286) baseStart_756286 baseEnd_756286 := by
    simpa [prefixWord, tailWord_756286, baseEnd_756286] using wordTrace_append hprefix tailTrace_756286
  have hstable : (prefixWord ++ tailWord_756286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756286).length < 2 ^ (prefixWord ++ tailWord_756286).sum := by decide
  have hdescent : baseEnd_756286 < baseStart_756286 := by decide
  rcases family_descends (prefixWord ++ tailWord_756286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756325 : List Nat := [1, 3, 1, 3, 13]
def baseStart_756325 : Nat := 118140960795 + 756325 * 2 ^ 59
def prefixEnd_756325 : Nat := 4983230072969 + 3 ^ 40 * 756325 * 2
def baseEnd_756325 : Nat := 2130909498007454642849

theorem tailTrace_756325 : CollatzResearch.WordTrace tailWord_756325 prefixEnd_756325 2130909498007454642849 := by
  unfold tailWord_756325
  simp only [CollatzResearch.WordTrace]
  refine ⟨27585438984971169871358429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18390292656647446580905619 27585438984971169871358429)
  ·
    refine ⟨10344539619364188701759411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27585438984971169871358429 10344539619364188701759411)
    ·
      refine ⟨15516809429046283052639117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10344539619364188701759411 15516809429046283052639117)
      ·
        refine ⟨5818803535892356144739669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15516809429046283052639117 5818803535892356144739669)
        ·
          refine ⟨2130909498007454642849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 5818803535892356144739669 2130909498007454642849)
          ·
            rfl

theorem cell21_756325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 13].length) (baseStart_756325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756325 prefixEnd_756325 := by exact prefixLift 756325
  have htrace : WordTrace (prefixWord ++ tailWord_756325) baseStart_756325 baseEnd_756325 := by
    simpa [prefixWord, tailWord_756325, baseEnd_756325] using wordTrace_append hprefix tailTrace_756325
  have hstable : (prefixWord ++ tailWord_756325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756325).length < 2 ^ (prefixWord ++ tailWord_756325).sum := by decide
  have hdescent : baseEnd_756325 < baseStart_756325 := by decide
  rcases family_descends (prefixWord ++ tailWord_756325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756387 : List Nat := [1, 1, 1, 4, 1, 1, 2, 6, 4]
def baseStart_756387 : Nat := 118140960795 + 756387 * 2 ^ 59
def prefixEnd_756387 : Nat := 4983230072969 + 3 ^ 40 * 756387 * 2
def baseEnd_756387 : Nat := 172617818583305496037309

theorem tailTrace_756387 : CollatzResearch.WordTrace tailWord_756387 prefixEnd_756387 172617818583305496037309 := by
  unfold tailWord_756387
  simp only [CollatzResearch.WordTrace]
  refine ⟨27587700310746554460115415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18391800207164369640076943 27587700310746554460115415)
  ·
    refine ⟨41381550466119831690173123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27587700310746554460115415 41381550466119831690173123)
    ·
      refine ⟨62072325699179747535259685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41381550466119831690173123 62072325699179747535259685)
      ·
        refine ⟨11638561068596202662861191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62072325699179747535259685 11638561068596202662861191)
        ·
          refine ⟨17457841602894303994291787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11638561068596202662861191 17457841602894303994291787)
          ·
            refine ⟨26186762404341455991437681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17457841602894303994291787 26186762404341455991437681)
            ·
              refine ⟨19640071803256091993578261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26186762404341455991437681 19640071803256091993578261)
              ·
                refine ⟨920628365777629312198981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19640071803256091993578261 920628365777629312198981)
                ·
                  refine ⟨172617818583305496037309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 920628365777629312198981 172617818583305496037309)
                  ·
                    rfl

theorem cell21_756387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 4].length) (baseStart_756387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756387 prefixEnd_756387 := by exact prefixLift 756387
  have htrace : WordTrace (prefixWord ++ tailWord_756387) baseStart_756387 baseEnd_756387 := by
    simpa [prefixWord, tailWord_756387, baseEnd_756387] using wordTrace_append hprefix tailTrace_756387
  have hstable : (prefixWord ++ tailWord_756387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756387).length < 2 ^ (prefixWord ++ tailWord_756387).sum := by decide
  have hdescent : baseEnd_756387 < baseStart_756387 := by decide
  rcases family_descends (prefixWord ++ tailWord_756387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756449 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 5]
def baseStart_756449 : Nat := 118140960795 + 756449 * 2 ^ 59
def prefixEnd_756449 : Nat := 4983230072969 + 3 ^ 40 * 756449 * 2
def baseEnd_756449 : Nat := 172631967828007166003849

theorem tailTrace_756449 : CollatzResearch.WordTrace tailWord_756449 prefixEnd_756449 172631967828007166003849 := by
  unfold tailWord_756449
  simp only [CollatzResearch.WordTrace]
  refine ⟨27589961636521939048872401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18393307757681292699248267 27589961636521939048872401)
  ·
    refine ⟨20692471227391454286654301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27589961636521939048872401 20692471227391454286654301)
    ·
      refine ⟨7759676710271795357495363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20692471227391454286654301 7759676710271795357495363)
      ·
        refine ⟨11639515065407693036243045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7759676710271795357495363 11639515065407693036243045)
        ·
          refine ⟨2182409074763942444295571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11639515065407693036243045 2182409074763942444295571)
          ·
            refine ⟨3273613612145913666443357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182409074763942444295571 3273613612145913666443357)
            ·
              refine ⟨1227605104554717624916259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3273613612145913666443357 1227605104554717624916259)
              ·
                refine ⟨1841407656832076437374389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227605104554717624916259 1841407656832076437374389)
                ·
                  refine ⟨172631967828007166003849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1841407656832076437374389 172631967828007166003849)
                  ·
                    rfl

theorem cell21_756449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_756449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756449 prefixEnd_756449 := by exact prefixLift 756449
  have htrace : WordTrace (prefixWord ++ tailWord_756449) baseStart_756449 baseEnd_756449 := by
    simpa [prefixWord, tailWord_756449, baseEnd_756449] using wordTrace_append hprefix tailTrace_756449
  have hstable : (prefixWord ++ tailWord_756449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756449).length < 2 ^ (prefixWord ++ tailWord_756449).sum := by decide
  have hdescent : baseEnd_756449 < baseStart_756449 := by decide
  rcases family_descends (prefixWord ++ tailWord_756449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756477 : List Nat := [1, 4, 1, 1, 1, 1, 3, 9]
def baseStart_756477 : Nat := 118140960795 + 756477 * 2 ^ 59
def prefixEnd_756477 : Nat := 4983230072969 + 3 ^ 40 * 756477 * 2
def baseEnd_756477 : Nat := 57546119269828446512375

theorem tailTrace_756477 : CollatzResearch.WordTrace tailWord_756477 prefixEnd_756477 57546119269828446512375 := by
  unfold tailWord_756477
  simp only [CollatzResearch.WordTrace]
  refine ⟨27590982880420499830891685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18393988586946999887261123 27590982880420499830891685)
  ·
    refine ⟨5173309290078843718292191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27590982880420499830891685 5173309290078843718292191)
    ·
      refine ⟨7759963935118265577438287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5173309290078843718292191 7759963935118265577438287)
      ·
        refine ⟨11639945902677398366157431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7759963935118265577438287 11639945902677398366157431)
        ·
          refine ⟨17459918854016097549236147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11639945902677398366157431 17459918854016097549236147)
          ·
            refine ⟨26189878281024146323854221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17459918854016097549236147 26189878281024146323854221)
            ·
              refine ⟨9821204355384054871445333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26189878281024146323854221 9821204355384054871445333)
              ·
                refine ⟨57546119269828446512375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9821204355384054871445333 57546119269828446512375)
                ·
                  rfl

theorem cell21_756477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 9].length) (baseStart_756477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756477 prefixEnd_756477 := by exact prefixLift 756477
  have htrace : WordTrace (prefixWord ++ tailWord_756477) baseStart_756477 baseEnd_756477 := by
    simpa [prefixWord, tailWord_756477, baseEnd_756477] using wordTrace_append hprefix tailTrace_756477
  have hstable : (prefixWord ++ tailWord_756477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756477).length < 2 ^ (prefixWord ++ tailWord_756477).sum := by decide
  have hdescent : baseEnd_756477 < baseStart_756477 := by decide
  rcases family_descends (prefixWord ++ tailWord_756477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756553 : List Nat := [1, 2, 1, 1, 2, 6, 8]
def baseStart_756553 : Nat := 118140960795 + 756553 * 2 ^ 59
def prefixEnd_756553 : Nat := 4983230072969 + 3 ^ 40 * 756553 * 2
def baseEnd_756553 : Nat := 19183966893880677363367

theorem tailTrace_756553 : CollatzResearch.WordTrace tailWord_756553 prefixEnd_756553 19183966893880677363367 := by
  unfold tailWord_756553
  simp only [CollatzResearch.WordTrace]
  refine ⟨27593754828145164810658313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18395836552096776540438875 27593754828145164810658313)
  ·
    refine ⟨20695316121108873607993735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27593754828145164810658313 20695316121108873607993735)
    ·
      refine ⟨31042974181663310411990603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20695316121108873607993735 31042974181663310411990603)
      ·
        refine ⟨46564461272494965617985905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31042974181663310411990603 46564461272494965617985905)
        ·
          refine ⟨34923345954371224213489429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46564461272494965617985905 34923345954371224213489429)
          ·
            refine ⟨1637031841611151135007317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34923345954371224213489429 1637031841611151135007317)
            ·
              refine ⟨19183966893880677363367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1637031841611151135007317 19183966893880677363367)
              ·
                rfl

theorem cell21_756553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 8].length) (baseStart_756553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756553 prefixEnd_756553 := by exact prefixLift 756553
  have htrace : WordTrace (prefixWord ++ tailWord_756553) baseStart_756553 baseEnd_756553 := by
    simpa [prefixWord, tailWord_756553, baseEnd_756553] using wordTrace_append hprefix tailTrace_756553
  have hstable : (prefixWord ++ tailWord_756553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756553).length < 2 ^ (prefixWord ++ tailWord_756553).sum := by decide
  have hdescent : baseEnd_756553 < baseStart_756553 := by decide
  rcases family_descends (prefixWord ++ tailWord_756553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756556 : List Nat := [2, 2, 1, 3, 3, 1, 3, 2, 4]
def baseStart_756556 : Nat := 118140960795 + 756556 * 2 ^ 59
def prefixEnd_756556 : Nat := 4983230072969 + 3 ^ 40 * 756556 * 2
def baseEnd_756556 : Nat := 172656386685798757720297

theorem tailTrace_756556 : CollatzResearch.WordTrace tailWord_756556 prefixEnd_756556 172656386685798757720297 := by
  unfold tailWord_756556
  simp only [CollatzResearch.WordTrace]
  refine ⟨13796932123567148161508761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18395909498089530882011681 13796932123567148161508761)
  ·
    refine ⟨10347699092675361121131571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13796932123567148161508761 10347699092675361121131571)
    ·
      refine ⟨15521548639013041681697357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10347699092675361121131571 15521548639013041681697357)
      ·
        refine ⟨5820580739629890630636509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15521548639013041681697357 5820580739629890630636509)
        ·
          refine ⟨2182717777361208986488691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5820580739629890630636509 2182717777361208986488691)
          ·
            refine ⟨3274076666041813479733037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182717777361208986488691 3274076666041813479733037)
            ·
              refine ⟨1227778749765680054899889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3274076666041813479733037 1227778749765680054899889)
              ·
                refine ⟨920834062324260041174917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227778749765680054899889 920834062324260041174917)
                ·
                  refine ⟨172656386685798757720297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 920834062324260041174917 172656386685798757720297)
                  ·
                    rfl

theorem cell21_756556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_756556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756556 prefixEnd_756556 := by exact prefixLift 756556
  have htrace : WordTrace (prefixWord ++ tailWord_756556) baseStart_756556 baseEnd_756556 := by
    simpa [prefixWord, tailWord_756556, baseEnd_756556] using wordTrace_append hprefix tailTrace_756556
  have hstable : (prefixWord ++ tailWord_756556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756556).length < 2 ^ (prefixWord ++ tailWord_756556).sum := by decide
  have hdescent : baseEnd_756556 < baseStart_756556 := by decide
  rcases family_descends (prefixWord ++ tailWord_756556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756615 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 6]
def baseStart_756615 : Nat := 118140960795 + 756615 * 2 ^ 59
def prefixEnd_756615 : Nat := 4983230072969 + 3 ^ 40 * 756615 * 2
def baseEnd_756615 : Nat := 172669851289627766236843

theorem tailTrace_756615 : CollatzResearch.WordTrace tailWord_756615 prefixEnd_756615 172669851289627766236843 := by
  unfold tailWord_756615
  simp only [CollatzResearch.WordTrace]
  refine ⟨27596016153920549399415299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18397344102613699599610199 27596016153920549399415299)
  ·
    refine ⟨41394024230880824099122949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27596016153920549399415299 41394024230880824099122949)
    ·
      refine ⟨7761379543290154518585553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41394024230880824099122949 7761379543290154518585553)
      ·
        refine ⟨5821034657467615888939165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7761379543290154518585553 5821034657467615888939165)
        ·
          refine ⟨2182887996550355958352187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5821034657467615888939165 2182887996550355958352187)
          ·
            refine ⟨3274331994825533937528281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182887996550355958352187 3274331994825533937528281)
            ·
              refine ⟨2455748996119150453146211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3274331994825533937528281 2455748996119150453146211)
              ·
                refine ⟨3683623494178725679719317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2455748996119150453146211 3683623494178725679719317)
                ·
                  refine ⟨172669851289627766236843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3683623494178725679719317 172669851289627766236843)
                  ·
                    rfl

theorem cell21_756615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 6].length) (baseStart_756615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756615 prefixEnd_756615 := by exact prefixLift 756615
  have htrace : WordTrace (prefixWord ++ tailWord_756615) baseStart_756615 baseEnd_756615 := by
    simpa [prefixWord, tailWord_756615, baseEnd_756615] using wordTrace_append hprefix tailTrace_756615
  have hstable : (prefixWord ++ tailWord_756615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756615).length < 2 ^ (prefixWord ++ tailWord_756615).sum := by decide
  have hdescent : baseEnd_756615 < baseStart_756615 := by decide
  rcases family_descends (prefixWord ++ tailWord_756615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756618 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_756618 : Nat := 118140960795 + 756618 * 2 ^ 59
def prefixEnd_756618 : Nat := 4983230072969 + 3 ^ 40 * 756618 * 2
def baseEnd_756618 : Nat := 172670535930500427686837

theorem tailTrace_756618 : CollatzResearch.WordTrace tailWord_756618 prefixEnd_756618 172670535930500427686837 := by
  unfold tailWord_756618
  simp only [CollatzResearch.WordTrace]
  refine ⟨6899031393227420227943627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18397417048606453941183005 6899031393227420227943627)
  ·
    refine ⟨10348547089841130341915441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6899031393227420227943627 10348547089841130341915441)
    ·
      refine ⟨7761410317380847756436581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10348547089841130341915441 7761410317380847756436581)
      ·
        refine ⟨1455264434508908954331859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7761410317380847756436581 1455264434508908954331859)
        ·
          refine ⟨2182896651763363431497789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455264434508908954331859 2182896651763363431497789)
          ·
            refine ⟨818586244411261286811671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2182896651763363431497789 818586244411261286811671)
            ·
              refine ⟨1227879366616891930217507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818586244411261286811671 1227879366616891930217507)
              ·
                refine ⟨1841819049925337895326261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227879366616891930217507 1841819049925337895326261)
                ·
                  refine ⟨172670535930500427686837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1841819049925337895326261 172670535930500427686837)
                  ·
                    rfl

theorem cell21_756618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_756618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756618 prefixEnd_756618 := by exact prefixLift 756618
  have htrace : WordTrace (prefixWord ++ tailWord_756618) baseStart_756618 baseEnd_756618 := by
    simpa [prefixWord, tailWord_756618, baseEnd_756618] using wordTrace_append hprefix tailTrace_756618
  have hstable : (prefixWord ++ tailWord_756618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756618).length < 2 ^ (prefixWord ++ tailWord_756618).sum := by decide
  have hdescent : baseEnd_756618 < baseStart_756618 := by decide
  rcases family_descends (prefixWord ++ tailWord_756618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756629 : List Nat := [1, 3, 2, 1, 1, 4, 1, 8]
def baseStart_756629 : Nat := 118140960795 + 756629 * 2 ^ 59
def prefixEnd_756629 : Nat := 4983230072969 + 3 ^ 40 * 756629 * 2
def baseEnd_756629 : Nat := 57557682093455617667827

theorem tailTrace_756629 : CollatzResearch.WordTrace tailWord_756629 prefixEnd_756629 57557682093455617667827 := by
  unfold tailWord_756629
  simp only [CollatzResearch.WordTrace]
  refine ⟨27596526775869829790424941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18397684517246553193616627 27596526775869829790424941)
  ·
    refine ⟨10348697540951186171409353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27596526775869829790424941 10348697540951186171409353)
    ·
      refine ⟨7761523155713389628557015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10348697540951186171409353 7761523155713389628557015)
      ·
        refine ⟨11642284733570084442835523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7761523155713389628557015 11642284733570084442835523)
        ·
          refine ⟨17463427100355126664253285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11642284733570084442835523 17463427100355126664253285)
          ·
            refine ⟨3274392581316586249547491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17463427100355126664253285 3274392581316586249547491)
            ·
              refine ⟨4911588871974879374321237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3274392581316586249547491 4911588871974879374321237)
              ·
                refine ⟨57557682093455617667827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4911588871974879374321237 57557682093455617667827)
                ·
                  rfl

theorem cell21_756629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 8].length) (baseStart_756629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756629 prefixEnd_756629 := by exact prefixLift 756629
  have htrace : WordTrace (prefixWord ++ tailWord_756629) baseStart_756629 baseEnd_756629 := by
    simpa [prefixWord, tailWord_756629, baseEnd_756629] using wordTrace_append hprefix tailTrace_756629
  have hstable : (prefixWord ++ tailWord_756629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756629).length < 2 ^ (prefixWord ++ tailWord_756629).sum := by decide
  have hdescent : baseEnd_756629 < baseStart_756629 := by decide
  rcases family_descends (prefixWord ++ tailWord_756629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756694 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_756694 : Nat := 118140960795 + 756694 * 2 ^ 59
def prefixEnd_756694 : Nat := 4983230072969 + 3 ^ 40 * 756694 * 2
def baseEnd_756694 : Nat := 172687880165941184420015

theorem tailTrace_756694 : CollatzResearch.WordTrace tailWord_756694 prefixEnd_756694 172687880165941184420015 := by
  unfold tailWord_756694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1724931095039646618221321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18399265013756230594360757 1724931095039646618221321)
  ·
    refine ⟨1293698321279734963665991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1724931095039646618221321 1293698321279734963665991)
    ·
      refine ⟨1940547481919602445498987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1293698321279734963665991 1940547481919602445498987)
      ·
        refine ⟨2910821222879403668248481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1940547481919602445498987 2910821222879403668248481)
        ·
          refine ⟨2183115917159552751186361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2910821222879403668248481 2183115917159552751186361)
          ·
            refine ⟨1637336937869664563389771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2183115917159552751186361 1637336937869664563389771)
            ·
              refine ⟨2456005406804496845084657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637336937869664563389771 2456005406804496845084657)
              ·
                refine ⟨1842004055103372633813493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456005406804496845084657 1842004055103372633813493)
                ·
                  refine ⟨172687880165941184420015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1842004055103372633813493 172687880165941184420015)
                  ·
                    rfl

theorem cell21_756694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_756694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756694 prefixEnd_756694 := by exact prefixLift 756694
  have htrace : WordTrace (prefixWord ++ tailWord_756694) baseStart_756694 baseEnd_756694 := by
    simpa [prefixWord, tailWord_756694, baseEnd_756694] using wordTrace_append hprefix tailTrace_756694
  have hstable : (prefixWord ++ tailWord_756694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756694).length < 2 ^ (prefixWord ++ tailWord_756694).sum := by decide
  have hdescent : baseEnd_756694 < baseStart_756694 := by decide
  rcases family_descends (prefixWord ++ tailWord_756694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756725 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 6]
def baseStart_756725 : Nat := 118140960795 + 756725 * 2 ^ 59
def prefixEnd_756725 : Nat := 4983230072969 + 3 ^ 40 * 756725 * 2
def baseEnd_756725 : Nat := 172694954788292019403285

theorem tailTrace_756725 : CollatzResearch.WordTrace tailWord_756725 prefixEnd_756725 172694954788292019403285 := by
  unfold tailWord_756725
  simp only [CollatzResearch.WordTrace]
  refine ⟨27600028183522038185919629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18400018789014692123946419 27600028183522038185919629)
  ·
    refine ⟨10350010568820764319719861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27600028183522038185919629 10350010568820764319719861)
    ·
      refine ⟨970313490826946654973737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10350010568820764319719861 970313490826946654973737)
      ·
        refine ⟨727735118120209991230303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 970313490826946654973737 727735118120209991230303)
        ·
          refine ⟨1091602677180314986845455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727735118120209991230303 1091602677180314986845455)
          ·
            refine ⟨1637404015770472480268183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091602677180314986845455 1637404015770472480268183)
            ·
              refine ⟨2456106023655708720402275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637404015770472480268183 2456106023655708720402275)
              ·
                refine ⟨3684159035483563080603413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2456106023655708720402275 3684159035483563080603413)
                ·
                  refine ⟨172694954788292019403285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3684159035483563080603413 172694954788292019403285)
                  ·
                    rfl

theorem cell21_756725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_756725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756725 prefixEnd_756725 := by exact prefixLift 756725
  have htrace : WordTrace (prefixWord ++ tailWord_756725) baseStart_756725 baseEnd_756725 := by
    simpa [prefixWord, tailWord_756725, baseEnd_756725] using wordTrace_append hprefix tailTrace_756725
  have hstable : (prefixWord ++ tailWord_756725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756725).length < 2 ^ (prefixWord ++ tailWord_756725).sum := by decide
  have hdescent : baseEnd_756725 < baseStart_756725 := by decide
  rcases family_descends (prefixWord ++ tailWord_756725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756770 : List Nat := [3, 3, 1, 1, 1, 3, 3, 3, 3]
def baseStart_756770 : Nat := 118140960795 + 756770 * 2 ^ 59
def prefixEnd_756770 : Nat := 4983230072969 + 3 ^ 40 * 756770 * 2
def baseEnd_756770 : Nat := 172705224401381941153193

theorem tailTrace_756770 : CollatzResearch.WordTrace tailWord_756770 prefixEnd_756770 172705224401381941153193 := by
  unfold tailWord_756770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6900417367089752717826941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18401112978906007247538509 6900417367089752717826941)
  ·
    refine ⟨2587656512658657269185103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6900417367089752717826941 2587656512658657269185103)
    ·
      refine ⟨3881484768987985903777655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2587656512658657269185103 3881484768987985903777655)
      ·
        refine ⟨5822227153481978855666483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3881484768987985903777655 5822227153481978855666483)
        ·
          refine ⟨8733340730222968283499725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5822227153481978855666483 8733340730222968283499725)
          ·
            refine ⟨3275002773833613106312397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8733340730222968283499725 3275002773833613106312397)
            ·
              refine ⟨1228126040187604914867149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3275002773833613106312397 1228126040187604914867149)
              ·
                refine ⟨460547265070351843075181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1228126040187604914867149 460547265070351843075181)
                ·
                  refine ⟨172705224401381941153193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460547265070351843075181 172705224401381941153193)
                  ·
                    rfl

theorem cell21_756770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_756770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756770 prefixEnd_756770 := by exact prefixLift 756770
  have htrace : WordTrace (prefixWord ++ tailWord_756770) baseStart_756770 baseEnd_756770 := by
    simpa [prefixWord, tailWord_756770, baseEnd_756770] using wordTrace_append hprefix tailTrace_756770
  have hstable : (prefixWord ++ tailWord_756770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756770).length < 2 ^ (prefixWord ++ tailWord_756770).sum := by decide
  have hdescent : baseEnd_756770 < baseStart_756770 := by decide
  rcases family_descends (prefixWord ++ tailWord_756770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756798 : List Nat := [4, 2, 1, 3, 1, 1, 1, 8]
def baseStart_756798 : Nat := 118140960795 + 756798 * 2 ^ 59
def prefixEnd_756798 : Nat := 4983230072969 + 3 ^ 40 * 756798 * 2
def baseEnd_756798 : Nat := 57570538127620038228823

theorem tailTrace_756798 : CollatzResearch.WordTrace tailWord_756798 prefixEnd_756798 57570538127620038228823 := by
  unfold tailWord_756798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3450336339032196456665881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18401793808171714435551365 3450336339032196456665881)
  ·
    refine ⟨2587752254274147342499411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3450336339032196456665881 2587752254274147342499411)
    ·
      refine ⟨3881628381411221013749117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2587752254274147342499411 3881628381411221013749117)
      ·
        refine ⟨1455610643029207880155919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3881628381411221013749117 1455610643029207880155919)
        ·
          refine ⟨2183415964543811820233879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455610643029207880155919 2183415964543811820233879)
          ·
            refine ⟨3275123946815717730350819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183415964543811820233879 3275123946815717730350819)
            ·
              refine ⟨4912685920223576595526229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3275123946815717730350819 4912685920223576595526229)
              ·
                refine ⟨57570538127620038228823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4912685920223576595526229 57570538127620038228823)
                ·
                  rfl

theorem cell21_756798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_756798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756798 prefixEnd_756798 := by exact prefixLift 756798
  have htrace : WordTrace (prefixWord ++ tailWord_756798) baseStart_756798 baseEnd_756798 := by
    simpa [prefixWord, tailWord_756798, baseEnd_756798] using wordTrace_append hprefix tailTrace_756798
  have hstable : (prefixWord ++ tailWord_756798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756798).length < 2 ^ (prefixWord ++ tailWord_756798).sum := by decide
  have hdescent : baseEnd_756798 < baseStart_756798 := by decide
  rcases family_descends (prefixWord ++ tailWord_756798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756826 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_756826 : Nat := 118140960795 + 756826 * 2 ^ 59
def prefixEnd_756826 : Nat := 4983230072969 + 3 ^ 40 * 756826 * 2
def baseEnd_756826 : Nat := 172718004364338288219745

theorem tailTrace_756826 : CollatzResearch.WordTrace tailWord_756826 prefixEnd_756826 172718004364338288219745 := by
  unfold tailWord_756826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6900927989039033108836583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18402474637437421623564221 6900927989039033108836583)
  ·
    refine ⟨10351391983558549663254875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6900927989039033108836583 10351391983558549663254875)
    ·
      refine ⟨15527087975337824494882313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10351391983558549663254875 15527087975337824494882313)
      ·
        refine ⟨11645315981503368371161735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15527087975337824494882313 11645315981503368371161735)
        ·
          refine ⟨17467973972255052556742603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11645315981503368371161735 17467973972255052556742603)
          ·
            refine ⟨26201960958382578835113905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17467973972255052556742603 26201960958382578835113905)
            ·
              refine ⟨19651470718786934126335429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26201960958382578835113905 19651470718786934126335429)
              ·
                refine ⟨3684650759772550148687893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19651470718786934126335429 3684650759772550148687893)
                ·
                  refine ⟨172718004364338288219745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3684650759772550148687893 172718004364338288219745)
                  ·
                    rfl

theorem cell21_756826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_756826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756826 prefixEnd_756826 := by exact prefixLift 756826
  have htrace : WordTrace (prefixWord ++ tailWord_756826) baseStart_756826 baseEnd_756826 := by
    simpa [prefixWord, tailWord_756826, baseEnd_756826] using wordTrace_append hprefix tailTrace_756826
  have hstable : (prefixWord ++ tailWord_756826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756826).length < 2 ^ (prefixWord ++ tailWord_756826).sum := by decide
  have hdescent : baseEnd_756826 < baseStart_756826 := by decide
  rcases family_descends (prefixWord ++ tailWord_756826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756846 : List Nat := [4, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_756846 : Nat := 118140960795 + 756846 * 2 ^ 59
def prefixEnd_756846 : Nat := 4983230072969 + 3 ^ 40 * 756846 * 2
def baseEnd_756846 : Nat := 172722568636822697886371

theorem tailTrace_756846 : CollatzResearch.WordTrace tailWord_756846 prefixEnd_756846 172722568636822697886371 := by
  unfold tailWord_756846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3450555177010459481384299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18402960944055783900716261 3450555177010459481384299)
  ·
    refine ⟨5175832765515689222076449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3450555177010459481384299 5175832765515689222076449)
    ·
      refine ⟨3881874574136766916557337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5175832765515689222076449 3881874574136766916557337)
      ·
        refine ⟨2911405930602575187418003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3881874574136766916557337 2911405930602575187418003)
        ·
          refine ⟨4367108895903862781127005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2911405930602575187418003 4367108895903862781127005)
          ·
            refine ⟨1637665835963948542922627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4367108895903862781127005 1637665835963948542922627)
            ·
              refine ⟨2456498753945922814383941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637665835963948542922627 2456498753945922814383941)
              ·
                refine ⟨460593516364860527696989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2456498753945922814383941 460593516364860527696989)
                ·
                  refine ⟨172722568636822697886371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460593516364860527696989 172722568636822697886371)
                  ·
                    rfl

theorem cell21_756846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_756846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756846 prefixEnd_756846 := by exact prefixLift 756846
  have htrace : WordTrace (prefixWord ++ tailWord_756846) baseStart_756846 baseEnd_756846 := by
    simpa [prefixWord, tailWord_756846, baseEnd_756846] using wordTrace_append hprefix tailTrace_756846
  have hstable : (prefixWord ++ tailWord_756846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756846).length < 2 ^ (prefixWord ++ tailWord_756846).sum := by decide
  have hdescent : baseEnd_756846 < baseStart_756846 := by decide
  rcases family_descends (prefixWord ++ tailWord_756846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756874 : List Nat := [3, 1, 2, 3, 1, 1, 5, 5]
def baseStart_756874 : Nat := 118140960795 + 756874 * 2 ^ 59
def prefixEnd_756874 : Nat := 4983230072969 + 3 ^ 40 * 756874 * 2
def baseEnd_756874 : Nat := 57576319539433623806549

theorem tailTrace_756874 : CollatzResearch.WordTrace tailWord_756874 prefixEnd_756874 57576319539433623806549 := by
  unfold tailWord_756874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6901365664995559158273419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18403641773321491088729117 6901365664995559158273419)
  ·
    refine ⟨10352048497493338737410129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6901365664995559158273419 10352048497493338737410129)
    ·
      refine ⟨7764036373120004053057597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10352048497493338737410129 7764036373120004053057597)
      ·
        refine ⟨2911513639920001519896599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7764036373120004053057597 2911513639920001519896599)
        ·
          refine ⟨4367270459880002279844899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2911513639920001519896599 4367270459880002279844899)
          ·
            refine ⟨6550905689820003419767349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4367270459880002279844899 6550905689820003419767349)
            ·
              refine ⟨614147408420625320603189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6550905689820003419767349 614147408420625320603189)
              ·
                refine ⟨57576319539433623806549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 614147408420625320603189 57576319539433623806549)
                ·
                  rfl

theorem cell21_756874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_756874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756874 prefixEnd_756874 := by exact prefixLift 756874
  have htrace : WordTrace (prefixWord ++ tailWord_756874) baseStart_756874 baseEnd_756874 := by
    simpa [prefixWord, tailWord_756874, baseEnd_756874] using wordTrace_append hprefix tailTrace_756874
  have hstable : (prefixWord ++ tailWord_756874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756874).length < 2 ^ (prefixWord ++ tailWord_756874).sum := by decide
  have hdescent : baseEnd_756874 < baseStart_756874 := by decide
  rcases family_descends (prefixWord ++ tailWord_756874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756964 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 5]
def baseStart_756964 : Nat := 118140960795 + 756964 * 2 ^ 59
def prefixEnd_756964 : Nat := 4983230072969 + 3 ^ 40 * 756964 * 2
def baseEnd_756964 : Nat := 172749497844480714919463

theorem tailTrace_756964 : CollatzResearch.WordTrace tailWord_756964 prefixEnd_756964 172749497844480714919463 := by
  unfold tailWord_756964
  simp only [CollatzResearch.WordTrace]
  refine ⟨13804372614828091001934973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18405830153104121335913297 13804372614828091001934973)
  ·
    refine ⟨5176639730560534125725615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13804372614828091001934973 5176639730560534125725615)
    ·
      refine ⟨7764959595840801188588423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5176639730560534125725615 7764959595840801188588423)
      ·
        refine ⟨11647439393761201782882635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7764959595840801188588423 11647439393761201782882635)
        ·
          refine ⟨17471159090641802674323953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11647439393761201782882635 17471159090641802674323953)
          ·
            refine ⟨13103369317981352005742965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17471159090641802674323953 13103369317981352005742965)
            ·
              refine ⟨1228440873560751750538403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13103369317981352005742965 1228440873560751750538403)
              ·
                refine ⟨1842661310341127625807605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228440873560751750538403 1842661310341127625807605)
                ·
                  refine ⟨172749497844480714919463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1842661310341127625807605 172749497844480714919463)
                  ·
                    rfl

theorem cell21_756964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_756964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756964 prefixEnd_756964 := by exact prefixLift 756964
  have htrace : WordTrace (prefixWord ++ tailWord_756964) baseStart_756964 baseEnd_756964 := by
    simpa [prefixWord, tailWord_756964, baseEnd_756964] using wordTrace_append hprefix tailTrace_756964
  have hstable : (prefixWord ++ tailWord_756964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756964).length < 2 ^ (prefixWord ++ tailWord_756964).sum := by decide
  have hdescent : baseEnd_756964 < baseStart_756964 := by decide
  rcases family_descends (prefixWord ++ tailWord_756964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757088 : List Nat := [2, 1, 1, 3, 4, 2, 3, 1, 4]
def baseStart_757088 : Nat := 118140960795 + 757088 * 2 ^ 59
def prefixEnd_757088 : Nat := 4983230072969 + 3 ^ 40 * 757088 * 2
def baseEnd_757088 : Nat := 172777796333884054852543

theorem tailTrace_757088 : CollatzResearch.WordTrace tailWord_757088 prefixEnd_757088 172777796333884054852543 := by
  unfold tailWord_757088
  simp only [CollatzResearch.WordTrace]
  refine ⟨13806633940603475590691959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18408845254137967454255945 13806633940603475590691959)
  ·
    refine ⟨20709950910905213386037939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13806633940603475590691959 20709950910905213386037939)
    ·
      refine ⟨31064926366357820079056909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20709950910905213386037939 31064926366357820079056909)
      ·
        refine ⟨11649347387384182529646341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31064926366357820079056909 11649347387384182529646341)
        ·
          refine ⟨2184252635134534224308689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11649347387384182529646341 2184252635134534224308689)
          ·
            refine ⟨1638189476350900668231517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2184252635134534224308689 1638189476350900668231517)
            ·
              refine ⟨614321053631587750586819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1638189476350900668231517 614321053631587750586819)
              ·
                refine ⟨921481580447381625880229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614321053631587750586819 921481580447381625880229)
                ·
                  refine ⟨172777796333884054852543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 921481580447381625880229 172777796333884054852543)
                  ·
                    rfl

theorem cell21_757088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_757088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757088 prefixEnd_757088 := by exact prefixLift 757088
  have htrace : WordTrace (prefixWord ++ tailWord_757088) baseStart_757088 baseEnd_757088 := by
    simpa [prefixWord, tailWord_757088, baseEnd_757088] using wordTrace_append hprefix tailTrace_757088
  have hstable : (prefixWord ++ tailWord_757088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757088).length < 2 ^ (prefixWord ++ tailWord_757088).sum := by decide
  have hdescent : baseEnd_757088 < baseStart_757088 := by decide
  rcases family_descends (prefixWord ++ tailWord_757088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757220 : List Nat := [2, 3, 1, 1, 1, 1, 1, 11]
def baseStart_757220 : Nat := 118140960795 + 757220 * 2 ^ 59
def prefixEnd_757220 : Nat := 4983230072969 + 3 ^ 40 * 757220 * 2
def baseEnd_757220 : Nat := 57602640177427052884091

theorem tailTrace_757220 : CollatzResearch.WordTrace tailWord_757220 prefixEnd_757220 57602640177427052884091 := by
  unfold tailWord_757220
  simp only [CollatzResearch.WordTrace]
  refine ⟨13809041158364368862594557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18412054877819158483459409 13809041158364368862594557)
  ·
    refine ⟨5178390434386638323472959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13809041158364368862594557 5178390434386638323472959)
    ·
      refine ⟨7767585651579957485209439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5178390434386638323472959 7767585651579957485209439)
      ·
        refine ⟨11651378477369936227814159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7767585651579957485209439 11651378477369936227814159)
        ·
          refine ⟨17477067716054904341721239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11651378477369936227814159 17477067716054904341721239)
          ·
            refine ⟨26215601574082356512581859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17477067716054904341721239 26215601574082356512581859)
            ·
              refine ⟨39323402361123534768872789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26215601574082356512581859 39323402361123534768872789)
              ·
                refine ⟨57602640177427052884091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 39323402361123534768872789 57602640177427052884091)
                ·
                  rfl

theorem cell21_757220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_757220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757220 prefixEnd_757220 := by exact prefixLift 757220
  have htrace : WordTrace (prefixWord ++ tailWord_757220) baseStart_757220 baseEnd_757220 := by
    simpa [prefixWord, tailWord_757220, baseEnd_757220] using wordTrace_append hprefix tailTrace_757220
  have hstable : (prefixWord ++ tailWord_757220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757220).length < 2 ^ (prefixWord ++ tailWord_757220).sum := by decide
  have hdescent : baseEnd_757220 < baseStart_757220 := by decide
  rcases family_descends (prefixWord ++ tailWord_757220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757226 : List Nat := [3, 1, 3, 1, 4, 1, 2, 3, 3]
def baseStart_757226 : Nat := 118140960795 + 757226 * 2 ^ 59
def prefixEnd_757226 : Nat := 4983230072969 + 3 ^ 40 * 757226 * 2
def baseEnd_757226 : Nat := 172809289814026481552261

theorem tailTrace_757226 : CollatzResearch.WordTrace tailWord_757226 prefixEnd_757226 172809289814026481552261 := by
  unfold tailWord_757226
  simp only [CollatzResearch.WordTrace]
  refine ⟨6904575288676750187476883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18412200769804667166605021 6904575288676750187476883)
  ·
    refine ⟨10356862933015125281215325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6904575288676750187476883 10356862933015125281215325)
    ·
      refine ⟨3883823599880671980455747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10356862933015125281215325 3883823599880671980455747)
      ·
        refine ⟨5825735399821007970683621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3883823599880671980455747 5825735399821007970683621)
        ·
          refine ⟨1092325387466438994503179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5825735399821007970683621 1092325387466438994503179)
          ·
            refine ⟨1638488081199658491754769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092325387466438994503179 1638488081199658491754769)
            ·
              refine ⟨1228866060899743868816077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1638488081199658491754769 1228866060899743868816077)
              ·
                refine ⟨460824772837403950806029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1228866060899743868816077 460824772837403950806029)
                ·
                  refine ⟨172809289814026481552261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460824772837403950806029 172809289814026481552261)
                  ·
                    rfl

theorem cell21_757226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_757226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757226 prefixEnd_757226 := by exact prefixLift 757226
  have htrace : WordTrace (prefixWord ++ tailWord_757226) baseStart_757226 baseEnd_757226 := by
    simpa [prefixWord, tailWord_757226, baseEnd_757226] using wordTrace_append hprefix tailTrace_757226
  have hstable : (prefixWord ++ tailWord_757226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757226).length < 2 ^ (prefixWord ++ tailWord_757226).sum := by decide
  have hdescent : baseEnd_757226 < baseStart_757226 := by decide
  rcases family_descends (prefixWord ++ tailWord_757226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757282 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_757282 : Nat := 118140960795 + 757282 * 2 ^ 59
def prefixEnd_757282 : Nat := 4983230072969 + 3 ^ 40 * 757282 * 2
def baseEnd_757282 : Nat := 172822069776982828618813

theorem tailTrace_757282 : CollatzResearch.WordTrace tailWord_757282 prefixEnd_757282 172822069776982828618813 := by
  unfold tailWord_757282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6905085910626030578486525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18413562428336081542630733 6905085910626030578486525)
  ·
    refine ⟨2589407216484761466932447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6905085910626030578486525 2589407216484761466932447)
    ·
      refine ⟨3884110824727142200398671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2589407216484761466932447 3884110824727142200398671)
      ·
        refine ⟨5826166237090713300598007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3884110824727142200398671 5826166237090713300598007)
        ·
          refine ⟨8739249355636069950897011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826166237090713300598007 8739249355636069950897011)
          ·
            refine ⟨13108874033454104926345517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8739249355636069950897011 13108874033454104926345517)
            ·
              refine ⟨4915827762545289347379569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13108874033454104926345517 4915827762545289347379569)
              ·
                refine ⟨3686870821908967010534677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4915827762545289347379569 3686870821908967010534677)
                ·
                  refine ⟨172822069776982828618813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3686870821908967010534677 172822069776982828618813)
                  ·
                    rfl

theorem cell21_757282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_757282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757282 prefixEnd_757282 := by exact prefixLift 757282
  have htrace : WordTrace (prefixWord ++ tailWord_757282) baseStart_757282 baseEnd_757282 := by
    simpa [prefixWord, tailWord_757282, baseEnd_757282] using wordTrace_append hprefix tailTrace_757282
  have hstable : (prefixWord ++ tailWord_757282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757282).length < 2 ^ (prefixWord ++ tailWord_757282).sum := by decide
  have hdescent : baseEnd_757282 < baseStart_757282 := by decide
  rcases family_descends (prefixWord ++ tailWord_757282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757302 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_757302 : Nat := 118140960795 + 757302 * 2 ^ 59
def prefixEnd_757302 : Nat := 4983230072969 + 3 ^ 40 * 757302 * 2
def baseEnd_757302 : Nat := 172826634049467238285439

theorem tailTrace_757302 : CollatzResearch.WordTrace tailWord_757302 prefixEnd_757302 172826634049467238285439 := by
  unfold tailWord_757302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1726317068901979108104635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18414048734954443819782773 1726317068901979108104635)
  ·
    refine ⟨2589475603352968662156953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1726317068901979108104635 2589475603352968662156953)
    ·
      refine ⟨1942106702514726496617715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2589475603352968662156953 1942106702514726496617715)
      ·
        refine ⟨2913160053772089744926573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1942106702514726496617715 2913160053772089744926573)
        ·
          refine ⟨1092435020164533654347465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2913160053772089744926573 1092435020164533654347465)
          ·
            refine ⟨819326265123400240760599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1092435020164533654347465 819326265123400240760599)
            ·
              refine ⟨1228989397685100361140899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819326265123400240760599 1228989397685100361140899)
              ·
                refine ⟨1843484096527650541711349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228989397685100361140899 1843484096527650541711349)
                ·
                  refine ⟨172826634049467238285439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1843484096527650541711349 172826634049467238285439)
                  ·
                    rfl

theorem cell21_757302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_757302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757302 prefixEnd_757302 := by exact prefixLift 757302
  have htrace : WordTrace (prefixWord ++ tailWord_757302) baseStart_757302 baseEnd_757302 := by
    simpa [prefixWord, tailWord_757302, baseEnd_757302] using wordTrace_append hprefix tailTrace_757302
  have hstable : (prefixWord ++ tailWord_757302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757302).length < 2 ^ (prefixWord ++ tailWord_757302).sum := by decide
  have hdescent : baseEnd_757302 < baseStart_757302 := by decide
  rcases family_descends (prefixWord ++ tailWord_757302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757313 : List Nat := [1, 2, 5, 1, 1, 1, 4, 6]
def baseStart_757313 : Nat := 118140960795 + 757313 * 2 ^ 59
def prefixEnd_757313 : Nat := 4983230072969 + 3 ^ 40 * 757313 * 2
def baseEnd_757313 : Nat := 57609714799777887867361

theorem tailTrace_757313 : CollatzResearch.WordTrace tailWord_757313 prefixEnd_757313 57609714799777887867361 := by
  unfold tailWord_757313
  simp only [CollatzResearch.WordTrace]
  refine ⟨27621474305391814608324593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18414316203594543072216395 27621474305391814608324593)
  ·
    refine ⟨20716105729043860956243445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27621474305391814608324593 20716105729043860956243445)
    ·
      refine ⟨1942134912097861964647823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20716105729043860956243445 1942134912097861964647823)
      ·
        refine ⟨2913202368146792946971735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1942134912097861964647823 2913202368146792946971735)
        ·
          refine ⟨4369803552220189420457603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2913202368146792946971735 4369803552220189420457603)
          ·
            refine ⟨6554705328330284130686405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4369803552220189420457603 6554705328330284130686405)
            ·
              refine ⟨1229007249061928274503701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6554705328330284130686405 1229007249061928274503701)
              ·
                refine ⟨57609714799777887867361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1229007249061928274503701 57609714799777887867361)
                ·
                  rfl

theorem cell21_757313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 6].length) (baseStart_757313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757313 prefixEnd_757313 := by exact prefixLift 757313
  have htrace : WordTrace (prefixWord ++ tailWord_757313) baseStart_757313 baseEnd_757313 := by
    simpa [prefixWord, tailWord_757313, baseEnd_757313] using wordTrace_append hprefix tailTrace_757313
  have hstable : (prefixWord ++ tailWord_757313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757313).length < 2 ^ (prefixWord ++ tailWord_757313).sum := by decide
  have hdescent : baseEnd_757313 < baseStart_757313 := by decide
  rcases family_descends (prefixWord ++ tailWord_757313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757344 : List Nat := [2, 1, 1, 3, 2, 1, 1, 7, 3]
def baseStart_757344 : Nat := 118140960795 + 757344 * 2 ^ 59
def prefixEnd_757344 : Nat := 4983230072969 + 3 ^ 40 * 757344 * 2
def baseEnd_757344 : Nat := 172836219021684498585353

theorem tailTrace_757344 : CollatzResearch.WordTrace tailWord_757344 prefixEnd_757344 172836219021684498585353 := by
  unfold tailWord_757344
  simp only [CollatzResearch.WordTrace]
  refine ⟨13811302484139753451351543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18415069978853004601802057 13811302484139753451351543)
  ·
    refine ⟨20716953726209630177027315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13811302484139753451351543 20716953726209630177027315)
    ·
      refine ⟨31075430589314445265540973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20716953726209630177027315 31075430589314445265540973)
      ·
        refine ⟨11653286470992916974577865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31075430589314445265540973 11653286470992916974577865)
        ·
          refine ⟨8739964853244687730933399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11653286470992916974577865 8739964853244687730933399)
          ·
            refine ⟨13109947279867031596400099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8739964853244687730933399 13109947279867031596400099)
            ·
              refine ⟨19664920919800547394600149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13109947279867031596400099 19664920919800547394600149)
              ·
                refine ⟨460896584057825329560941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19664920919800547394600149 460896584057825329560941)
                ·
                  refine ⟨172836219021684498585353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460896584057825329560941 172836219021684498585353)
                  ·
                    rfl

theorem cell21_757344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 3].length) (baseStart_757344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757344 prefixEnd_757344 := by exact prefixLift 757344
  have htrace : WordTrace (prefixWord ++ tailWord_757344) baseStart_757344 baseEnd_757344 := by
    simpa [prefixWord, tailWord_757344, baseEnd_757344] using wordTrace_append hprefix tailTrace_757344
  have hstable : (prefixWord ++ tailWord_757344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757344).length < 2 ^ (prefixWord ++ tailWord_757344).sum := by decide
  have hdescent : baseEnd_757344 < baseStart_757344 := by decide
  rcases family_descends (prefixWord ++ tailWord_757344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757448 : List Nat := [2, 1, 3, 1, 2, 2, 3, 7]
def baseStart_757448 : Nat := 118140960795 + 757448 * 2 ^ 59
def prefixEnd_757448 : Nat := 4983230072969 + 3 ^ 40 * 757448 * 2
def baseEnd_757448 : Nat := 57619984412867809617269

theorem tailTrace_757448 : CollatzResearch.WordTrace tailWord_757448 prefixEnd_757448 57619984412867809617269 := by
  unfold tailWord_757448
  simp only [CollatzResearch.WordTrace]
  refine ⟨13813199079951366332244499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18417598773268488442992665 13813199079951366332244499)
  ·
    refine ⟨20719798619927049498366749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13813199079951366332244499 20719798619927049498366749)
    ·
      refine ⟨7769924482472643561887531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20719798619927049498366749 7769924482472643561887531)
      ·
        refine ⟨11654886723708965342831297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7769924482472643561887531 11654886723708965342831297)
        ·
          refine ⟨8741165042781724007123473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11654886723708965342831297 8741165042781724007123473)
          ·
            refine ⟨6555873782086293005342605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8741165042781724007123473 6555873782086293005342605)
            ·
              refine ⟨2458452668282359877003477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6555873782086293005342605 2458452668282359877003477)
              ·
                refine ⟨57619984412867809617269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2458452668282359877003477 57619984412867809617269)
                ·
                  rfl

theorem cell21_757448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_757448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757448 prefixEnd_757448 := by exact prefixLift 757448
  have htrace : WordTrace (prefixWord ++ tailWord_757448) baseStart_757448 baseEnd_757448 := by
    simpa [prefixWord, tailWord_757448, baseEnd_757448] using wordTrace_append hprefix tailTrace_757448
  have hstable : (prefixWord ++ tailWord_757448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757448).length < 2 ^ (prefixWord ++ tailWord_757448).sum := by decide
  have hdescent : baseEnd_757448 < baseStart_757448 := by decide
  rcases family_descends (prefixWord ++ tailWord_757448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757527 : List Nat := [1, 1, 3, 4, 2, 2, 2, 2, 4]
def baseStart_757527 : Nat := 118140960795 + 757527 * 2 ^ 59
def prefixEnd_757527 : Nat := 4983230072969 + 3 ^ 40 * 757527 * 2
def baseEnd_757527 : Nat := 172877982114916847034979

theorem tailTrace_757527 : CollatzResearch.WordTrace tailWord_757527 prefixEnd_757527 172877982114916847034979 := by
  unfold tailWord_757527
  simp only [CollatzResearch.WordTrace]
  refine ⟨27629279526616529156614835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18419519684411019437743223 27629279526616529156614835)
  ·
    refine ⟨41443919289924793734922253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27629279526616529156614835 41443919289924793734922253)
    ·
      refine ⟨15541469733721797650595845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41443919289924793734922253 15541469733721797650595845)
      ·
        refine ⟨2914025575072837059486721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15541469733721797650595845 2914025575072837059486721)
        ·
          refine ⟨2185519181304627794615041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2914025575072837059486721 2185519181304627794615041)
          ·
            refine ⟨1639139385978470845961281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2185519181304627794615041 1639139385978470845961281)
            ·
              refine ⟨1229354539483853134470961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1639139385978470845961281 1229354539483853134470961)
              ·
                refine ⟨922015904612889850853221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1229354539483853134470961 922015904612889850853221)
                ·
                  refine ⟨172877982114916847034979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 922015904612889850853221 172877982114916847034979)
                  ·
                    rfl

theorem cell21_757527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 4].length) (baseStart_757527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757527 prefixEnd_757527 := by exact prefixLift 757527
  have htrace : WordTrace (prefixWord ++ tailWord_757527) baseStart_757527 baseEnd_757527 := by
    simpa [prefixWord, tailWord_757527, baseEnd_757527] using wordTrace_append hprefix tailTrace_757527
  have hstable : (prefixWord ++ tailWord_757527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757527).length < 2 ^ (prefixWord ++ tailWord_757527).sum := by decide
  have hdescent : baseEnd_757527 < baseStart_757527 := by decide
  rcases family_descends (prefixWord ++ tailWord_757527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757530 : List Nat := [3, 1, 1, 3, 2, 4, 2, 2, 3]
def baseStart_757530 : Nat := 118140960795 + 757530 * 2 ^ 59
def prefixEnd_757530 : Nat := 4983230072969 + 3 ^ 40 * 757530 * 2
def baseEnd_757530 : Nat := 172878666755789508484973

theorem tailTrace_757530 : CollatzResearch.WordTrace tailWord_757530 prefixEnd_757530 172878666755789508484973 := by
  unfold tailWord_757530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6907347236401415167243511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18419592630403773779316029 6907347236401415167243511)
  ·
    refine ⟨10361020854602122750865267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6907347236401415167243511 10361020854602122750865267)
    ·
      refine ⟨15541531281903184126297901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10361020854602122750865267 15541531281903184126297901)
      ·
        refine ⟨5828074230713694047361713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15541531281903184126297901 5828074230713694047361713)
        ·
          refine ⟨4371055673035270535521285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5828074230713694047361713 4371055673035270535521285)
          ·
            refine ⟨819572938694113225410241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4371055673035270535521285 819572938694113225410241)
            ·
              refine ⟨614679704020584919057681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819572938694113225410241 614679704020584919057681)
              ·
                refine ⟨461009778015438689293261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 614679704020584919057681 461009778015438689293261)
                ·
                  refine ⟨172878666755789508484973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461009778015438689293261 172878666755789508484973)
                  ·
                    rfl

theorem cell21_757530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_757530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757530 prefixEnd_757530 := by exact prefixLift 757530
  have htrace : WordTrace (prefixWord ++ tailWord_757530) baseStart_757530 baseEnd_757530 := by
    simpa [prefixWord, tailWord_757530, baseEnd_757530] using wordTrace_append hprefix tailTrace_757530
  have hstable : (prefixWord ++ tailWord_757530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757530).length < 2 ^ (prefixWord ++ tailWord_757530).sum := by decide
  have hdescent : baseEnd_757530 < baseStart_757530 := by decide
  rcases family_descends (prefixWord ++ tailWord_757530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757541 : List Nat := [1, 3, 1, 2, 3, 4, 1, 6]
def baseStart_757541 : Nat := 118140960795 + 757541 * 2 ^ 59
def prefixEnd_757541 : Nat := 4983230072969 + 3 ^ 40 * 757541 * 2
def baseEnd_757541 : Nat := 57627059035218644600539

theorem tailTrace_757541 : CollatzResearch.WordTrace tailWord_757541 prefixEnd_757541 57627059035218644600539 := by
  unfold tailWord_757541
  simp only [CollatzResearch.WordTrace]
  refine ⟨27629790148565809547624477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18419860099043873031749651 27629790148565809547624477)
  ·
    refine ⟨10361171305712178580359179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27629790148565809547624477 10361171305712178580359179)
    ·
      refine ⟨15541756958568267870538769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10361171305712178580359179 15541756958568267870538769)
      ·
        refine ⟨11656317718926200902904077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15541756958568267870538769 11656317718926200902904077)
        ·
          refine ⟨4371119144597325338589029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11656317718926200902904077 4371119144597325338589029)
          ·
            refine ⟨819584839611998500985443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4371119144597325338589029 819584839611998500985443)
            ·
              refine ⟨1229377259417997751478165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819584839611998500985443 1229377259417997751478165)
              ·
                refine ⟨57627059035218644600539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1229377259417997751478165 57627059035218644600539)
                ·
                  rfl

theorem cell21_757541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 6].length) (baseStart_757541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757541 prefixEnd_757541 := by exact prefixLift 757541
  have htrace : WordTrace (prefixWord ++ tailWord_757541) baseStart_757541 baseEnd_757541 := by
    simpa [prefixWord, tailWord_757541, baseEnd_757541] using wordTrace_append hprefix tailTrace_757541
  have hstable : (prefixWord ++ tailWord_757541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757541).length < 2 ^ (prefixWord ++ tailWord_757541).sum := by decide
  have hdescent : baseEnd_757541 < baseStart_757541 := by decide
  rcases family_descends (prefixWord ++ tailWord_757541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757586 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_757586 : Nat := 118140960795 + 757586 * 2 ^ 59
def prefixEnd_757586 : Nat := 4983230072969 + 3 ^ 40 * 757586 * 2
def baseEnd_757586 : Nat := 172891446718745855551525

theorem tailTrace_757586 : CollatzResearch.WordTrace tailWord_757586 prefixEnd_757586 172891446718745855551525 := by
  unfold tailWord_757586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6907857858350695558253153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18420954288935188155341741 6907857858350695558253153)
  ·
    refine ⟨5180893393763021668689865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6907857858350695558253153 5180893393763021668689865)
    ·
      refine ⟨3885670045322266251517399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5180893393763021668689865 3885670045322266251517399)
      ·
        refine ⟨5828505067983399377276099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3885670045322266251517399 5828505067983399377276099)
        ·
          refine ⟨8742757601975099065914149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5828505067983399377276099 8742757601975099065914149)
          ·
            refine ⟨1639267050370331074858903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8742757601975099065914149 1639267050370331074858903)
            ·
              refine ⟨2458900575555496612288355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639267050370331074858903 2458900575555496612288355)
              ·
                refine ⟨3688350863333244918432533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2458900575555496612288355 3688350863333244918432533)
                ·
                  refine ⟨172891446718745855551525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3688350863333244918432533 172891446718745855551525)
                  ·
                    rfl

theorem cell21_757586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_757586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757586 prefixEnd_757586 := by exact prefixLift 757586
  have htrace : WordTrace (prefixWord ++ tailWord_757586) baseStart_757586 baseEnd_757586 := by
    simpa [prefixWord, tailWord_757586, baseEnd_757586] using wordTrace_append hprefix tailTrace_757586
  have hstable : (prefixWord ++ tailWord_757586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757586).length < 2 ^ (prefixWord ++ tailWord_757586).sum := by decide
  have hdescent : baseEnd_757586 < baseStart_757586 := by decide
  rcases family_descends (prefixWord ++ tailWord_757586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757690 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_757690 : Nat := 118140960795 + 757690 * 2 ^ 59
def prefixEnd_757690 : Nat := 4983230072969 + 3 ^ 40 * 757690 * 2
def baseEnd_757690 : Nat := 172915180935664785817979

theorem tailTrace_757690 : CollatzResearch.WordTrace tailWord_757690 prefixEnd_757690 172915180935664785817979 := by
  unfold tailWord_757690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6908806156256501998699631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18423483083350671996532349 6908806156256501998699631)
  ·
    refine ⟨10363209234384752998049447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6908806156256501998699631 10363209234384752998049447)
    ·
      refine ⟨15544813851577129497074171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10363209234384752998049447 15544813851577129497074171)
      ·
        refine ⟨23317220777365694245611257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15544813851577129497074171 23317220777365694245611257)
        ·
          refine ⟨17487915583024270684208443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23317220777365694245611257 17487915583024270684208443)
          ·
            refine ⟨26231873374536406026312665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17487915583024270684208443 26231873374536406026312665)
            ·
              refine ⟨19673905030902304519734499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26231873374536406026312665 19673905030902304519734499)
              ·
                refine ⟨29510857546353456779601749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19673905030902304519734499 29510857546353456779601749)
                ·
                  refine ⟨172915180935664785817979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29510857546353456779601749 172915180935664785817979)
                  ·
                    rfl

theorem cell21_757690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_757690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757690 prefixEnd_757690 := by exact prefixLift 757690
  have htrace : WordTrace (prefixWord ++ tailWord_757690) baseStart_757690 baseEnd_757690 := by
    simpa [prefixWord, tailWord_757690, baseEnd_757690] using wordTrace_append hprefix tailTrace_757690
  have hstable : (prefixWord ++ tailWord_757690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757690).length < 2 ^ (prefixWord ++ tailWord_757690).sum := by decide
  have hdescent : baseEnd_757690 < baseStart_757690 := by decide
  rcases family_descends (prefixWord ++ tailWord_757690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757797 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 6]
def baseStart_757797 : Nat := 118140960795 + 757797 * 2 ^ 59
def prefixEnd_757797 : Nat := 4983230072969 + 3 ^ 40 * 757797 * 2
def baseEnd_757797 : Nat := 172939599793456377534427

theorem tailTrace_757797 : CollatzResearch.WordTrace tailWord_757797 prefixEnd_757797 172939599793456377534427 := by
  unfold tailWord_757797
  simp only [CollatzResearch.WordTrace]
  refine ⟨27639127235638365268943645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18426084823758910179295763 27639127235638365268943645)
  ·
    refine ⟨10364672713364386975853867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27639127235638365268943645 10364672713364386975853867)
    ·
      refine ⟨15547009070046580463780801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10364672713364386975853867 15547009070046580463780801)
      ·
        refine ⟨11660256802534935347835601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15547009070046580463780801 11660256802534935347835601)
        ·
          refine ⟨8745192601901201510876701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11660256802534935347835601 8745192601901201510876701)
          ·
            refine ⟨3279447225712950566578763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8745192601901201510876701 3279447225712950566578763)
            ·
              refine ⟨4919170838569425849868145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3279447225712950566578763 4919170838569425849868145)
              ·
                refine ⟨3689378128927069387401109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4919170838569425849868145 3689378128927069387401109)
                ·
                  refine ⟨172939599793456377534427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3689378128927069387401109 172939599793456377534427)
                  ·
                    rfl

theorem cell21_757797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_757797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757797 prefixEnd_757797 := by exact prefixLift 757797
  have htrace : WordTrace (prefixWord ++ tailWord_757797) baseStart_757797 baseEnd_757797 := by
    simpa [prefixWord, tailWord_757797, baseEnd_757797] using wordTrace_append hprefix tailTrace_757797
  have hstable : (prefixWord ++ tailWord_757797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757797).length < 2 ^ (prefixWord ++ tailWord_757797).sum := by decide
  have hdescent : baseEnd_757797 < baseStart_757797 := by decide
  rcases family_descends (prefixWord ++ tailWord_757797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757811 : List Nat := [1, 1, 1, 2, 4, 1, 11]
def baseStart_757811 : Nat := 118140960795 + 757811 * 2 ^ 59
def prefixEnd_757811 : Nat := 4983230072969 + 3 ^ 40 * 757811 * 2
def baseEnd_757811 : Nat := 19215866087132829366785

theorem tailTrace_757811 : CollatzResearch.WordTrace tailWord_757811 prefixEnd_757811 19215866087132829366785 := by
  unfold tailWord_757811
  simp only [CollatzResearch.WordTrace]
  refine ⟨27639637857587645659953287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18426425238391763773302191 27639637857587645659953287)
  ·
    refine ⟨41459456786381468489929931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27639637857587645659953287 41459456786381468489929931)
    ·
      refine ⟨62189185179572202734894897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41459456786381468489929931 62189185179572202734894897)
      ·
        refine ⟨46641888884679152051171173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62189185179572202734894897 46641888884679152051171173)
        ·
          refine ⟨8745354165877341009594595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46641888884679152051171173 8745354165877341009594595)
          ·
            refine ⟨13118031248816011514391893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8745354165877341009594595 13118031248816011514391893)
            ·
              refine ⟨19215866087132829366785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13118031248816011514391893 19215866087132829366785)
              ·
                rfl

theorem cell21_757811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 11].length) (baseStart_757811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757811 prefixEnd_757811 := by exact prefixLift 757811
  have htrace : WordTrace (prefixWord ++ tailWord_757811) baseStart_757811 baseEnd_757811 := by
    simpa [prefixWord, tailWord_757811, baseEnd_757811] using wordTrace_append hprefix tailTrace_757811
  have hstable : (prefixWord ++ tailWord_757811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757811).length < 2 ^ (prefixWord ++ tailWord_757811).sum := by decide
  have hdescent : baseEnd_757811 < baseStart_757811 := by decide
  rcases family_descends (prefixWord ++ tailWord_757811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757814 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_757814 : Nat := 118140960795 + 757814 * 2 ^ 59
def prefixEnd_757814 : Nat := 4983230072969 + 3 ^ 40 * 757814 * 2
def baseEnd_757814 : Nat := 172943479425068125751059

theorem tailTrace_757814 : CollatzResearch.WordTrace tailWord_757814 prefixEnd_757814 172943479425068125751059 := by
  unfold tailWord_757814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1727484204786048573269531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18426498184384518114874997 1727484204786048573269531)
  ·
    refine ⟨2591226307179072859904297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1727484204786048573269531 2591226307179072859904297)
    ·
      refine ⟨1943419730384304644928223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2591226307179072859904297 1943419730384304644928223)
      ·
        refine ⟨2915129595576456967392335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943419730384304644928223 2915129595576456967392335)
        ·
          refine ⟨4372694393364685451088503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2915129595576456967392335 4372694393364685451088503)
          ·
            refine ⟨6559041590047028176632755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4372694393364685451088503 6559041590047028176632755)
            ·
              refine ⟨9838562385070542264949133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6559041590047028176632755 9838562385070542264949133)
              ·
                refine ⟨3689460894401453349355925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9838562385070542264949133 3689460894401453349355925)
                ·
                  refine ⟨172943479425068125751059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3689460894401453349355925 172943479425068125751059)
                  ·
                    rfl

theorem cell21_757814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_757814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757814 prefixEnd_757814 := by exact prefixLift 757814
  have htrace : WordTrace (prefixWord ++ tailWord_757814) baseStart_757814 baseEnd_757814 := by
    simpa [prefixWord, tailWord_757814, baseEnd_757814] using wordTrace_append hprefix tailTrace_757814
  have hstable : (prefixWord ++ tailWord_757814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757814).length < 2 ^ (prefixWord ++ tailWord_757814).sum := by decide
  have hdescent : baseEnd_757814 < baseStart_757814 := by decide
  rcases family_descends (prefixWord ++ tailWord_757814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757817 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 5]
def baseStart_757817 : Nat := 118140960795 + 757817 * 2 ^ 59
def prefixEnd_757817 : Nat := 4983230072969 + 3 ^ 40 * 757817 * 2
def baseEnd_757817 : Nat := 172944164065940787201053

theorem tailTrace_757817 : CollatzResearch.WordTrace tailWord_757817 prefixEnd_757817 172944164065940787201053 := by
  unfold tailWord_757817
  simp only [CollatzResearch.WordTrace]
  refine ⟨27639856695565908684671705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18426571130377272456447803 27639856695565908684671705)
  ·
    refine ⟨20729892521674431513503779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27639856695565908684671705 20729892521674431513503779)
    ·
      refine ⟨31094838782511647270255669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20729892521674431513503779 31094838782511647270255669)
      ·
        refine ⟨2915141135860466931586469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31094838782511647270255669 2915141135860466931586469)
        ·
          refine ⟨546588962973837549672463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2915141135860466931586469 546588962973837549672463)
          ·
            refine ⟨819883444460756324508695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546588962973837549672463 819883444460756324508695)
            ·
              refine ⟨1229825166691134486763043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819883444460756324508695 1229825166691134486763043)
              ·
                refine ⟨1844737750036701730144565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229825166691134486763043 1844737750036701730144565)
                ·
                  refine ⟨172944164065940787201053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1844737750036701730144565 172944164065940787201053)
                  ·
                    rfl

theorem cell21_757817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 5].length) (baseStart_757817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757817 prefixEnd_757817 := by exact prefixLift 757817
  have htrace : WordTrace (prefixWord ++ tailWord_757817) baseStart_757817 baseEnd_757817 := by
    simpa [prefixWord, tailWord_757817, baseEnd_757817] using wordTrace_append hprefix tailTrace_757817
  have hstable : (prefixWord ++ tailWord_757817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757817).length < 2 ^ (prefixWord ++ tailWord_757817).sum := by decide
  have hdescent : baseEnd_757817 < baseStart_757817 := by decide
  rcases family_descends (prefixWord ++ tailWord_757817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757904 : List Nat := [2, 1, 1, 1, 1, 1, 9, 5]
def baseStart_757904 : Nat := 118140960795 + 757904 * 2 ^ 59
def prefixEnd_757904 : Nat := 4983230072969 + 3 ^ 40 * 757904 * 2
def baseEnd_757904 : Nat := 57654672883749323083625

theorem tailTrace_757904 : CollatzResearch.WordTrace tailWord_757904 prefixEnd_757904 57654672883749323083625 := by
  unfold tailWord_757904
  simp only [CollatzResearch.WordTrace]
  refine ⟨13821514923125361271544383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18428686564167148362059177 13821514923125361271544383)
  ·
    refine ⟨20732272384688041907316575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13821514923125361271544383 20732272384688041907316575)
    ·
      refine ⟨31098408577032062860974863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20732272384688041907316575 31098408577032062860974863)
      ·
        refine ⟨46647612865548094291462295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31098408577032062860974863 46647612865548094291462295)
        ·
          refine ⟨69971419298322141437193443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46647612865548094291462295 69971419298322141437193443)
          ·
            refine ⟨104957128947483212155790165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69971419298322141437193443 104957128947483212155790165)
            ·
              refine ⟨614983177426659446225333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 104957128947483212155790165 614983177426659446225333)
              ·
                refine ⟨57654672883749323083625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 614983177426659446225333 57654672883749323083625)
                ·
                  rfl

theorem cell21_757904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 5].length) (baseStart_757904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757904 prefixEnd_757904 := by exact prefixLift 757904
  have htrace : WordTrace (prefixWord ++ tailWord_757904) baseStart_757904 baseEnd_757904 := by
    simpa [prefixWord, tailWord_757904, baseEnd_757904] using wordTrace_append hprefix tailTrace_757904
  have hstable : (prefixWord ++ tailWord_757904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757904).length < 2 ^ (prefixWord ++ tailWord_757904).sum := by decide
  have hdescent : baseEnd_757904 < baseStart_757904 := by decide
  rcases family_descends (prefixWord ++ tailWord_757904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757924 : List Nat := [2, 3, 1, 2, 5, 1, 1, 2, 4]
def baseStart_757924 : Nat := 118140960795 + 757924 * 2 ^ 59
def prefixEnd_757924 : Nat := 4983230072969 + 3 ^ 40 * 757924 * 2
def baseEnd_757924 : Nat := 172968582923732378917501

theorem tailTrace_757924 : CollatzResearch.WordTrace tailWord_757924 prefixEnd_757924 172968582923732378917501 := by
  unfold tailWord_757924
  simp only [CollatzResearch.WordTrace]
  refine ⟨13821879653089132979408413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18429172870785510639211217 13821879653089132979408413)
  ·
    refine ⟨5183204869908424867278155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13821879653089132979408413 5183204869908424867278155)
    ·
      refine ⟨7774807304862637300917233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5183204869908424867278155 7774807304862637300917233)
      ·
        refine ⟨5831105478646977975687925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7774807304862637300917233 5831105478646977975687925)
        ·
          refine ⟨546666138623154185220743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5831105478646977975687925 546666138623154185220743)
          ·
            refine ⟨819999207934731277831115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546666138623154185220743 819999207934731277831115)
            ·
              refine ⟨1229998811902096916746673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819999207934731277831115 1229998811902096916746673)
              ·
                refine ⟨922499108926572687560005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1229998811902096916746673 922499108926572687560005)
                ·
                  refine ⟨172968582923732378917501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 922499108926572687560005 172968582923732378917501)
                  ·
                    rfl

theorem cell21_757924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_757924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757924 prefixEnd_757924 := by exact prefixLift 757924
  have htrace : WordTrace (prefixWord ++ tailWord_757924) baseStart_757924 baseEnd_757924 := by
    simpa [prefixWord, tailWord_757924, baseEnd_757924] using wordTrace_append hprefix tailTrace_757924
  have hstable : (prefixWord ++ tailWord_757924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757924).length < 2 ^ (prefixWord ++ tailWord_757924).sum := by decide
  have hdescent : baseEnd_757924 < baseStart_757924 := by decide
  rcases family_descends (prefixWord ++ tailWord_757924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757963 : List Nat := [1, 1, 1, 1, 3, 2, 5, 7]
def baseStart_757963 : Nat := 118140960795 + 757963 * 2 ^ 59
def prefixEnd_757963 : Nat := 4983230072969 + 3 ^ 40 * 757963 * 2
def baseEnd_757963 : Nat := 57659161085025659255807

theorem tailTrace_757963 : CollatzResearch.WordTrace tailWord_757963 prefixEnd_757963 57659161085025659255807 := by
  unfold tailWord_757963
  simp only [CollatzResearch.WordTrace]
  refine ⟨27645181753036975619486543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18430121168691317079657695 27645181753036975619486543)
  ·
    refine ⟨41467772629555463429229815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27645181753036975619486543 41467772629555463429229815)
    ·
      refine ⟨62201658944333195143844723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41467772629555463429229815 62201658944333195143844723)
      ·
        refine ⟨93302488416499792715767085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62201658944333195143844723 93302488416499792715767085)
        ·
          refine ⟨34988433156187422268412657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93302488416499792715767085 34988433156187422268412657)
          ·
            refine ⟨26241324867140566701309493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34988433156187422268412657 26241324867140566701309493)
            ·
              refine ⟨2460124206294428128247765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26241324867140566701309493 2460124206294428128247765)
              ·
                refine ⟨57659161085025659255807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2460124206294428128247765 57659161085025659255807)
                ·
                  rfl

theorem cell21_757963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 7].length) (baseStart_757963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757963 prefixEnd_757963 := by exact prefixLift 757963
  have htrace : WordTrace (prefixWord ++ tailWord_757963) baseStart_757963 baseEnd_757963 := by
    simpa [prefixWord, tailWord_757963, baseEnd_757963] using wordTrace_append hprefix tailTrace_757963
  have hstable : (prefixWord ++ tailWord_757963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757963).length < 2 ^ (prefixWord ++ tailWord_757963).sum := by decide
  have hdescent : baseEnd_757963 < baseStart_757963 := by decide
  rcases family_descends (prefixWord ++ tailWord_757963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757997 : List Nat := [1, 5, 1, 2, 3, 1, 2, 6]
def baseStart_757997 : Nat := 118140960795 + 757997 * 2 ^ 59
def prefixEnd_757997 : Nat := 4983230072969 + 3 ^ 40 * 757997 * 2
def baseEnd_757997 : Nat := 57661747506100158066895

theorem tailTrace_757997 : CollatzResearch.WordTrace tailWord_757997 prefixEnd_757997 57661747506100158066895 := by
  unfold tailWord_757997
  simp only [CollatzResearch.WordTrace]
  refine ⟨27646421834913799426224245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18430947889942532950816163 27646421834913799426224245)
  ·
    refine ⟨2591852047023168696208523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27646421834913799426224245 2591852047023168696208523)
    ·
      refine ⟨3887778070534753044312785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2591852047023168696208523 3887778070534753044312785)
      ·
        refine ⟨2915833552901064783234589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3887778070534753044312785 2915833552901064783234589)
        ·
          refine ⟨1093437582337899293712971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2915833552901064783234589 1093437582337899293712971)
          ·
            refine ⟨1640156373506848940569457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093437582337899293712971 1640156373506848940569457)
            ·
              refine ⟨1230117280130136705427093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1640156373506848940569457 1230117280130136705427093)
              ·
                refine ⟨57661747506100158066895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1230117280130136705427093 57661747506100158066895)
                ·
                  rfl

theorem cell21_757997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 6].length) (baseStart_757997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_757997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_757997 prefixEnd_757997 := by exact prefixLift 757997
  have htrace : WordTrace (prefixWord ++ tailWord_757997) baseStart_757997 baseEnd_757997 := by
    simpa [prefixWord, tailWord_757997, baseEnd_757997] using wordTrace_append hprefix tailTrace_757997
  have hstable : (prefixWord ++ tailWord_757997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757997).length < 2 ^ (prefixWord ++ tailWord_757997).sum := by decide
  have hdescent : baseEnd_757997 < baseStart_757997 := by decide
  rcases family_descends (prefixWord ++ tailWord_757997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758039 : List Nat := [1, 1, 3, 4, 1, 11]
def baseStart_758039 : Nat := 118140960795 + 758039 * 2 ^ 59
def prefixEnd_758039 : Nat := 4983230072969 + 3 ^ 40 * 758039 * 2
def baseEnd_758039 : Nat := 6407215832982138314837

theorem tailTrace_758039 : CollatzResearch.WordTrace tailWord_758039 prefixEnd_758039 6407215832982138314837 := by
  unfold tailWord_758039
  simp only [CollatzResearch.WordTrace]
  refine ⟨27647953700761640599253171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18431969133841093732835447 27647953700761640599253171)
  ·
    refine ⟨41471930551142460898879757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27647953700761640599253171 41471930551142460898879757)
    ·
      refine ⟨15551973956678422837079909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41471930551142460898879757 15551973956678422837079909)
      ·
        refine ⟨2915995116877204281952483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15551973956678422837079909 2915995116877204281952483)
        ·
          refine ⟨4373992675315806422928725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2915995116877204281952483 4373992675315806422928725)
          ·
            refine ⟨6407215832982138314837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4373992675315806422928725 6407215832982138314837)
            ·
              rfl

theorem cell21_758039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 11].length) (baseStart_758039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758039 prefixEnd_758039 := by exact prefixLift 758039
  have htrace : WordTrace (prefixWord ++ tailWord_758039) baseStart_758039 baseEnd_758039 := by
    simpa [prefixWord, tailWord_758039, baseEnd_758039] using wordTrace_append hprefix tailTrace_758039
  have hstable : (prefixWord ++ tailWord_758039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758039).length < 2 ^ (prefixWord ++ tailWord_758039).sum := by decide
  have hdescent : baseEnd_758039 < baseStart_758039 := by decide
  rcases family_descends (prefixWord ++ tailWord_758039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758045 : List Nat := [1, 4, 2, 3, 2, 1, 1, 4, 3]
def baseStart_758045 : Nat := 118140960795 + 758045 * 2 ^ 59
def prefixEnd_758045 : Nat := 4983230072969 + 3 ^ 40 * 758045 * 2
def baseEnd_758045 : Nat := 172996196772263057400587

theorem tailTrace_758045 : CollatzResearch.WordTrace tailWord_758045 prefixEnd_758045 172996196772263057400587 := by
  unfold tailWord_758045
  simp only [CollatzResearch.WordTrace]
  refine ⟨27648172538739903623971589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18432115025826602415981059 27648172538739903623971589)
  ·
    refine ⟨5184032351013731929494673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27648172538739903623971589 5184032351013731929494673)
    ·
      refine ⟨3888024263260298947121005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5184032351013731929494673 3888024263260298947121005)
      ·
        refine ⟨1458009098722612105170377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3888024263260298947121005 1458009098722612105170377)
        ·
          refine ⟨1093506824041959078877783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1458009098722612105170377 1093506824041959078877783)
          ·
            refine ⟨1640260236062938618316675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093506824041959078877783 1640260236062938618316675)
            ·
              refine ⟨2460390354094407927475013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640260236062938618316675 2460390354094407927475013)
              ·
                refine ⟨461323191392701486401565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2460390354094407927475013 461323191392701486401565)
                ·
                  refine ⟨172996196772263057400587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461323191392701486401565 172996196772263057400587)
                  ·
                    rfl

theorem cell21_758045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_758045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758045 prefixEnd_758045 := by exact prefixLift 758045
  have htrace : WordTrace (prefixWord ++ tailWord_758045) baseStart_758045 baseEnd_758045 := by
    simpa [prefixWord, tailWord_758045, baseEnd_758045] using wordTrace_append hprefix tailTrace_758045
  have hstable : (prefixWord ++ tailWord_758045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758045).length < 2 ^ (prefixWord ++ tailWord_758045).sum := by decide
  have hdescent : baseEnd_758045 < baseStart_758045 := by decide
  rcases family_descends (prefixWord ++ tailWord_758045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758073 : List Nat := [1, 2, 1, 6, 1, 2, 3, 5]
def baseStart_758073 : Nat := 118140960795 + 758073 * 2 ^ 59
def prefixEnd_758073 : Nat := 4983230072969 + 3 ^ 40 * 758073 * 2
def baseEnd_758073 : Nat := 57667528917913743644621

theorem tailTrace_758073 : CollatzResearch.WordTrace tailWord_758073 prefixEnd_758073 57667528917913743644621 := by
  unfold tailWord_758073
  simp only [CollatzResearch.WordTrace]
  refine ⟨27649193782638464405990873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18432795855092309603993915 27649193782638464405990873)
  ·
    refine ⟨20736895336978848304493155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27649193782638464405990873 20736895336978848304493155)
    ·
      refine ⟨31105343005468272456739733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20736895336978848304493155 31105343005468272456739733)
      ·
        refine ⟨1458062953381325271409675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31105343005468272456739733 1458062953381325271409675)
        ·
          refine ⟨2187094430071987907114513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1458062953381325271409675 2187094430071987907114513)
          ·
            refine ⟨1640320822553990930335885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2187094430071987907114513 1640320822553990930335885)
            ·
              refine ⟨615120308457746598875957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1640320822553990930335885 615120308457746598875957)
              ·
                refine ⟨57667528917913743644621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 615120308457746598875957 57667528917913743644621)
                ·
                  rfl

theorem cell21_758073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 5].length) (baseStart_758073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758073 prefixEnd_758073 := by exact prefixLift 758073
  have htrace : WordTrace (prefixWord ++ tailWord_758073) baseStart_758073 baseEnd_758073 := by
    simpa [prefixWord, tailWord_758073, baseEnd_758073] using wordTrace_append hprefix tailTrace_758073
  have hstable : (prefixWord ++ tailWord_758073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758073).length < 2 ^ (prefixWord ++ tailWord_758073).sum := by decide
  have hdescent : baseEnd_758073 < baseStart_758073 := by decide
  rcases family_descends (prefixWord ++ tailWord_758073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758115 : List Nat := [1, 1, 1, 5, 2, 1, 2, 8]
def baseStart_758115 : Nat := 118140960795 + 758115 * 2 ^ 59
def prefixEnd_758115 : Nat := 4983230072969 + 3 ^ 40 * 758115 * 2
def baseEnd_758115 : Nat := 57670723908652830411259

theorem tailTrace_758115 : CollatzResearch.WordTrace tailWord_758115 prefixEnd_758115 57670723908652830411259 := by
  unfold tailWord_758115
  simp only [CollatzResearch.WordTrace]
  refine ⟨27650725648486305579019799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18433817098990870386013199 27650725648486305579019799)
  ·
    refine ⟨41476088472729458368529699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27650725648486305579019799 41476088472729458368529699)
    ·
      refine ⟨62214132709094187552794549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41476088472729458368529699 62214132709094187552794549)
      ·
        refine ⟨5832574941477580083074489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62214132709094187552794549 5832574941477580083074489)
        ·
          refine ⟨4374431206108185062305867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5832574941477580083074489 4374431206108185062305867)
          ·
            refine ⟨6561646809162277593458801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4374431206108185062305867 6561646809162277593458801)
            ·
              refine ⟨4921235106871708195094101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6561646809162277593458801 4921235106871708195094101)
              ·
                refine ⟨57670723908652830411259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4921235106871708195094101 57670723908652830411259)
                ·
                  rfl

theorem cell21_758115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 8].length) (baseStart_758115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758115 prefixEnd_758115 := by exact prefixLift 758115
  have htrace : WordTrace (prefixWord ++ tailWord_758115) baseStart_758115 baseEnd_758115 := by
    simpa [prefixWord, tailWord_758115, baseEnd_758115] using wordTrace_append hprefix tailTrace_758115
  have hstable : (prefixWord ++ tailWord_758115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758115).length < 2 ^ (prefixWord ++ tailWord_758115).sum := by decide
  have hdescent : baseEnd_758115 < baseStart_758115 := by decide
  rcases family_descends (prefixWord ++ tailWord_758115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758222 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_758222 : Nat := 118140960795 + 758222 * 2 ^ 59
def prefixEnd_758222 : Nat := 4983230072969 + 3 ^ 40 * 758222 * 2
def baseEnd_758222 : Nat := 173036590583750082950225

theorem tailTrace_758222 : CollatzResearch.WordTrace tailWord_758222 prefixEnd_758222 173036590583750082950225 := by
  unfold tailWord_758222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3456828532387332856645615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18436418839399108568776613 3456828532387332856645615)
  ·
    refine ⟨5185242798580999284968423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3456828532387332856645615 5185242798580999284968423)
    ·
      refine ⟨7777864197871498927452635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5185242798580999284968423 7777864197871498927452635)
      ·
        refine ⟨11666796296807248391178953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7777864197871498927452635 11666796296807248391178953)
        ·
          refine ⟨8750097222605436293384215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11666796296807248391178953 8750097222605436293384215)
          ·
            refine ⟨13125145833908154440076323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8750097222605436293384215 13125145833908154440076323)
            ·
              refine ⟨19687718750862231660114485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13125145833908154440076323 19687718750862231660114485)
              ·
                refine ⟨1845723632893334218135733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19687718750862231660114485 1845723632893334218135733)
                ·
                  refine ⟨173036590583750082950225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1845723632893334218135733 173036590583750082950225)
                  ·
                    rfl

theorem cell21_758222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_758222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758222 prefixEnd_758222 := by exact prefixLift 758222
  have htrace : WordTrace (prefixWord ++ tailWord_758222) baseStart_758222 baseEnd_758222 := by
    simpa [prefixWord, tailWord_758222, baseEnd_758222] using wordTrace_append hprefix tailTrace_758222
  have hstable : (prefixWord ++ tailWord_758222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758222).length < 2 ^ (prefixWord ++ tailWord_758222).sum := by decide
  have hdescent : baseEnd_758222 < baseStart_758222 := by decide
  rcases family_descends (prefixWord ++ tailWord_758222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758298 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_758298 : Nat := 118140960795 + 758298 * 2 ^ 59
def prefixEnd_758298 : Nat := 4983230072969 + 3 ^ 40 * 758298 * 2
def baseEnd_758298 : Nat := 173053934819190839683403

theorem tailTrace_758298 : CollatzResearch.WordTrace tailWord_758298 prefixEnd_758298 173053934819190839683403 := by
  unfold tailWord_758298
  simp only [CollatzResearch.WordTrace]
  refine ⟨6914350051705831958232887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18438266804548885221954365 6914350051705831958232887)
  ·
    refine ⟨10371525077558747937349331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6914350051705831958232887 10371525077558747937349331)
    ·
      refine ⟨15557287616338121906023997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10371525077558747937349331 15557287616338121906023997)
      ·
        refine ⟨5833982856126795714758999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15557287616338121906023997 5833982856126795714758999)
        ·
          refine ⟨8750974284190193572138499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5833982856126795714758999 8750974284190193572138499)
          ·
            refine ⟨13126461426285290358207749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8750974284190193572138499 13126461426285290358207749)
            ·
              refine ⟨2461211517428491942163953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13126461426285290358207749 2461211517428491942163953)
              ·
                refine ⟨1845908638071368956622965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2461211517428491942163953 1845908638071368956622965)
                ·
                  refine ⟨173053934819190839683403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1845908638071368956622965 173053934819190839683403)
                  ·
                    rfl

theorem cell21_758298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_758298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758298 prefixEnd_758298 := by exact prefixLift 758298
  have htrace : WordTrace (prefixWord ++ tailWord_758298) baseStart_758298 baseEnd_758298 := by
    simpa [prefixWord, tailWord_758298, baseEnd_758298] using wordTrace_append hprefix tailTrace_758298
  have hstable : (prefixWord ++ tailWord_758298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758298).length < 2 ^ (prefixWord ++ tailWord_758298).sum := by decide
  have hdescent : baseEnd_758298 < baseStart_758298 := by decide
  rcases family_descends (prefixWord ++ tailWord_758298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758301 : List Nat := [1, 4, 2, 2, 1, 4, 2, 5]
def baseStart_758301 : Nat := 118140960795 + 758301 * 2 ^ 59
def prefixEnd_758301 : Nat := 4983230072969 + 3 ^ 40 * 758301 * 2
def baseEnd_758301 : Nat := 57684873153354500377799

theorem tailTrace_758301 : CollatzResearch.WordTrace tailWord_758301 prefixEnd_758301 57684873153354500377799 := by
  unfold tailWord_758301
  simp only [CollatzResearch.WordTrace]
  refine ⟨27657509625812459345290757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18438339750541639563527171 27657509625812459345290757)
  ·
    refine ⟨5185783054839836127242017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27657509625812459345290757 5185783054839836127242017)
    ·
      refine ⟨3889337291129877095431513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5185783054839836127242017 3889337291129877095431513)
      ·
        refine ⟨2917002968347407821573635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3889337291129877095431513 2917002968347407821573635)
        ·
          refine ⟨4375504452521111732360453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917002968347407821573635 4375504452521111732360453)
          ·
            refine ⟨820407084847708449817585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4375504452521111732360453 820407084847708449817585)
            ·
              refine ⟨615305313635781337363189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820407084847708449817585 615305313635781337363189)
              ·
                refine ⟨57684873153354500377799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 615305313635781337363189 57684873153354500377799)
                ·
                  rfl

theorem cell21_758301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 5].length) (baseStart_758301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758301 prefixEnd_758301 := by exact prefixLift 758301
  have htrace : WordTrace (prefixWord ++ tailWord_758301) baseStart_758301 baseEnd_758301 := by
    simpa [prefixWord, tailWord_758301, baseEnd_758301] using wordTrace_append hprefix tailTrace_758301
  have hstable : (prefixWord ++ tailWord_758301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758301).length < 2 ^ (prefixWord ++ tailWord_758301).sum := by decide
  have hdescent : baseEnd_758301 < baseStart_758301 := by decide
  rcases family_descends (prefixWord ++ tailWord_758301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758329 : List Nat := [1, 2, 1, 5, 1, 1, 2, 4, 4]
def baseStart_758329 : Nat := 118140960795 + 758329 * 2 ^ 59
def prefixEnd_758329 : Nat := 4983230072969 + 3 ^ 40 * 758329 * 2
def baseEnd_758329 : Nat := 173061009441541674666673

theorem tailTrace_758329 : CollatzResearch.WordTrace tailWord_758329 prefixEnd_758329 173061009441541674666673 := by
  unfold tailWord_758329
  simp only [CollatzResearch.WordTrace]
  refine ⟨27658530869711020127310041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18439020579807346751540027 27658530869711020127310041)
  ·
    refine ⟨20743898152283265095482531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27658530869711020127310041 20743898152283265095482531)
    ·
      refine ⟨31115847228424897643223797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20743898152283265095482531 31115847228424897643223797)
      ·
        refine ⟨2917110677664834154052231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31115847228424897643223797 2917110677664834154052231)
        ·
          refine ⟨4375666016497251231078347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917110677664834154052231 4375666016497251231078347)
          ·
            refine ⟨6563499024745876846617521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375666016497251231078347 6563499024745876846617521)
            ·
              refine ⟨4922624268559407634963141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6563499024745876846617521 4922624268559407634963141)
              ·
                refine ⟨922992050354888931555589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4922624268559407634963141 922992050354888931555589)
                ·
                  refine ⟨173061009441541674666673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 922992050354888931555589 173061009441541674666673)
                  ·
                    rfl

theorem cell21_758329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_758329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758329 prefixEnd_758329 := by exact prefixLift 758329
  have htrace : WordTrace (prefixWord ++ tailWord_758329) baseStart_758329 baseEnd_758329 := by
    simpa [prefixWord, tailWord_758329, baseEnd_758329] using wordTrace_append hprefix tailTrace_758329
  have hstable : (prefixWord ++ tailWord_758329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758329).length < 2 ^ (prefixWord ++ tailWord_758329).sum := by decide
  have hdescent : baseEnd_758329 < baseStart_758329 := by decide
  rcases family_descends (prefixWord ++ tailWord_758329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758343 : List Nat := [1, 1, 4, 1, 4, 1, 1, 8]
def baseStart_758343 : Nat := 118140960795 + 758343 * 2 ^ 59
def prefixEnd_758343 : Nat := 4983230072969 + 3 ^ 40 * 758343 * 2
def baseEnd_758343 : Nat := 57688068144093587144437

theorem tailTrace_758343 : CollatzResearch.WordTrace tailWord_758343 prefixEnd_758343 57688068144093587144437 := by
  unfold tailWord_758343
  simp only [CollatzResearch.WordTrace]
  refine ⟨27659041491660300518319683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18439360994440200345546455 27659041491660300518319683)
  ·
    refine ⟨41488562237490450777479525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27659041491660300518319683 41488562237490450777479525)
    ·
      refine ⟨7779105419529459520777411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41488562237490450777479525 7779105419529459520777411)
      ·
        refine ⟨11668658129294189281166117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7779105419529459520777411 11668658129294189281166117)
        ·
          refine ⟨2187873399242660490218647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11668658129294189281166117 2187873399242660490218647)
          ·
            refine ⟨3281810098863990735327971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187873399242660490218647 3281810098863990735327971)
            ·
              refine ⟨4922715148295986102991957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3281810098863990735327971 4922715148295986102991957)
              ·
                refine ⟨57688068144093587144437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4922715148295986102991957 57688068144093587144437)
                ·
                  rfl

theorem cell21_758343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 8].length) (baseStart_758343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758343 prefixEnd_758343 := by exact prefixLift 758343
  have htrace : WordTrace (prefixWord ++ tailWord_758343) baseStart_758343 baseEnd_758343 := by
    simpa [prefixWord, tailWord_758343, baseEnd_758343] using wordTrace_append hprefix tailTrace_758343
  have hstable : (prefixWord ++ tailWord_758343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758343).length < 2 ^ (prefixWord ++ tailWord_758343).sum := by decide
  have hdescent : baseEnd_758343 < baseStart_758343 := by decide
  rcases family_descends (prefixWord ++ tailWord_758343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758346 : List Nat := [3, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_758346 : Nat := 118140960795 + 758346 * 2 ^ 59
def prefixEnd_758346 : Nat := 4983230072969 + 3 ^ 40 * 758346 * 2
def baseEnd_758346 : Nat := 173064889073153422883305

theorem tailTrace_758346 : CollatzResearch.WordTrace tailWord_758346 prefixEnd_758346 173064889073153422883305 := by
  unfold tailWord_758346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6914787727662358007669723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18439433940432954687119261 6914787727662358007669723)
  ·
    refine ⟨10372181591493537011504585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6914787727662358007669723 10372181591493537011504585)
    ·
      refine ⟨7779136193620152758628439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10372181591493537011504585 7779136193620152758628439)
      ·
        refine ⟨11668704290430229137942659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7779136193620152758628439 11668704290430229137942659)
        ·
          refine ⟨17503056435645343706913989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11668704290430229137942659 17503056435645343706913989)
          ·
            refine ⟨3281823081683501945046373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17503056435645343706913989 3281823081683501945046373)
            ·
              refine ⟨615341827815656614696195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3281823081683501945046373 615341827815656614696195)
              ·
                refine ⟨923012741723484922044293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615341827815656614696195 923012741723484922044293)
                ·
                  refine ⟨173064889073153422883305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 923012741723484922044293 173064889073153422883305)
                  ·
                    rfl

theorem cell21_758346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_758346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758346 prefixEnd_758346 := by exact prefixLift 758346
  have htrace : WordTrace (prefixWord ++ tailWord_758346) baseStart_758346 baseEnd_758346 := by
    simpa [prefixWord, tailWord_758346, baseEnd_758346] using wordTrace_append hprefix tailTrace_758346
  have hstable : (prefixWord ++ tailWord_758346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758346).length < 2 ^ (prefixWord ++ tailWord_758346).sum := by decide
  have hdescent : baseEnd_758346 < baseStart_758346 := by decide
  rcases family_descends (prefixWord ++ tailWord_758346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758405 : List Nat := [1, 3, 1, 1, 4, 2, 2, 3, 4]
def baseStart_758405 : Nat := 118140960795 + 758405 * 2 ^ 59
def prefixEnd_758405 : Nat := 4983230072969 + 3 ^ 40 * 758405 * 2
def baseEnd_758405 : Nat := 173078353676982431399851

theorem tailTrace_758405 : CollatzResearch.WordTrace tailWord_758405 prefixEnd_758405 173078353676982431399851 := by
  unfold tailWord_758405
  simp only [CollatzResearch.WordTrace]
  refine ⟨27661302817435685107076669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18440868544957123404717779 27661302817435685107076669)
  ·
    refine ⟨10372988556538381915153751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27661302817435685107076669 10372988556538381915153751)
    ·
      refine ⟨15559482834807572872730627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10372988556538381915153751 15559482834807572872730627)
      ·
        refine ⟨23339224252211359309095941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15559482834807572872730627 23339224252211359309095941)
        ·
          refine ⟨4376104547289629870455489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23339224252211359309095941 4376104547289629870455489)
          ·
            refine ⟨3282078410467222402841617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4376104547289629870455489 3282078410467222402841617)
            ·
              refine ⟨2461558807850416802131213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3282078410467222402841617 2461558807850416802131213)
              ·
                refine ⟨923084552943906300799205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2461558807850416802131213 923084552943906300799205)
                ·
                  refine ⟨173078353676982431399851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 923084552943906300799205 173078353676982431399851)
                  ·
                    rfl

theorem cell21_758405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_758405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758405 prefixEnd_758405 := by exact prefixLift 758405
  have htrace : WordTrace (prefixWord ++ tailWord_758405) baseStart_758405 baseEnd_758405 := by
    simpa [prefixWord, tailWord_758405, baseEnd_758405] using wordTrace_append hprefix tailTrace_758405
  have hstable : (prefixWord ++ tailWord_758405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758405).length < 2 ^ (prefixWord ++ tailWord_758405).sum := by decide
  have hdescent : baseEnd_758405 < baseStart_758405 := by decide
  rcases family_descends (prefixWord ++ tailWord_758405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758470 : List Nat := [6, 1, 2, 1, 2, 1, 1, 7]
def baseStart_758470 : Nat := 118140960795 + 758470 * 2 ^ 59
def prefixEnd_758470 : Nat := 4983230072969 + 3 ^ 40 * 758470 * 2
def baseEnd_758470 : Nat := 57697729187518920938795

theorem tailTrace_758470 : CollatzResearch.WordTrace tailWord_758470 prefixEnd_758470 57697729187518920938795 := by
  unfold tailWord_758470
  simp only [CollatzResearch.WordTrace]
  refine ⟨864489798818756287756027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18442449041466800805461909 864489798818756287756027)
  ·
    refine ⟨1296734698228134431634041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 864489798818756287756027 1296734698228134431634041)
    ·
      refine ⟨972551023671100823725531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1296734698228134431634041 972551023671100823725531)
      ·
        refine ⟨1458826535506651235588297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 972551023671100823725531 1458826535506651235588297)
        ·
          refine ⟨1094119901629988426691223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1458826535506651235588297 1094119901629988426691223)
          ·
            refine ⟨1641179852444982640036835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094119901629988426691223 1641179852444982640036835)
            ·
              refine ⟨2461769778667473960055253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641179852444982640036835 2461769778667473960055253)
              ·
                refine ⟨57697729187518920938795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2461769778667473960055253 57697729187518920938795)
                ·
                  rfl

theorem cell21_758470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_758470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758470 prefixEnd_758470 := by exact prefixLift 758470
  have htrace : WordTrace (prefixWord ++ tailWord_758470) baseStart_758470 baseEnd_758470 := by
    simpa [prefixWord, tailWord_758470, baseEnd_758470] using wordTrace_append hprefix tailTrace_758470
  have hstable : (prefixWord ++ tailWord_758470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758470).length < 2 ^ (prefixWord ++ tailWord_758470).sum := by decide
  have hdescent : baseEnd_758470 < baseStart_758470 := by decide
  rcases family_descends (prefixWord ++ tailWord_758470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758495 : List Nat := [1, 1, 2, 3, 2, 5, 7]
def baseStart_758495 : Nat := 118140960795 + 758495 * 2 ^ 59
def prefixEnd_758495 : Nat := 4983230072969 + 3 ^ 40 * 758495 * 2
def baseEnd_758495 : Nat := 19233210322573586099963

theorem tailTrace_758495 : CollatzResearch.WordTrace tailWord_758495 prefixEnd_758495 19233210322573586099963 := by
  unfold tailWord_758495
  simp only [CollatzResearch.WordTrace]
  refine ⟨27664585387109630477852939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18443056924739753651901959 27664585387109630477852939)
  ·
    refine ⟨41496878080664445716779409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27664585387109630477852939 41496878080664445716779409)
    ·
      refine ⟨31122658560498334287584557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41496878080664445716779409 31122658560498334287584557)
      ·
        refine ⟨11670996960186875357844209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31122658560498334287584557 11670996960186875357844209)
        ·
          refine ⟨8753247720140156518383157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11670996960186875357844209 8753247720140156518383157)
          ·
            refine ⟨820616973763139673598421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8753247720140156518383157 820616973763139673598421)
            ·
              refine ⟨19233210322573586099963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 820616973763139673598421 19233210322573586099963)
              ·
                rfl

theorem cell21_758495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 7].length) (baseStart_758495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758495 prefixEnd_758495 := by exact prefixLift 758495
  have htrace : WordTrace (prefixWord ++ tailWord_758495) baseStart_758495 baseEnd_758495 := by
    simpa [prefixWord, tailWord_758495, baseEnd_758495] using wordTrace_append hprefix tailTrace_758495
  have hstable : (prefixWord ++ tailWord_758495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758495).length < 2 ^ (prefixWord ++ tailWord_758495).sum := by decide
  have hdescent : baseEnd_758495 < baseStart_758495 := by decide
  rcases family_descends (prefixWord ++ tailWord_758495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758560 : List Nat := [2, 1, 1, 5, 1, 2, 4, 2, 3]
def baseStart_758560 : Nat := 118140960795 + 758560 * 2 ^ 59
def prefixEnd_758560 : Nat := 4983230072969 + 3 ^ 40 * 758560 * 2
def baseEnd_758560 : Nat := 173113726788736606316201

theorem tailTrace_758560 : CollatzResearch.WordTrace tailWord_758560 prefixEnd_758560 173113726788736606316201 := by
  unfold tailWord_758560
  simp only [CollatzResearch.WordTrace]
  refine ⟨13833478065937073289484567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18444637421249431052646089 13833478065937073289484567)
  ·
    refine ⟨20750217098905609934226851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13833478065937073289484567 20750217098905609934226851)
    ·
      refine ⟨31125325648358414901340277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20750217098905609934226851 31125325648358414901340277)
      ·
        refine ⟨2917999279533601397000651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31125325648358414901340277 2917999279533601397000651)
        ·
          refine ⟨4376998919300402095500977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917999279533601397000651 4376998919300402095500977)
          ·
            refine ⟨3282749189475301571625733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4376998919300402095500977 3282749189475301571625733)
            ·
              refine ⟨615515473026619044679825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3282749189475301571625733 615515473026619044679825)
              ·
                refine ⟨461636604769964283509869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615515473026619044679825 461636604769964283509869)
                ·
                  refine ⟨173113726788736606316201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461636604769964283509869 173113726788736606316201)
                  ·
                    rfl

theorem cell21_758560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 3].length) (baseStart_758560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758560 prefixEnd_758560 := by exact prefixLift 758560
  have htrace : WordTrace (prefixWord ++ tailWord_758560) baseStart_758560 baseEnd_758560 := by
    simpa [prefixWord, tailWord_758560, baseEnd_758560] using wordTrace_append hprefix tailTrace_758560
  have hstable : (prefixWord ++ tailWord_758560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758560).length < 2 ^ (prefixWord ++ tailWord_758560).sum := by decide
  have hdescent : baseEnd_758560 < baseStart_758560 := by decide
  rcases family_descends (prefixWord ++ tailWord_758560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758574 : List Nat := [4, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_758574 : Nat := 118140960795 + 758574 * 2 ^ 59
def prefixEnd_758574 : Nat := 4983230072969 + 3 ^ 40 * 758574 * 2
def baseEnd_758574 : Nat := 173116921779475693082839

theorem tailTrace_758574 : CollatzResearch.WordTrace tailWord_758574 prefixEnd_758574 173116921779475693082839 := by
  unfold tailWord_758574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3458433344227928371247347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18444977835882284646652517 3458433344227928371247347)
  ·
    refine ⟨5187650016341892556871021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3458433344227928371247347 5187650016341892556871021)
    ·
      refine ⟨1945368756128209708826633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5187650016341892556871021 1945368756128209708826633)
      ·
        refine ⟨1459026567096157281619975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1945368756128209708826633 1459026567096157281619975)
        ·
          refine ⟨2188539850644235922429963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459026567096157281619975 2188539850644235922429963)
          ·
            refine ⟨3282809775966353883644945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188539850644235922429963 3282809775966353883644945)
            ·
              refine ⟨2462107331974765412733709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3282809775966353883644945 2462107331974765412733709)
              ·
                refine ⟨923290249490537029775141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2462107331974765412733709 923290249490537029775141)
                ·
                  refine ⟨173116921779475693082839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 923290249490537029775141 173116921779475693082839)
                  ·
                    rfl

theorem cell21_758574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_758574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758574 prefixEnd_758574 := by exact prefixLift 758574
  have htrace : WordTrace (prefixWord ++ tailWord_758574) baseStart_758574 baseEnd_758574 := by
    simpa [prefixWord, tailWord_758574, baseEnd_758574] using wordTrace_append hprefix tailTrace_758574
  have hstable : (prefixWord ++ tailWord_758574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758574).length < 2 ^ (prefixWord ++ tailWord_758574).sum := by decide
  have hdescent : baseEnd_758574 < baseStart_758574 := by decide
  rcases family_descends (prefixWord ++ tailWord_758574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758684 : List Nat := [2, 2, 3, 3, 3, 1, 2, 1, 4]
def baseStart_758684 : Nat := 118140960795 + 758684 * 2 ^ 59
def prefixEnd_758684 : Nat := 4983230072969 + 3 ^ 40 * 758684 * 2
def baseEnd_758684 : Nat := 173142025278139946249281

theorem tailTrace_758684 : CollatzResearch.WordTrace tailWord_758684 prefixEnd_758684 173142025278139946249281 := by
  unfold tailWord_758684
  simp only [CollatzResearch.WordTrace]
  refine ⟨13835739391712457878241553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18447652522283277170988737 13835739391712457878241553)
  ·
    refine ⟨10376804543784343408681165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13835739391712457878241553 10376804543784343408681165)
    ·
      refine ⟨3891301703919128778255437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10376804543784343408681165 3891301703919128778255437)
      ·
        refine ⟨1459238138969673291845789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3891301703919128778255437 1459238138969673291845789)
        ·
          refine ⟨547214302113627484442171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1459238138969673291845789 547214302113627484442171)
          ·
            refine ⟨820821453170441226663257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547214302113627484442171 820821453170441226663257)
            ·
              refine ⟨615616089877830919997443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820821453170441226663257 615616089877830919997443)
              ·
                refine ⟨923424134816746379996165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615616089877830919997443 923424134816746379996165)
                ·
                  refine ⟨173142025278139946249281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 923424134816746379996165 173142025278139946249281)
                  ·
                    rfl

theorem cell21_758684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_758684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758684 prefixEnd_758684 := by exact prefixLift 758684
  have htrace : WordTrace (prefixWord ++ tailWord_758684) baseStart_758684 baseEnd_758684 := by
    simpa [prefixWord, tailWord_758684, baseEnd_758684] using wordTrace_append hprefix tailTrace_758684
  have hstable : (prefixWord ++ tailWord_758684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758684).length < 2 ^ (prefixWord ++ tailWord_758684).sum := by decide
  have hdescent : baseEnd_758684 < baseStart_758684 := by decide
  rcases family_descends (prefixWord ++ tailWord_758684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758737 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 5]
def baseStart_758737 : Nat := 118140960795 + 758737 * 2 ^ 59
def prefixEnd_758737 : Nat := 4983230072969 + 3 ^ 40 * 758737 * 2
def baseEnd_758737 : Nat := 173154120600223631865839

theorem tailTrace_758737 : CollatzResearch.WordTrace tailWord_758737 prefixEnd_758737 173154120600223631865839 := by
  unfold tailWord_758737
  simp only [CollatzResearch.WordTrace]
  refine ⟨27673411852232905808162465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18448941234821937205441643 27673411852232905808162465)
  ·
    refine ⟨20755058889174679356121849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27673411852232905808162465 20755058889174679356121849)
    ·
      refine ⟨15566294166881009517091387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20755058889174679356121849 15566294166881009517091387)
      ·
        refine ⟨23349441250321514275637081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15566294166881009517091387 23349441250321514275637081)
        ·
          refine ⟨17512080937741135706727811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23349441250321514275637081 17512080937741135706727811)
          ·
            refine ⟨26268121406611703560091717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17512080937741135706727811 26268121406611703560091717)
            ·
              refine ⟨4925272763739694417517197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26268121406611703560091717 4925272763739694417517197)
              ·
                refine ⟨1846977286402385406568949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4925272763739694417517197 1846977286402385406568949)
                ·
                  refine ⟨173154120600223631865839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1846977286402385406568949 173154120600223631865839)
                  ·
                    rfl

theorem cell21_758737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_758737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758737 prefixEnd_758737 := by exact prefixLift 758737
  have htrace : WordTrace (prefixWord ++ tailWord_758737) baseStart_758737 baseEnd_758737 := by
    simpa [prefixWord, tailWord_758737, baseEnd_758737] using wordTrace_append hprefix tailTrace_758737
  have hstable : (prefixWord ++ tailWord_758737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758737).length < 2 ^ (prefixWord ++ tailWord_758737).sum := by decide
  have hdescent : baseEnd_758737 < baseStart_758737 := by decide
  rcases family_descends (prefixWord ++ tailWord_758737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758740 : List Nat := [2, 4, 1, 2, 1, 4, 1, 6]
def baseStart_758740 : Nat := 118140960795 + 758740 * 2 ^ 59
def prefixEnd_758740 : Nat := 4983230072969 + 3 ^ 40 * 758740 * 2
def baseEnd_758740 : Nat := 57718268413698764438611

theorem tailTrace_758740 : CollatzResearch.WordTrace tailWord_758740 prefixEnd_758740 57718268413698764438611 := by
  unfold tailWord_758740
  simp only [CollatzResearch.WordTrace]
  refine ⟨13836760635611018660260837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18449014180814691547014449 13836760635611018660260837)
  ·
    refine ⟨2594392619177065998798907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13836760635611018660260837 2594392619177065998798907)
    ·
      refine ⟨3891588928765598998198361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2594392619177065998798907 3891588928765598998198361)
      ·
        refine ⟨2918691696574199248648771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3891588928765598998198361 2918691696574199248648771)
        ·
          refine ⟨4378037544861298872973157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2918691696574199248648771 4378037544861298872973157)
          ·
            refine ⟨820882039661493538682467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4378037544861298872973157 820882039661493538682467)
            ·
              refine ⟨1231323059492240308023701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820882039661493538682467 1231323059492240308023701)
              ·
                refine ⟨57718268413698764438611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1231323059492240308023701 57718268413698764438611)
                ·
                  rfl

theorem cell21_758740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 6].length) (baseStart_758740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758740 prefixEnd_758740 := by exact prefixLift 758740
  have htrace : WordTrace (prefixWord ++ tailWord_758740) baseStart_758740 baseEnd_758740 := by
    simpa [prefixWord, tailWord_758740, baseEnd_758740] using wordTrace_append hprefix tailTrace_758740
  have hstable : (prefixWord ++ tailWord_758740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758740).length < 2 ^ (prefixWord ++ tailWord_758740).sum := by decide
  have hdescent : baseEnd_758740 < baseStart_758740 := by decide
  rcases family_descends (prefixWord ++ tailWord_758740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758757 : List Nat := [1, 3, 1, 6, 1, 1, 3, 5]
def baseStart_758757 : Nat := 118140960795 + 758757 * 2 ^ 59
def prefixEnd_758757 : Nat := 4983230072969 + 3 ^ 40 * 758757 * 2
def baseEnd_758757 : Nat := 57719561624236013844155

theorem tailTrace_758757 : CollatzResearch.WordTrace tailWord_758757 prefixEnd_758757 57719561624236013844155 := by
  unfold tailWord_758757
  simp only [CollatzResearch.WordTrace]
  refine ⟨27674141312160449223890525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18449427541440299482593683 27674141312160449223890525)
  ·
    refine ⟨10377802992060168458958947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27674141312160449223890525 10377802992060168458958947)
    ·
      refine ⟨15566704488090252688438421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10377802992060168458958947 15566704488090252688438421)
      ·
        refine ⟨729689272879230594770551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15566704488090252688438421 729689272879230594770551)
        ·
          refine ⟨1094533909318845892155827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729689272879230594770551 1094533909318845892155827)
          ·
            refine ⟨1641800863978268838233741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094533909318845892155827 1641800863978268838233741)
            ·
              refine ⟨615675323991850814337653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1641800863978268838233741 615675323991850814337653)
              ·
                refine ⟨57719561624236013844155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 615675323991850814337653 57719561624236013844155)
                ·
                  rfl

theorem cell21_758757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 5].length) (baseStart_758757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758757 prefixEnd_758757 := by exact prefixLift 758757
  have htrace : WordTrace (prefixWord ++ tailWord_758757) baseStart_758757 baseEnd_758757 := by
    simpa [prefixWord, tailWord_758757, baseEnd_758757] using wordTrace_append hprefix tailTrace_758757
  have hstable : (prefixWord ++ tailWord_758757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758757).length < 2 ^ (prefixWord ++ tailWord_758757).sum := by decide
  have hdescent : baseEnd_758757 < baseStart_758757 := by decide
  rcases family_descends (prefixWord ++ tailWord_758757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758785 : List Nat := [1, 2, 4, 1, 2, 2, 3, 2, 4]
def baseStart_758785 : Nat := 118140960795 + 758785 * 2 ^ 59
def prefixEnd_758785 : Nat := 4983230072969 + 3 ^ 40 * 758785 * 2
def baseEnd_758785 : Nat := 173165074854186215065741

theorem tailTrace_758785 : CollatzResearch.WordTrace tailWord_758785 prefixEnd_758785 173165074854186215065741 := by
  unfold tailWord_758785
  simp only [CollatzResearch.WordTrace]
  refine ⟨27675162556059010005909809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18450108370706006670606539 27675162556059010005909809)
  ·
    refine ⟨20756371917044257504432357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27675162556059010005909809 20756371917044257504432357)
    ·
      refine ⟨3891819734445798282081067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20756371917044257504432357 3891819734445798282081067)
      ·
        refine ⟨5837729601668697423121601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3891819734445798282081067 5837729601668697423121601)
        ·
          refine ⟨4378297201251523067341201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5837729601668697423121601 4378297201251523067341201)
          ·
            refine ⟨3283722900938642300505901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4378297201251523067341201 3283722900938642300505901)
            ·
              refine ⟨1231396087851990862689713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3283722900938642300505901 1231396087851990862689713)
              ·
                refine ⟨923547065888993147017285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231396087851990862689713 923547065888993147017285)
                ·
                  refine ⟨173165074854186215065741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 923547065888993147017285 173165074854186215065741)
                  ·
                    rfl

theorem cell21_758785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_758785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758785 prefixEnd_758785 := by exact prefixLift 758785
  have htrace : WordTrace (prefixWord ++ tailWord_758785) baseStart_758785 baseEnd_758785 := by
    simpa [prefixWord, tailWord_758785, baseEnd_758785] using wordTrace_append hprefix tailTrace_758785
  have hstable : (prefixWord ++ tailWord_758785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758785).length < 2 ^ (prefixWord ++ tailWord_758785).sum := by decide
  have hdescent : baseEnd_758785 < baseStart_758785 := by decide
  rcases family_descends (prefixWord ++ tailWord_758785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758816 : List Nat := [2, 1, 1, 7, 1, 1, 1, 7]
def baseStart_758816 : Nat := 118140960795 + 758816 * 2 ^ 59
def prefixEnd_758816 : Nat := 4983230072969 + 3 ^ 40 * 758816 * 2
def baseEnd_758816 : Nat := 57724049825512350016337

theorem tailTrace_758816 : CollatzResearch.WordTrace tailWord_758816 prefixEnd_758816 57724049825512350016337 := by
  unfold tailWord_758816
  simp only [CollatzResearch.WordTrace]
  refine ⟨13838146609473351150144151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18450862145964468200192201 13838146609473351150144151)
  ·
    refine ⟨20757219914210026725216227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13838146609473351150144151 20757219914210026725216227)
    ·
      refine ⟨31135829871315040087824341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20757219914210026725216227 31135829871315040087824341)
      ·
        refine ⟨729746012608946252058383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 31135829871315040087824341 729746012608946252058383)
        ·
          refine ⟨1094619018913419378087575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729746012608946252058383 1094619018913419378087575)
          ·
            refine ⟨1641928528370129067131363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094619018913419378087575 1641928528370129067131363)
            ·
              refine ⟨2462892792555193600697045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641928528370129067131363 2462892792555193600697045)
              ·
                refine ⟨57724049825512350016337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2462892792555193600697045 57724049825512350016337)
                ·
                  rfl

theorem cell21_758816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 7].length) (baseStart_758816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758816 prefixEnd_758816 := by exact prefixLift 758816
  have htrace : WordTrace (prefixWord ++ tailWord_758816) baseStart_758816 baseEnd_758816 := by
    simpa [prefixWord, tailWord_758816, baseEnd_758816] using wordTrace_append hprefix tailTrace_758816
  have hstable : (prefixWord ++ tailWord_758816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758816).length < 2 ^ (prefixWord ++ tailWord_758816).sum := by decide
  have hdescent : baseEnd_758816 < baseStart_758816 := by decide
  rcases family_descends (prefixWord ++ tailWord_758816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758827 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 8]
def baseStart_758827 : Nat := 118140960795 + 758827 * 2 ^ 59
def prefixEnd_758827 : Nat := 4983230072969 + 3 ^ 40 * 758827 * 2
def baseEnd_758827 : Nat := 173174659826403475365655

theorem tailTrace_758827 : CollatzResearch.WordTrace tailWord_758827 prefixEnd_758827 173174659826403475365655 := by
  unfold tailWord_758827
  simp only [CollatzResearch.WordTrace]
  refine ⟨27676694421906851178938735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18451129614604567452625823 27676694421906851178938735)
  ·
    refine ⟨41515041632860276768408103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27676694421906851178938735 41515041632860276768408103)
    ·
      refine ⟨62272562449290415152612155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41515041632860276768408103 62272562449290415152612155)
      ·
        refine ⟨93408843673935622728918233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62272562449290415152612155 93408843673935622728918233)
        ·
          refine ⟨70056632755451717046688675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93408843673935622728918233 70056632755451717046688675)
          ·
            refine ⟨105084949133177575570033013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70056632755451717046688675 105084949133177575570033013)
            ·
              refine ⟨9851713981235397709690595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105084949133177575570033013 9851713981235397709690595)
              ·
                refine ⟨14777570971853096564535893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9851713981235397709690595 14777570971853096564535893)
                ·
                  refine ⟨173174659826403475365655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14777570971853096564535893 173174659826403475365655)
                  ·
                    rfl

theorem cell21_758827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_758827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758827 prefixEnd_758827 := by exact prefixLift 758827
  have htrace : WordTrace (prefixWord ++ tailWord_758827) baseStart_758827 baseEnd_758827 := by
    simpa [prefixWord, tailWord_758827, baseEnd_758827] using wordTrace_append hprefix tailTrace_758827
  have hstable : (prefixWord ++ tailWord_758827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758827).length < 2 ^ (prefixWord ++ tailWord_758827).sum := by decide
  have hdescent : baseEnd_758827 < baseStart_758827 := by decide
  rcases family_descends (prefixWord ++ tailWord_758827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758844 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 6]
def baseStart_758844 : Nat := 118140960795 + 758844 * 2 ^ 59
def prefixEnd_758844 : Nat := 4983230072969 + 3 ^ 40 * 758844 * 2
def baseEnd_758844 : Nat := 173178539458015223582287

theorem tailTrace_758844 : CollatzResearch.WordTrace tailWord_758844 prefixEnd_758844 173178539458015223582287 := by
  unfold tailWord_758844
  simp only [CollatzResearch.WordTrace]
  refine ⟨13838657231422631541153793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18451542975230175388205057 13838657231422631541153793)
  ·
    refine ⟨10378992923566973655865345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13838657231422631541153793 10378992923566973655865345)
    ·
      refine ⟨7784244692675230241899009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10378992923566973655865345 7784244692675230241899009)
      ·
        refine ⟨5838183519506422681424257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7784244692675230241899009 5838183519506422681424257)
        ·
          refine ⟨4378637639629817011068193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5838183519506422681424257 4378637639629817011068193)
          ·
            refine ⟨3283978229722362758301145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4378637639629817011068193 3283978229722362758301145)
            ·
              refine ⟨2462983672291772068725859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3283978229722362758301145 2462983672291772068725859)
              ·
                refine ⟨3694475508437658103088789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462983672291772068725859 3694475508437658103088789)
                ·
                  refine ⟨173178539458015223582287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3694475508437658103088789 173178539458015223582287)
                  ·
                    rfl

theorem cell21_758844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_758844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758844 prefixEnd_758844 := by exact prefixLift 758844
  have htrace : WordTrace (prefixWord ++ tailWord_758844) baseStart_758844 baseEnd_758844 := by
    simpa [prefixWord, tailWord_758844, baseEnd_758844] using wordTrace_append hprefix tailTrace_758844
  have hstable : (prefixWord ++ tailWord_758844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758844).length < 2 ^ (prefixWord ++ tailWord_758844).sum := by decide
  have hdescent : baseEnd_758844 < baseStart_758844 := by decide
  rcases family_descends (prefixWord ++ tailWord_758844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758858 : List Nat := [3, 1, 2, 1, 1, 2, 3, 8]
def baseStart_758858 : Nat := 118140960795 + 758858 * 2 ^ 59
def prefixEnd_758858 : Nat := 4983230072969 + 3 ^ 40 * 758858 * 2
def baseEnd_758858 : Nat := 57727244816251436782975

theorem tailTrace_758858 : CollatzResearch.WordTrace tailWord_758858 prefixEnd_758858 57727244816251436782975 := by
  unfold tailWord_758858
  simp only [CollatzResearch.WordTrace]
  refine ⟨6919456271198635868329307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18451883389863028982211485 6919456271198635868329307)
  ·
    refine ⟨10379184406797953802493961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6919456271198635868329307 10379184406797953802493961)
    ·
      refine ⟨7784388305098465351870471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10379184406797953802493961 7784388305098465351870471)
      ·
        refine ⟨11676582457647698027805707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7784388305098465351870471 11676582457647698027805707)
        ·
          refine ⟨17514873686471547041708561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11676582457647698027805707 17514873686471547041708561)
          ·
            refine ⟨13136155264853660281281421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17514873686471547041708561 13136155264853660281281421)
            ·
              refine ⟨4926058224320122605480533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13136155264853660281281421 4926058224320122605480533)
              ·
                refine ⟨57727244816251436782975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4926058224320122605480533 57727244816251436782975)
                ·
                  rfl

theorem cell21_758858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_758858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758858 prefixEnd_758858 := by exact prefixLift 758858
  have htrace : WordTrace (prefixWord ++ tailWord_758858) baseStart_758858 baseEnd_758858 := by
    simpa [prefixWord, tailWord_758858, baseEnd_758858] using wordTrace_append hprefix tailTrace_758858
  have hstable : (prefixWord ++ tailWord_758858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758858).length < 2 ^ (prefixWord ++ tailWord_758858).sum := by decide
  have hdescent : baseEnd_758858 < baseStart_758858 := by decide
  rcases family_descends (prefixWord ++ tailWord_758858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758951 : List Nat := [1, 1, 6, 2, 1, 2, 8]
def baseStart_758951 : Nat := 118140960795 + 758951 * 2 ^ 59
def prefixEnd_758951 : Nat := 4983230072969 + 3 ^ 40 * 758951 * 2
def baseEnd_758951 : Nat := 19244773146200757255415

theorem tailTrace_758951 : CollatzResearch.WordTrace tailWord_758951 prefixEnd_758951 19244773146200757255415 := by
  unfold tailWord_758951
  simp only [CollatzResearch.WordTrace]
  refine ⟨27681217073457620356452707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18454144715638413570968471 27681217073457620356452707)
  ·
    refine ⟨41521825610186430534679061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27681217073457620356452707 41521825610186430534679061)
    ·
      refine ⟨1946335575477488931313081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41521825610186430534679061 1946335575477488931313081)
      ·
        refine ⟨1459751681608116698484811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1946335575477488931313081 1459751681608116698484811)
        ·
          refine ⟨2189627522412175047727217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459751681608116698484811 2189627522412175047727217)
          ·
            refine ⟨1642220641809131285795413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2189627522412175047727217 1642220641809131285795413)
            ·
              refine ⟨19244773146200757255415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1642220641809131285795413 19244773146200757255415)
              ·
                rfl

theorem cell21_758951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 8].length) (baseStart_758951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758951 prefixEnd_758951 := by exact prefixLift 758951
  have htrace : WordTrace (prefixWord ++ tailWord_758951) baseStart_758951 baseEnd_758951 := by
    simpa [prefixWord, tailWord_758951, baseEnd_758951] using wordTrace_append hprefix tailTrace_758951
  have hstable : (prefixWord ++ tailWord_758951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758951).length < 2 ^ (prefixWord ++ tailWord_758951).sum := by decide
  have hdescent : baseEnd_758951 < baseStart_758951 := by decide
  rcases family_descends (prefixWord ++ tailWord_758951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758954 : List Nat := [3, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_758954 : Nat := 118140960795 + 758954 * 2 ^ 59
def prefixEnd_758954 : Nat := 4983230072969 + 3 ^ 40 * 758954 * 2
def baseEnd_758954 : Nat := 173203642956679476748729

theorem tailTrace_758954 : CollatzResearch.WordTrace tailWord_758954 prefixEnd_758954 173203642956679476748729 := by
  unfold tailWord_758954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6920331623111687967202979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18454217661631167912541277 6920331623111687967202979)
  ·
    refine ⟨10380497434667531950804469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6920331623111687967202979 10380497434667531950804469)
    ·
      refine ⟨973171634500081120387919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10380497434667531950804469 973171634500081120387919)
      ·
        refine ⟨1459757451750121680581879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 973171634500081120387919 1459757451750121680581879)
        ·
          refine ⟨2189636177625182520872819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459757451750121680581879 2189636177625182520872819)
          ·
            refine ⟨3284454266437773781309229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189636177625182520872819 3284454266437773781309229)
            ·
              refine ⟨1231670349914165167990961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3284454266437773781309229 1231670349914165167990961)
              ·
                refine ⟨923752762435623875993221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231670349914165167990961 923752762435623875993221)
                ·
                  refine ⟨173203642956679476748729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 923752762435623875993221 173203642956679476748729)
                  ·
                    rfl

theorem cell21_758954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_758954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_758954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_758954 prefixEnd_758954 := by exact prefixLift 758954
  have htrace : WordTrace (prefixWord ++ tailWord_758954) baseStart_758954 baseEnd_758954 := by
    simpa [prefixWord, tailWord_758954, baseEnd_758954] using wordTrace_append hprefix tailTrace_758954
  have hstable : (prefixWord ++ tailWord_758954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758954).length < 2 ^ (prefixWord ++ tailWord_758954).sum := by decide
  have hdescent : baseEnd_758954 < baseStart_758954 := by decide
  rcases family_descends (prefixWord ++ tailWord_758954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759075 : List Nat := [1, 1, 1, 4, 2, 3, 4, 2, 3]
def baseStart_759075 : Nat := 118140960795 + 759075 * 2 ^ 59
def prefixEnd_759075 : Nat := 4983230072969 + 3 ^ 40 * 759075 * 2
def baseEnd_759075 : Nat := 173231256805210155231815

theorem tailTrace_759075 : CollatzResearch.WordTrace tailWord_759075 prefixEnd_759075 173231256805210155231815 := by
  unfold tailWord_759075
  simp only [CollatzResearch.WordTrace]
  refine ⟨27685739725008389533966679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18457159816672259689311119 27685739725008389533966679)
  ·
    refine ⟨41528609587512584300950019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27685739725008389533966679 41528609587512584300950019)
    ·
      refine ⟨62292914381268876451425029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41528609587512584300950019 62292914381268876451425029)
      ·
        refine ⟨11679921446487914334642193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62292914381268876451425029 11679921446487914334642193)
        ·
          refine ⟨8759941084865935750981645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11679921446487914334642193 8759941084865935750981645)
          ·
            refine ⟨3284977906824725906618117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8759941084865935750981645 3284977906824725906618117)
            ·
              refine ⟨615933357529636107490897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3284977906824725906618117 615933357529636107490897)
              ·
                refine ⟨461950018147227080618173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615933357529636107490897 461950018147227080618173)
                ·
                  refine ⟨173231256805210155231815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461950018147227080618173 173231256805210155231815)
                  ·
                    rfl

theorem cell21_759075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 3].length) (baseStart_759075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759075 prefixEnd_759075 := by exact prefixLift 759075
  have htrace : WordTrace (prefixWord ++ tailWord_759075) baseStart_759075 baseEnd_759075 := by
    simpa [prefixWord, tailWord_759075, baseEnd_759075] using wordTrace_append hprefix tailTrace_759075
  have hstable : (prefixWord ++ tailWord_759075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759075).length < 2 ^ (prefixWord ++ tailWord_759075).sum := by decide
  have hdescent : baseEnd_759075 < baseStart_759075 := by decide
  rcases family_descends (prefixWord ++ tailWord_759075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759103 : List Nat := [1, 1, 2, 2, 4, 3, 3, 5]
def baseStart_759103 : Nat := 118140960795 + 759103 * 2 ^ 59
def prefixEnd_759103 : Nat := 4983230072969 + 3 ^ 40 * 759103 * 2
def baseEnd_759103 : Nat := 57745882262229442921697

theorem tailTrace_759103 : CollatzResearch.WordTrace tailWord_759103 prefixEnd_759103 57745882262229442921697 := by
  unfold tailWord_759103
  simp only [CollatzResearch.WordTrace]
  refine ⟨27686760968906950315985963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18457840645937966877323975 27686760968906950315985963)
  ·
    refine ⟨41530141453360425473978945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27686760968906950315985963 41530141453360425473978945)
    ·
      refine ⟨31147606090020319105484209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41530141453360425473978945 31147606090020319105484209)
      ·
        refine ⟨23360704567515239329113157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31147606090020319105484209 23360704567515239329113157)
        ·
          refine ⟨4380132106409107374208717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23360704567515239329113157 4380132106409107374208717)
          ·
            refine ⟨1642549539903415265328269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4380132106409107374208717 1642549539903415265328269)
            ·
              refine ⟨615956077463780724498101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1642549539903415265328269 615956077463780724498101)
              ·
                refine ⟨57745882262229442921697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 615956077463780724498101 57745882262229442921697)
                ·
                  rfl

theorem cell21_759103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 5].length) (baseStart_759103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759103 prefixEnd_759103 := by exact prefixLift 759103
  have htrace : WordTrace (prefixWord ++ tailWord_759103) baseStart_759103 baseEnd_759103 := by
    simpa [prefixWord, tailWord_759103, baseEnd_759103] using wordTrace_append hprefix tailTrace_759103
  have hstable : (prefixWord ++ tailWord_759103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759103).length < 2 ^ (prefixWord ++ tailWord_759103).sum := by decide
  have hdescent : baseEnd_759103 < baseStart_759103 := by decide
  rcases family_descends (prefixWord ++ tailWord_759103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759193 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 5]
def baseStart_759193 : Nat := 118140960795 + 759193 * 2 ^ 59
def prefixEnd_759193 : Nat := 4983230072969 + 3 ^ 40 * 759193 * 2
def baseEnd_759193 : Nat := 173258186012868172264907

theorem tailTrace_759193 : CollatzResearch.WordTrace tailWord_759193 prefixEnd_759193 173258186012868172264907 := by
  unfold tailWord_759193
  simp only [CollatzResearch.WordTrace]
  refine ⟨27690043538580895686762233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18460029025720597124508155 27690043538580895686762233)
  ·
    refine ⟨20767532653935671765071675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27690043538580895686762233 20767532653935671765071675)
    ·
      refine ⟨31151298980903507647607513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20767532653935671765071675 31151298980903507647607513)
      ·
        refine ⟨23363474235677630735705635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31151298980903507647607513 23363474235677630735705635)
        ·
          refine ⟨35045211353516446103558453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23363474235677630735705635 35045211353516446103558453)
          ·
            refine ⟨3285488564392166822208605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35045211353516446103558453 3285488564392166822208605)
            ·
              refine ⟨1232058211647062558328227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3285488564392166822208605 1232058211647062558328227)
              ·
                refine ⟨1848087317470593837492341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232058211647062558328227 1848087317470593837492341)
                ·
                  refine ⟨173258186012868172264907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1848087317470593837492341 173258186012868172264907)
                  ·
                    rfl

theorem cell21_759193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_759193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759193 prefixEnd_759193 := by exact prefixLift 759193
  have htrace : WordTrace (prefixWord ++ tailWord_759193) baseStart_759193 baseEnd_759193 := by
    simpa [prefixWord, tailWord_759193, baseEnd_759193] using wordTrace_append hprefix tailTrace_759193
  have hstable : (prefixWord ++ tailWord_759193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759193).length < 2 ^ (prefixWord ++ tailWord_759193).sum := by decide
  have hdescent : baseEnd_759193 < baseStart_759193 := by decide
  rcases family_descends (prefixWord ++ tailWord_759193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759196 : List Nat := [2, 2, 3, 4, 1, 1, 2, 6]
def baseStart_759196 : Nat := 118140960795 + 759196 * 2 ^ 59
def prefixEnd_759196 : Nat := 4983230072969 + 3 ^ 40 * 759196 * 2
def baseEnd_759196 : Nat := 57752956884580277904967

theorem tailTrace_759196 : CollatzResearch.WordTrace tailWord_759196 prefixEnd_759196 57752956884580277904967 := by
  unfold tailWord_759196
  simp only [CollatzResearch.WordTrace]
  refine ⟨13845076478785013599560721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18460101971713351466080961 13845076478785013599560721)
  ·
    refine ⟨10383807359088760199670541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13845076478785013599560721 10383807359088760199670541)
    ·
      refine ⟨3893927759658285074876453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10383807359088760199670541 3893927759658285074876453)
      ·
        refine ⟨730111454935928451539335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3893927759658285074876453 730111454935928451539335)
        ·
          refine ⟨1095167182403892677309003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730111454935928451539335 1095167182403892677309003)
          ·
            refine ⟨1642750773605839015963505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095167182403892677309003 1642750773605839015963505)
            ·
              refine ⟨1232063080204379261972629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1642750773605839015963505 1232063080204379261972629)
              ·
                refine ⟨57752956884580277904967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1232063080204379261972629 57752956884580277904967)
                ·
                  rfl

theorem cell21_759196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 6].length) (baseStart_759196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759196 prefixEnd_759196 := by exact prefixLift 759196
  have htrace : WordTrace (prefixWord ++ tailWord_759196) baseStart_759196 baseEnd_759196 := by
    simpa [prefixWord, tailWord_759196, baseEnd_759196] using wordTrace_append hprefix tailTrace_759196
  have hstable : (prefixWord ++ tailWord_759196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759196).length < 2 ^ (prefixWord ++ tailWord_759196).sum := by decide
  have hdescent : baseEnd_759196 < baseStart_759196 := by decide
  rcases family_descends (prefixWord ++ tailWord_759196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759244 : List Nat := [2, 2, 1, 4, 2, 3, 2, 2, 3]
def baseStart_759244 : Nat := 118140960795 + 759244 * 2 ^ 59
def prefixEnd_759244 : Nat := 4983230072969 + 3 ^ 40 * 759244 * 2
def baseEnd_759244 : Nat := 173269824907703416914803

theorem tailTrace_759244 : CollatzResearch.WordTrace tailWord_759244 prefixEnd_759244 173269824907703416914803 := by
  unfold tailWord_759244
  simp only [CollatzResearch.WordTrace]
  refine ⟨13845951830698065698434393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18461269107597420931245857 13845951830698065698434393)
  ·
    refine ⟨10384463873023549273825795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13845951830698065698434393 10384463873023549273825795)
    ·
      refine ⟨15576695809535323910738693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10384463873023549273825795 15576695809535323910738693)
      ·
        refine ⟨2920630464287873233263505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15576695809535323910738693 2920630464287873233263505)
        ·
          refine ⟨2190472848215904924947629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2920630464287873233263505 2190472848215904924947629)
          ·
            refine ⟨821427318080964346855361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2190472848215904924947629 821427318080964346855361)
            ·
              refine ⟨616070488560723260141521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821427318080964346855361 616070488560723260141521)
              ·
                refine ⟨462052866420542445106141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616070488560723260141521 462052866420542445106141)
                ·
                  refine ⟨173269824907703416914803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462052866420542445106141 173269824907703416914803)
                  ·
                    rfl

theorem cell21_759244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_759244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759244 prefixEnd_759244 := by exact prefixLift 759244
  have htrace : WordTrace (prefixWord ++ tailWord_759244) baseStart_759244 baseEnd_759244 := by
    simpa [prefixWord, tailWord_759244, baseEnd_759244] using wordTrace_append hprefix tailTrace_759244
  have hstable : (prefixWord ++ tailWord_759244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759244).length < 2 ^ (prefixWord ++ tailWord_759244).sum := by decide
  have hdescent : baseEnd_759244 < baseStart_759244 := by decide
  rcases family_descends (prefixWord ++ tailWord_759244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759269 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 7]
def baseStart_759269 : Nat := 118140960795 + 759269 * 2 ^ 59
def prefixEnd_759269 : Nat := 4983230072969 + 3 ^ 40 * 759269 * 2
def baseEnd_759269 : Nat := 173275530248308928998085

theorem tailTrace_759269 : CollatzResearch.WordTrace tailWord_759269 prefixEnd_759269 173275530248308928998085 := by
  unfold tailWord_759269
  simp only [CollatzResearch.WordTrace]
  refine ⟨27692815486305560666528861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18461876990870373777685907 27692815486305560666528861)
  ·
    refine ⟨10384805807364585249948323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27692815486305560666528861 10384805807364585249948323)
    ·
      refine ⟨15577208711046877874922485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10384805807364585249948323 15577208711046877874922485)
      ·
        refine ⟨1460363316660644800773983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15577208711046877874922485 1460363316660644800773983)
        ·
          refine ⟨2190544974990967201160975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1460363316660644800773983 2190544974990967201160975)
          ·
            refine ⟨3285817462486450801741463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2190544974990967201160975 3285817462486450801741463)
            ·
              refine ⟨4928726193729676202612195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3285817462486450801741463 4928726193729676202612195)
              ·
                refine ⟨7393089290594514303918293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4928726193729676202612195 7393089290594514303918293)
                ·
                  refine ⟨173275530248308928998085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7393089290594514303918293 173275530248308928998085)
                  ·
                    rfl

theorem cell21_759269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_759269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759269 prefixEnd_759269 := by exact prefixLift 759269
  have htrace : WordTrace (prefixWord ++ tailWord_759269) baseStart_759269 baseEnd_759269 := by
    simpa [prefixWord, tailWord_759269, baseEnd_759269] using wordTrace_append hprefix tailTrace_759269
  have hstable : (prefixWord ++ tailWord_759269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759269).length < 2 ^ (prefixWord ++ tailWord_759269).sum := by decide
  have hdescent : baseEnd_759269 < baseStart_759269 := by decide
  rcases family_descends (prefixWord ++ tailWord_759269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759317 : List Nat := [1, 3, 2, 1, 3, 3, 3, 1, 4]
def baseStart_759317 : Nat := 118140960795 + 759317 * 2 ^ 59
def prefixEnd_759317 : Nat := 4983230072969 + 3 ^ 40 * 759317 * 2
def baseEnd_759317 : Nat := 173286484502271512197987

theorem tailTrace_759317 : CollatzResearch.WordTrace tailWord_759317 prefixEnd_759317 173286484502271512197987 := by
  unfold tailWord_759317
  simp only [CollatzResearch.WordTrace]
  refine ⟨27694566190131664864276205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18463044126754443242850803 27694566190131664864276205)
  ·
    refine ⟨10385462321299374324103577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27694566190131664864276205 10385462321299374324103577)
    ·
      refine ⟨7789096740974530743077683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10385462321299374324103577 7789096740974530743077683)
      ·
        refine ⟨11683645111461796114616525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7789096740974530743077683 11683645111461796114616525)
        ·
          refine ⟨4381366916798173542981197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11683645111461796114616525 4381366916798173542981197)
          ·
            refine ⟨1643012593799315078617949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4381366916798173542981197 1643012593799315078617949)
            ·
              refine ⟨616129722674743154481731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1643012593799315078617949 616129722674743154481731)
              ·
                refine ⟨924194584012114731722597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616129722674743154481731 924194584012114731722597)
                ·
                  refine ⟨173286484502271512197987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 924194584012114731722597 173286484502271512197987)
                  ·
                    rfl

theorem cell21_759317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_759317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759317 prefixEnd_759317 := by exact prefixLift 759317
  have htrace : WordTrace (prefixWord ++ tailWord_759317) baseStart_759317 baseEnd_759317 := by
    simpa [prefixWord, tailWord_759317, baseEnd_759317] using wordTrace_append hprefix tailTrace_759317
  have hstable : (prefixWord ++ tailWord_759317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759317).length < 2 ^ (prefixWord ++ tailWord_759317).sum := by decide
  have hdescent : baseEnd_759317 < baseStart_759317 := by decide
  rcases family_descends (prefixWord ++ tailWord_759317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759359 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 6]
def baseStart_759359 : Nat := 118140960795 + 759359 * 2 ^ 59
def prefixEnd_759359 : Nat := 4983230072969 + 3 ^ 40 * 759359 * 2
def baseEnd_759359 : Nat := 173296069474488772497901

theorem tailTrace_759359 : CollatzResearch.WordTrace tailWord_759359 prefixEnd_759359 173296069474488772497901 := by
  unfold tailWord_759359
  simp only [CollatzResearch.WordTrace]
  refine ⟨27696098055979506037305131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18464065370653004024870087 27696098055979506037305131)
  ·
    refine ⟨41544147083969259055957697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27696098055979506037305131 41544147083969259055957697)
    ·
      refine ⟨31158110312976944291968273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41544147083969259055957697 31158110312976944291968273)
      ·
        refine ⟨23368582734732708218976205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31158110312976944291968273 23368582734732708218976205)
        ·
          refine ⟨8763218525524765582116077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23368582734732708218976205 8763218525524765582116077)
          ·
            refine ⟨3286206947071787093293529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8763218525524765582116077 3286206947071787093293529)
            ·
              refine ⟨2464655210303840319970147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3286206947071787093293529 2464655210303840319970147)
              ·
                refine ⟨3696982815455760479955221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464655210303840319970147 3696982815455760479955221)
                ·
                  refine ⟨173296069474488772497901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3696982815455760479955221 173296069474488772497901)
                  ·
                    rfl

theorem cell21_759359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 6].length) (baseStart_759359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759359 prefixEnd_759359 := by exact prefixLift 759359
  have htrace : WordTrace (prefixWord ++ tailWord_759359) baseStart_759359 baseEnd_759359 := by
    simpa [prefixWord, tailWord_759359, baseEnd_759359] using wordTrace_append hprefix tailTrace_759359
  have hstable : (prefixWord ++ tailWord_759359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759359).length < 2 ^ (prefixWord ++ tailWord_759359).sum := by decide
  have hdescent : baseEnd_759359 < baseStart_759359 := by decide
  rcases family_descends (prefixWord ++ tailWord_759359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759435 : List Nat := [1, 1, 1, 1, 4, 1, 3, 5, 4]
def baseStart_759435 : Nat := 118140960795 + 759435 * 2 ^ 59
def prefixEnd_759435 : Nat := 4983230072969 + 3 ^ 40 * 759435 * 2
def baseEnd_759435 : Nat := 173313413709929529231079

theorem tailTrace_759435 : CollatzResearch.WordTrace tailWord_759435 prefixEnd_759435 173313413709929529231079 := by
  unfold tailWord_759435
  simp only [CollatzResearch.WordTrace]
  refine ⟨27698870003704171017071759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18465913335802780678047839 27698870003704171017071759)
  ·
    refine ⟨41548305005556256525607639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27698870003704171017071759 41548305005556256525607639)
    ·
      refine ⟨62322457508334384788411459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41548305005556256525607639 62322457508334384788411459)
      ·
        refine ⟨93483686262501577182617189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62322457508334384788411459 93483686262501577182617189)
        ·
          refine ⟨17528191174219045721740723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93483686262501577182617189 17528191174219045721740723)
          ·
            refine ⟨26292286761328568582611085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17528191174219045721740723 26292286761328568582611085)
            ·
              refine ⟨9859607535498213218479157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26292286761328568582611085 9859607535498213218479157)
              ·
                refine ⟨924338206452957489232421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9859607535498213218479157 924338206452957489232421)
                ·
                  refine ⟨173313413709929529231079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 924338206452957489232421 173313413709929529231079)
                  ·
                    rfl

theorem cell21_759435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 4].length) (baseStart_759435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759435 prefixEnd_759435 := by exact prefixLift 759435
  have htrace : WordTrace (prefixWord ++ tailWord_759435) baseStart_759435 baseEnd_759435 := by
    simpa [prefixWord, tailWord_759435, baseEnd_759435] using wordTrace_append hprefix tailTrace_759435
  have hstable : (prefixWord ++ tailWord_759435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759435).length < 2 ^ (prefixWord ++ tailWord_759435).sum := by decide
  have hdescent : baseEnd_759435 < baseStart_759435 := by decide
  rcases family_descends (prefixWord ++ tailWord_759435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759500 : List Nat := [2, 2, 1, 5, 2, 2, 2, 5]
def baseStart_759500 : Nat := 118140960795 + 759500 * 2 ^ 59
def prefixEnd_759500 : Nat := 4983230072969 + 3 ^ 40 * 759500 * 2
def baseEnd_759500 : Nat := 57776082531834620215871

theorem tailTrace_759500 : CollatzResearch.WordTrace tailWord_759500 prefixEnd_759500 57776082531834620215871 := by
  unfold tailWord_759500
  simp only [CollatzResearch.WordTrace]
  refine ⟨13850620374234343559093977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18467493832312458078791969 13850620374234343559093977)
  ·
    refine ⟨10387965280675757669320483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13850620374234343559093977 10387965280675757669320483)
    ·
      refine ⟨15581947921013636503980725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10387965280675757669320483 15581947921013636503980725)
      ·
        refine ⟨1460807617595028422248193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15581947921013636503980725 1460807617595028422248193)
        ·
          refine ⟨1095605713196271316686145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1460807617595028422248193 1095605713196271316686145)
          ·
            refine ⟨821704284897203487514609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1095605713196271316686145 821704284897203487514609)
            ·
              refine ⟨616278213672902615635957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821704284897203487514609 616278213672902615635957)
              ·
                refine ⟨57776082531834620215871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 616278213672902615635957 57776082531834620215871)
                ·
                  rfl

theorem cell21_759500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 5].length) (baseStart_759500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759500 prefixEnd_759500 := by exact prefixLift 759500
  have htrace : WordTrace (prefixWord ++ tailWord_759500) baseStart_759500 baseEnd_759500 := by
    simpa [prefixWord, tailWord_759500, baseEnd_759500] using wordTrace_append hprefix tailTrace_759500
  have hstable : (prefixWord ++ tailWord_759500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759500).length < 2 ^ (prefixWord ++ tailWord_759500).sum := by decide
  have hdescent : baseEnd_759500 < baseStart_759500 := by decide
  rcases family_descends (prefixWord ++ tailWord_759500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759514 : List Nat := [3, 1, 1, 2, 2, 3, 3, 3, 3]
def baseStart_759514 : Nat := 118140960795 + 759514 * 2 ^ 59
def prefixEnd_759514 : Nat := 4983230072969 + 3 ^ 40 * 759514 * 2
def baseEnd_759514 : Nat := 173331442586242947414251

theorem tailTrace_759514 : CollatzResearch.WordTrace tailWord_759514 prefixEnd_759514 173331442586242947414251 := by
  unfold tailWord_759514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6925437842604491877299399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18467834246945311672798397 6925437842604491877299399)
  ·
    refine ⟨10388156763906737815949099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6925437842604491877299399 10388156763906737815949099)
    ·
      refine ⟨15582235145860106723923649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10388156763906737815949099 15582235145860106723923649)
      ·
        refine ⟨11686676359395080042942737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15582235145860106723923649 11686676359395080042942737)
        ·
          refine ⟨8765007269546310032207053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11686676359395080042942737 8765007269546310032207053)
          ·
            refine ⟨3286877726079866262077645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8765007269546310032207053 3286877726079866262077645)
            ·
              refine ⟨1232579147279949848279117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3286877726079866262077645 1232579147279949848279117)
              ·
                refine ⟨462217180229981193104669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1232579147279949848279117 462217180229981193104669)
                ·
                  refine ⟨173331442586242947414251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462217180229981193104669 173331442586242947414251)
                  ·
                    rfl

theorem cell21_759514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_759514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759514 prefixEnd_759514 := by exact prefixLift 759514
  have htrace : WordTrace (prefixWord ++ tailWord_759514) baseStart_759514 baseEnd_759514 := by
    simpa [prefixWord, tailWord_759514, baseEnd_759514] using wordTrace_append hprefix tailTrace_759514
  have hstable : (prefixWord ++ tailWord_759514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759514).length < 2 ^ (prefixWord ++ tailWord_759514).sum := by decide
  have hdescent : baseEnd_759514 < baseStart_759514 := by decide
  rcases family_descends (prefixWord ++ tailWord_759514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759542 : List Nat := [5, 1, 1, 1, 1, 3, 1, 8]
def baseStart_759542 : Nat := 118140960795 + 759542 * 2 ^ 59
def prefixEnd_759542 : Nat := 4983230072969 + 3 ^ 40 * 759542 * 2
def baseEnd_759542 : Nat := 57779277522573706982509

theorem tailTrace_759542 : CollatzResearch.WordTrace tailWord_759542 prefixEnd_759542 57779277522573706982509 := by
  unfold tailWord_759542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1731423288394783018201055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18468515076211018860811253 1731423288394783018201055)
  ·
    refine ⟨2597134932592174527301583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1731423288394783018201055 2597134932592174527301583)
    ·
      refine ⟨3895702398888261790952375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2597134932592174527301583 3895702398888261790952375)
      ·
        refine ⟨5843553598332392686428563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3895702398888261790952375 5843553598332392686428563)
        ·
          refine ⟨8765330397498589029642845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5843553598332392686428563 8765330397498589029642845)
          ·
            refine ⟨3286998899061970886116067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8765330397498589029642845 3286998899061970886116067)
            ·
              refine ⟨4930498348592956329174101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286998899061970886116067 4930498348592956329174101)
              ·
                refine ⟨57779277522573706982509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4930498348592956329174101 57779277522573706982509)
                ·
                  rfl

theorem cell21_759542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_759542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759542 prefixEnd_759542 := by exact prefixLift 759542
  have htrace : WordTrace (prefixWord ++ tailWord_759542) baseStart_759542 baseEnd_759542 := by
    simpa [prefixWord, tailWord_759542, baseEnd_759542] using wordTrace_append hprefix tailTrace_759542
  have hstable : (prefixWord ++ tailWord_759542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759542).length < 2 ^ (prefixWord ++ tailWord_759542).sum := by decide
  have hdescent : baseEnd_759542 < baseStart_759542 := by decide
  rcases family_descends (prefixWord ++ tailWord_759542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759582 : List Nat := [4, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_759582 : Nat := 118140960795 + 759582 * 2 ^ 59
def prefixEnd_759582 : Nat := 4983230072969 + 3 ^ 40 * 759582 * 2
def baseEnd_759582 : Nat := 173346961112689940280779

theorem tailTrace_759582 : CollatzResearch.WordTrace tailWord_759582 prefixEnd_759582 173346961112689940280779 := by
  unfold tailWord_759582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3463028941771451890334125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18469487689447743415115333 3463028941771451890334125)
  ·
    refine ⟨1298635853164294458875297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3463028941771451890334125 1298635853164294458875297)
    ·
      refine ⟨973976889873220844156473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1298635853164294458875297 973976889873220844156473)
      ·
        refine ⟨730482667404915633117355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 973976889873220844156473 730482667404915633117355)
        ·
          refine ⟨1095724001107373449676033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730482667404915633117355 1095724001107373449676033)
          ·
            refine ⟨821793000830530087257025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1095724001107373449676033 821793000830530087257025)
            ·
              refine ⟨616344750622897565442769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821793000830530087257025 616344750622897565442769)
              ·
                refine ⟨462258562967173174082077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616344750622897565442769 462258562967173174082077)
                ·
                  refine ⟨173346961112689940280779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462258562967173174082077 173346961112689940280779)
                  ·
                    rfl

theorem cell21_759582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_759582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759582 prefixEnd_759582 := by exact prefixLift 759582
  have htrace : WordTrace (prefixWord ++ tailWord_759582) baseStart_759582 baseEnd_759582 := by
    simpa [prefixWord, tailWord_759582, baseEnd_759582] using wordTrace_append hprefix tailTrace_759582
  have hstable : (prefixWord ++ tailWord_759582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759582).length < 2 ^ (prefixWord ++ tailWord_759582).sum := by decide
  have hdescent : baseEnd_759582 < baseStart_759582 := by decide
  rcases family_descends (prefixWord ++ tailWord_759582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759587 : List Nat := [1, 1, 1, 4, 2, 1, 3, 4, 4]
def baseStart_759587 : Nat := 118140960795 + 759587 * 2 ^ 59
def prefixEnd_759587 : Nat := 4983230072969 + 3 ^ 40 * 759587 * 2
def baseEnd_759587 : Nat := 173348102180811042697435

theorem tailTrace_759587 : CollatzResearch.WordTrace tailWord_759587 prefixEnd_759587 173348102180811042697435 := by
  unfold tailWord_759587
  simp only [CollatzResearch.WordTrace]
  refine ⟨27704413899153500976605015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18469609266102333984403343 27704413899153500976605015)
  ·
    refine ⟨41556620848730251464907523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27704413899153500976605015 41556620848730251464907523)
    ·
      refine ⟨62334931273095377197361285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41556620848730251464907523 62334931273095377197361285)
      ·
        refine ⟨11687799613705383224505241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62334931273095377197361285 11687799613705383224505241)
        ·
          refine ⟨8765849710279037418378931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11687799613705383224505241 8765849710279037418378931)
          ·
            refine ⟨13148774565418556127568397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8765849710279037418378931 13148774565418556127568397)
            ·
              refine ⟨4930790462031958547838149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13148774565418556127568397 4930790462031958547838149)
              ·
                refine ⟨924523211630992227719653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4930790462031958547838149 924523211630992227719653)
                ·
                  refine ⟨173348102180811042697435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 924523211630992227719653 173348102180811042697435)
                  ·
                    rfl

theorem cell21_759587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 4].length) (baseStart_759587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759587 prefixEnd_759587 := by exact prefixLift 759587
  have htrace : WordTrace (prefixWord ++ tailWord_759587) baseStart_759587 baseEnd_759587 := by
    simpa [prefixWord, tailWord_759587, baseEnd_759587] using wordTrace_append hprefix tailTrace_759587
  have hstable : (prefixWord ++ tailWord_759587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759587).length < 2 ^ (prefixWord ++ tailWord_759587).sum := by decide
  have hdescent : baseEnd_759587 < baseStart_759587 := by decide
  rcases family_descends (prefixWord ++ tailWord_759587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759649 : List Nat := [1, 2, 3, 1, 1, 1, 3, 6, 3]
def baseStart_759649 : Nat := 118140960795 + 759649 * 2 ^ 59
def prefixEnd_759649 : Nat := 4983230072969 + 3 ^ 40 * 759649 * 2
def baseEnd_759649 : Nat := 173362251425512712663975

theorem tailTrace_759649 : CollatzResearch.WordTrace tailWord_759649 prefixEnd_759649 173362251425512712663975 := by
  unfold tailWord_759649
  simp only [CollatzResearch.WordTrace]
  refine ⟨27706675224928885565362001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18471116816619257043574667 27706675224928885565362001)
  ·
    refine ⟨20780006418696664174021501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27706675224928885565362001 20780006418696664174021501)
    ·
      refine ⟨7792502407011249065258063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20780006418696664174021501 7792502407011249065258063)
      ·
        refine ⟨11688753610516873597887095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7792502407011249065258063 11688753610516873597887095)
        ·
          refine ⟨17533130415775310396830643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11688753610516873597887095 17533130415775310396830643)
          ·
            refine ⟨26299695623662965595245965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17533130415775310396830643 26299695623662965595245965)
            ·
              refine ⟨9862385858873612098217237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26299695623662965595245965 9862385858873612098217237)
              ·
                refine ⟨462299337134700567103933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9862385858873612098217237 462299337134700567103933)
                ·
                  refine ⟨173362251425512712663975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462299337134700567103933 173362251425512712663975)
                  ·
                    rfl

theorem cell21_759649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 3].length) (baseStart_759649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759649 prefixEnd_759649 := by exact prefixLift 759649
  have htrace : WordTrace (prefixWord ++ tailWord_759649) baseStart_759649 baseEnd_759649 := by
    simpa [prefixWord, tailWord_759649, baseEnd_759649] using wordTrace_append hprefix tailTrace_759649
  have hstable : (prefixWord ++ tailWord_759649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759649).length < 2 ^ (prefixWord ++ tailWord_759649).sum := by decide
  have hdescent : baseEnd_759649 < baseStart_759649 := by decide
  rcases family_descends (prefixWord ++ tailWord_759649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759714 : List Nat := [3, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_759714 : Nat := 118140960795 + 759714 * 2 ^ 59
def prefixEnd_759714 : Nat := 4983230072969 + 3 ^ 40 * 759714 * 2
def baseEnd_759714 : Nat := 173377085311087044080509

theorem tailTrace_759714 : CollatzResearch.WordTrace tailWord_759714 prefixEnd_759714 173377085311087044080509 := by
  unfold tailWord_759714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6927261492423350416619549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18472697313128934444318797 6927261492423350416619549)
  ·
    refine ⟨2597723059658756406232331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6927261492423350416619549 2597723059658756406232331)
    ·
      refine ⟨3896584589488134609348497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2597723059658756406232331 3896584589488134609348497)
      ·
        refine ⟨2922438442116100957011373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3896584589488134609348497 2922438442116100957011373)
        ·
          refine ⟨1095914415793537858879265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2922438442116100957011373 1095914415793537858879265)
          ·
            refine ⟨821935811845153394159449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1095914415793537858879265 821935811845153394159449)
            ·
              refine ⟨616451858883865045619587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821935811845153394159449 616451858883865045619587)
              ·
                refine ⟨924677788325797568429381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616451858883865045619587 924677788325797568429381)
                ·
                  refine ⟨173377085311087044080509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 924677788325797568429381 173377085311087044080509)
                  ·
                    rfl

theorem cell21_759714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_759714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759714 prefixEnd_759714 := by exact prefixLift 759714
  have htrace : WordTrace (prefixWord ++ tailWord_759714) baseStart_759714 baseEnd_759714 := by
    simpa [prefixWord, tailWord_759714, baseEnd_759714] using wordTrace_append hprefix tailTrace_759714
  have hstable : (prefixWord ++ tailWord_759714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759714).length < 2 ^ (prefixWord ++ tailWord_759714).sum := by decide
  have hdescent : baseEnd_759714 < baseStart_759714 := by decide
  rcases family_descends (prefixWord ++ tailWord_759714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759756 : List Nat := [2, 2, 1, 4, 1, 3, 2, 2, 4]
def baseStart_759756 : Nat := 118140960795 + 759756 * 2 ^ 59
def prefixEnd_759756 : Nat := 4983230072969 + 3 ^ 40 * 759756 * 2
def baseEnd_759756 : Nat := 173386670283304304380423

theorem tailTrace_759756 : CollatzResearch.WordTrace tailWord_759756 prefixEnd_759756 173386670283304304380423 := by
  unfold tailWord_759756
  simp only [CollatzResearch.WordTrace]
  refine ⟨13855288917770621419753561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18473718557027495226338081 13855288917770621419753561)
  ·
    refine ⟨10391466688327966064815171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13855288917770621419753561 10391466688327966064815171)
    ·
      refine ⟨15587200032491949097222757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10391466688327966064815171 15587200032491949097222757)
      ·
        refine ⟨2922600006092240455729267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15587200032491949097222757 2922600006092240455729267)
        ·
          refine ⟨4383900009138360683593901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2922600006092240455729267 4383900009138360683593901)
          ·
            refine ⟨1643962503426885256347713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4383900009138360683593901 1643962503426885256347713)
            ·
              refine ⟨1232971877570163942260785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1643962503426885256347713 1232971877570163942260785)
              ·
                refine ⟨924728908177622956695589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1232971877570163942260785 924728908177622956695589)
                ·
                  refine ⟨173386670283304304380423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 924728908177622956695589 173386670283304304380423)
                  ·
                    rfl

theorem cell21_759756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_759756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759756 prefixEnd_759756 := by exact prefixLift 759756
  have htrace : WordTrace (prefixWord ++ tailWord_759756) baseStart_759756 baseEnd_759756 := by
    simpa [prefixWord, tailWord_759756, baseEnd_759756] using wordTrace_append hprefix tailTrace_759756
  have hstable : (prefixWord ++ tailWord_759756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759756).length < 2 ^ (prefixWord ++ tailWord_759756).sum := by decide
  have hdescent : baseEnd_759756 < baseStart_759756 := by decide
  rcases family_descends (prefixWord ++ tailWord_759756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759801 : List Nat := [1, 2, 1, 3, 1, 4, 1, 5, 3]
def baseStart_759801 : Nat := 118140960795 + 759801 * 2 ^ 59
def prefixEnd_759801 : Nat := 4983230072969 + 3 ^ 40 * 759801 * 2
def baseEnd_759801 : Nat := 173396939896394226130331

theorem tailTrace_759801 : CollatzResearch.WordTrace tailWord_759801 prefixEnd_759801 173396939896394226130331 := by
  unfold tailWord_759801
  simp only [CollatzResearch.WordTrace]
  refine ⟨27712219120378215524895257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18474812746918810349930171 27712219120378215524895257)
  ·
    refine ⟨20784164340283661643671443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27712219120378215524895257 20784164340283661643671443)
    ·
      refine ⟨31176246510425492465507165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20784164340283661643671443 31176246510425492465507165)
      ·
        refine ⟨11691092441409559674565187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31176246510425492465507165 11691092441409559674565187)
        ·
          refine ⟨17536638662114339511847781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11691092441409559674565187 17536638662114339511847781)
          ·
            refine ⟨3288119749146438658471459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17536638662114339511847781 3288119749146438658471459)
            ·
              refine ⟨4932179623719657987707189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288119749146438658471459 4932179623719657987707189)
              ·
                refine ⟨462391839723717936347549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4932179623719657987707189 462391839723717936347549)
                ·
                  refine ⟨173396939896394226130331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462391839723717936347549 173396939896394226130331)
                  ·
                    rfl

theorem cell21_759801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 3].length) (baseStart_759801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759801 prefixEnd_759801 := by exact prefixLift 759801
  have htrace : WordTrace (prefixWord ++ tailWord_759801) baseStart_759801 baseEnd_759801 := by
    simpa [prefixWord, tailWord_759801, baseEnd_759801] using wordTrace_append hprefix tailTrace_759801
  have hstable : (prefixWord ++ tailWord_759801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759801).length < 2 ^ (prefixWord ++ tailWord_759801).sum := by decide
  have hdescent : baseEnd_759801 < baseStart_759801 := by decide
  rcases family_descends (prefixWord ++ tailWord_759801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759815 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 6]
def baseStart_759815 : Nat := 118140960795 + 759815 * 2 ^ 59
def prefixEnd_759815 : Nat := 4983230072969 + 3 ^ 40 * 759815 * 2
def baseEnd_759815 : Nat := 173400134887133312896969

theorem tailTrace_759815 : CollatzResearch.WordTrace tailWord_759815 prefixEnd_759815 173400134887133312896969 := by
  unfold tailWord_759815
  simp only [CollatzResearch.WordTrace]
  refine ⟨27712729742327495915904899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18475153161551663943936599 27712729742327495915904899)
  ·
    refine ⟨41569094613491243873857349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27712729742327495915904899 41569094613491243873857349)
    ·
      refine ⟨7794205240029608226348253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41569094613491243873857349 7794205240029608226348253)
      ·
        refine ⟨2922826965011103084880595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7794205240029608226348253 2922826965011103084880595)
        ·
          refine ⟨4384240447516654627320893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2922826965011103084880595 4384240447516654627320893)
          ·
            refine ⟨1644090167818745485245335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4384240447516654627320893 1644090167818745485245335)
            ·
              refine ⟨2466135251728118227868003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644090167818745485245335 2466135251728118227868003)
              ·
                refine ⟨3699202877592177341802005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466135251728118227868003 3699202877592177341802005)
                ·
                  refine ⟨173400134887133312896969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3699202877592177341802005 173400134887133312896969)
                  ·
                    rfl

theorem cell21_759815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 6].length) (baseStart_759815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759815 prefixEnd_759815 := by exact prefixLift 759815
  have htrace : WordTrace (prefixWord ++ tailWord_759815) baseStart_759815 baseEnd_759815 := by
    simpa [prefixWord, tailWord_759815, baseEnd_759815] using wordTrace_append hprefix tailTrace_759815
  have hstable : (prefixWord ++ tailWord_759815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759815).length < 2 ^ (prefixWord ++ tailWord_759815).sum := by decide
  have hdescent : baseEnd_759815 < baseStart_759815 := by decide
  rcases family_descends (prefixWord ++ tailWord_759815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759832 : List Nat := [2, 1, 2, 3, 2, 1, 5, 1, 4]
def baseStart_759832 : Nat := 118140960795 + 759832 * 2 ^ 59
def prefixEnd_759832 : Nat := 4983230072969 + 3 ^ 40 * 759832 * 2
def baseEnd_759832 : Nat := 173404014518745061113601

theorem tailTrace_759832 : CollatzResearch.WordTrace tailWord_759832 prefixEnd_759832 173404014518745061113601 := by
  unfold tailWord_759832
  simp only [CollatzResearch.WordTrace]
  refine ⟨13856674891632953909636875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18475566522177271879515833 13856674891632953909636875)
  ·
    refine ⟨20785012337449430864455313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13856674891632953909636875 20785012337449430864455313)
    ·
      refine ⟨15588759253087073148341485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20785012337449430864455313 15588759253087073148341485)
      ·
        refine ⟨5845784719907652430628057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15588759253087073148341485 5845784719907652430628057)
        ·
          refine ⟨4384338539930739322971043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5845784719907652430628057 4384338539930739322971043)
          ·
            refine ⟨6576507809896108984456565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384338539930739322971043 6576507809896108984456565)
            ·
              refine ⟨616547607177760217292803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6576507809896108984456565 616547607177760217292803)
              ·
                refine ⟨924821410766640325939205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616547607177760217292803 924821410766640325939205)
                ·
                  refine ⟨173404014518745061113601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 924821410766640325939205 173404014518745061113601)
                  ·
                    rfl

theorem cell21_759832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_759832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759832 prefixEnd_759832 := by exact prefixLift 759832
  have htrace : WordTrace (prefixWord ++ tailWord_759832) baseStart_759832 baseEnd_759832 := by
    simpa [prefixWord, tailWord_759832, baseEnd_759832] using wordTrace_append hprefix tailTrace_759832
  have hstable : (prefixWord ++ tailWord_759832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759832).length < 2 ^ (prefixWord ++ tailWord_759832).sum := by decide
  have hdescent : baseEnd_759832 < baseStart_759832 := by decide
  rcases family_descends (prefixWord ++ tailWord_759832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759956 : List Nat := [2, 4, 2, 3, 1, 1, 3, 5]
def baseStart_759956 : Nat := 118140960795 + 759956 * 2 ^ 59
def prefixEnd_759956 : Nat := 4983230072969 + 3 ^ 40 * 759956 * 2
def baseEnd_759956 : Nat := 57810771002716133682227

theorem tailTrace_759956 : CollatzResearch.WordTrace tailWord_759956 prefixEnd_759956 57810771002716133682227 := by
  unfold tailWord_759956
  simp only [CollatzResearch.WordTrace]
  refine ⟨13858936217408338498393861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18478581623211117997858481 13858936217408338498393861)
  ·
    refine ⟨2598550540764063468448849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13858936217408338498393861 2598550540764063468448849)
    ·
      refine ⟨1948912905573047601336637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2598550540764063468448849 1948912905573047601336637)
      ·
        refine ⟨730842339589892850501239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1948912905573047601336637 730842339589892850501239)
        ·
          refine ⟨1096263509384839275751859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730842339589892850501239 1096263509384839275751859)
          ·
            refine ⟨1644395264077258913627789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096263509384839275751859 1644395264077258913627789)
            ·
              refine ⟨616648224028972092610421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1644395264077258913627789 616648224028972092610421)
              ·
                refine ⟨57810771002716133682227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 616648224028972092610421 57810771002716133682227)
                ·
                  rfl

theorem cell21_759956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 5].length) (baseStart_759956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759956 prefixEnd_759956 := by exact prefixLift 759956
  have htrace : WordTrace (prefixWord ++ tailWord_759956) baseStart_759956 baseEnd_759956 := by
    simpa [prefixWord, tailWord_759956, baseEnd_759956] using wordTrace_append hprefix tailTrace_759956
  have hstable : (prefixWord ++ tailWord_759956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759956).length < 2 ^ (prefixWord ++ tailWord_759956).sum := by decide
  have hdescent : baseEnd_759956 < baseStart_759956 := by decide
  rcases family_descends (prefixWord ++ tailWord_759956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759970 : List Nat := [3, 3, 1, 3, 1, 1, 1, 5, 3]
def baseStart_759970 : Nat := 118140960795 + 759970 * 2 ^ 59
def prefixEnd_759970 : Nat := 4983230072969 + 3 ^ 40 * 759970 * 2
def baseEnd_759970 : Nat := 173435507998887487813319

theorem tailTrace_759970 : CollatzResearch.WordTrace tailWord_759970 prefixEnd_759970 173435507998887487813319 := by
  unfold tailWord_759970
  simp only [CollatzResearch.WordTrace]
  refine ⟨6929595764191489346949341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18478922037843971591864909 6929595764191489346949341)
  ·
    refine ⟨2598598411571808505106003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6929595764191489346949341 2598598411571808505106003)
    ·
      refine ⟨3897897617357712757659005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2598598411571808505106003 3897897617357712757659005)
      ·
        refine ⟨1461711606509142284122127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3897897617357712757659005 1461711606509142284122127)
        ·
          refine ⟨2192567409763713426183191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1461711606509142284122127 2192567409763713426183191)
          ·
            refine ⟨3288851114645570139274787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192567409763713426183191 3288851114645570139274787)
            ·
              refine ⟨4933276671968355208912181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288851114645570139274787 4933276671968355208912181)
              ·
                refine ⟨462494687997033300835517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4933276671968355208912181 462494687997033300835517)
                ·
                  refine ⟨173435507998887487813319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462494687997033300835517 173435507998887487813319)
                  ·
                    rfl

theorem cell21_759970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_759970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_759970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_759970 prefixEnd_759970 := by exact prefixLift 759970
  have htrace : WordTrace (prefixWord ++ tailWord_759970) baseStart_759970 baseEnd_759970 := by
    simpa [prefixWord, tailWord_759970, baseEnd_759970] using wordTrace_append hprefix tailTrace_759970
  have hstable : (prefixWord ++ tailWord_759970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759970).length < 2 ^ (prefixWord ++ tailWord_759970).sum := by decide
  have hdescent : baseEnd_759970 < baseStart_759970 := by decide
  rcases family_descends (prefixWord ++ tailWord_759970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760026 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_760026 : Nat := 118140960795 + 760026 * 2 ^ 59
def prefixEnd_760026 : Nat := 4983230072969 + 3 ^ 40 * 760026 * 2
def baseEnd_760026 : Nat := 173448287961843834879871

theorem tailTrace_760026 : CollatzResearch.WordTrace tailWord_760026 prefixEnd_760026 173448287961843834879871 := by
  unfold tailWord_760026
  simp only [CollatzResearch.WordTrace]
  refine ⟨6930106386140769737958983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18480283696375385967890621 6930106386140769737958983)
  ·
    refine ⟨10395159579211154606938475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6930106386140769737958983 10395159579211154606938475)
    ·
      refine ⟨15592739368816731910407713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10395159579211154606938475 15592739368816731910407713)
      ·
        refine ⟨11694554526612548932805785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15592739368816731910407713 11694554526612548932805785)
        ·
          refine ⟨8770915894959411699604339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11694554526612548932805785 8770915894959411699604339)
          ·
            refine ⟨13156373842439117549406509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8770915894959411699604339 13156373842439117549406509)
            ·
              refine ⟨4933640190914669081027441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13156373842439117549406509 4933640190914669081027441)
              ·
                refine ⟨3700230143186001810770581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4933640190914669081027441 3700230143186001810770581)
                ·
                  refine ⟨173448287961843834879871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3700230143186001810770581 173448287961843834879871)
                  ·
                    rfl

theorem cell21_760026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_760026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760026 prefixEnd_760026 := by exact prefixLift 760026
  have htrace : WordTrace (prefixWord ++ tailWord_760026) baseStart_760026 baseEnd_760026 := by
    simpa [prefixWord, tailWord_760026, baseEnd_760026] using wordTrace_append hprefix tailTrace_760026
  have hstable : (prefixWord ++ tailWord_760026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760026).length < 2 ^ (prefixWord ++ tailWord_760026).sum := by decide
  have hdescent : baseEnd_760026 < baseStart_760026 := by decide
  rcases family_descends (prefixWord ++ tailWord_760026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760060 : List Nat := [2, 2, 2, 1, 4, 1, 4, 1, 4]
def baseStart_760060 : Nat := 118140960795 + 760060 * 2 ^ 59
def prefixEnd_760060 : Nat := 4983230072969 + 3 ^ 40 * 760060 * 2
def baseEnd_760060 : Nat := 173456047225067331313135

theorem tailTrace_760060 : CollatzResearch.WordTrace tailWord_760060 prefixEnd_760060 173456047225067331313135 := by
  unfold tailWord_760060
  simp only [CollatzResearch.WordTrace]
  refine ⟨13860832813219951379286817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18481110417626601839049089 13860832813219951379286817)
  ·
    refine ⟨10395624609914963534465113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13860832813219951379286817 10395624609914963534465113)
    ·
      refine ⟨7796718457436222650848835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10395624609914963534465113 7796718457436222650848835)
      ·
        refine ⟨11695077686154333976273253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7796718457436222650848835 11695077686154333976273253)
        ·
          refine ⟨2192827066153937620551235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11695077686154333976273253 2192827066153937620551235)
          ·
            refine ⟨3289240599230906430826853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192827066153937620551235 3289240599230906430826853)
            ·
              refine ⟨616732612355794955780035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3289240599230906430826853 616732612355794955780035)
              ·
                refine ⟨925098918533692433670053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616732612355794955780035 925098918533692433670053)
                ·
                  refine ⟨173456047225067331313135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 925098918533692433670053 173456047225067331313135)
                  ·
                    rfl

theorem cell21_760060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_760060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760060 prefixEnd_760060 := by exact prefixLift 760060
  have htrace : WordTrace (prefixWord ++ tailWord_760060) baseStart_760060 baseEnd_760060 := by
    simpa [prefixWord, tailWord_760060, baseEnd_760060] using wordTrace_append hprefix tailTrace_760060
  have hstable : (prefixWord ++ tailWord_760060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760060).length < 2 ^ (prefixWord ++ tailWord_760060).sum := by decide
  have hdescent : baseEnd_760060 < baseStart_760060 := by decide
  rcases family_descends (prefixWord ++ tailWord_760060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760164 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 5]
def baseStart_760164 : Nat := 118140960795 + 760164 * 2 ^ 59
def prefixEnd_760164 : Nat := 4983230072969 + 3 ^ 40 * 760164 * 2
def baseEnd_760164 : Nat := 173479781441986261579589

theorem tailTrace_760164 : CollatzResearch.WordTrace tailWord_760164 prefixEnd_760164 173479781441986261579589 := by
  unfold tailWord_760164
  simp only [CollatzResearch.WordTrace]
  refine ⟨13862729409031564260179773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18483639212042085680239697 13862729409031564260179773)
  ·
    refine ⟨5198523528386836597567415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13862729409031564260179773 5198523528386836597567415)
    ·
      refine ⟨7797785292580254896351123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5198523528386836597567415 7797785292580254896351123)
      ·
        refine ⟨11696677938870382344526685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7797785292580254896351123 11696677938870382344526685)
        ·
          refine ⟨4386254227076393379197507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11696677938870382344526685 4386254227076393379197507)
          ·
            refine ⟨6579381340614590068796261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4386254227076393379197507 6579381340614590068796261)
            ·
              refine ⟨1233634001365235637899299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6579381340614590068796261 1233634001365235637899299)
              ·
                refine ⟨1850451002047853456848949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233634001365235637899299 1850451002047853456848949)
                ·
                  refine ⟨173479781441986261579589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1850451002047853456848949 173479781441986261579589)
                  ·
                    rfl

theorem cell21_760164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_760164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760164 prefixEnd_760164 := by exact prefixLift 760164
  have htrace : WordTrace (prefixWord ++ tailWord_760164) baseStart_760164 baseEnd_760164 := by
    simpa [prefixWord, tailWord_760164, baseEnd_760164] using wordTrace_append hprefix tailTrace_760164
  have hstable : (prefixWord ++ tailWord_760164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760164).length < 2 ^ (prefixWord ++ tailWord_760164).sum := by decide
  have hdescent : baseEnd_760164 < baseStart_760164 := by decide
  rcases family_descends (prefixWord ++ tailWord_760164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760254 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_760254 : Nat := 118140960795 + 760254 * 2 ^ 59
def prefixEnd_760254 : Nat := 4983230072969 + 3 ^ 40 * 760254 * 2
def baseEnd_760254 : Nat := 173500320668166105079405

theorem tailTrace_760254 : CollatzResearch.WordTrace tailWord_760254 prefixEnd_760254 173500320668166105079405 := by
  unfold tailWord_760254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3466092673467134236391977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18485827591824715927423877 3466092673467134236391977)
  ·
    refine ⟨2599569505100350677293983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3466092673467134236391977 2599569505100350677293983)
    ·
      refine ⟨3899354257650526015940975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2599569505100350677293983 3899354257650526015940975)
      ·
        refine ⟨5849031386475789023911463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3899354257650526015940975 5849031386475789023911463)
        ·
          refine ⟨8773547079713683535867195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5849031386475789023911463 8773547079713683535867195)
          ·
            refine ⟨13160320619570525303800793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8773547079713683535867195 13160320619570525303800793)
            ·
              refine ⟨9870240464677893977850595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13160320619570525303800793 9870240464677893977850595)
              ·
                refine ⟨14805360697016840966775893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9870240464677893977850595 14805360697016840966775893)
                ·
                  refine ⟨173500320668166105079405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14805360697016840966775893 173500320668166105079405)
                  ·
                    rfl

theorem cell21_760254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_760254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760254 prefixEnd_760254 := by exact prefixLift 760254
  have htrace : WordTrace (prefixWord ++ tailWord_760254) baseStart_760254 baseEnd_760254 := by
    simpa [prefixWord, tailWord_760254, baseEnd_760254] using wordTrace_append hprefix tailTrace_760254
  have hstable : (prefixWord ++ tailWord_760254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760254).length < 2 ^ (prefixWord ++ tailWord_760254).sum := by decide
  have hdescent : baseEnd_760254 < baseStart_760254 := by decide
  rcases family_descends (prefixWord ++ tailWord_760254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760268 : List Nat := [2, 2, 1, 4, 12]
def baseStart_760268 : Nat := 118140960795 + 760268 * 2 ^ 59
def prefixEnd_760268 : Nat := 4983230072969 + 3 ^ 40 * 760268 * 2
def baseEnd_760268 : Nat := 2142018711838335701803

theorem tailTrace_760268 : CollatzResearch.WordTrace tailWord_760268 prefixEnd_760268 2142018711838335701803 := by
  unfold tailWord_760268
  simp only [CollatzResearch.WordTrace]
  refine ⟨13864626004843177141072729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18486168006457569521430305 13864626004843177141072729)
  ·
    refine ⟨10398469503632382855804547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13864626004843177141072729 10398469503632382855804547)
    ·
      refine ⟨15597704255448574283706821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10398469503632382855804547 15597704255448574283706821)
      ·
        refine ⟨2924569547896607678195029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15597704255448574283706821 2924569547896607678195029)
        ·
          refine ⟨2142018711838335701803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2924569547896607678195029 2142018711838335701803)
          ·
            rfl

theorem cell21_760268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 12].length) (baseStart_760268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760268 prefixEnd_760268 := by exact prefixLift 760268
  have htrace : WordTrace (prefixWord ++ tailWord_760268) baseStart_760268 baseEnd_760268 := by
    simpa [prefixWord, tailWord_760268, baseEnd_760268] using wordTrace_append hprefix tailTrace_760268
  have hstable : (prefixWord ++ tailWord_760268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760268).length < 2 ^ (prefixWord ++ tailWord_760268).sum := by decide
  have hdescent : baseEnd_760268 < baseStart_760268 := by decide
  rcases family_descends (prefixWord ++ tailWord_760268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760299 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 5]
def baseStart_760299 : Nat := 118140960795 + 760299 * 2 ^ 59
def prefixEnd_760299 : Nat := 4983230072969 + 3 ^ 40 * 760299 * 2
def baseEnd_760299 : Nat := 173510590281256026829313

theorem tailTrace_760299 : CollatzResearch.WordTrace tailWord_760299 prefixEnd_760299 173510590281256026829313 := by
  unfold tailWord_760299
  simp only [CollatzResearch.WordTrace]
  refine ⟨27730382672574046576523951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18486921781716031051015967 27730382672574046576523951)
  ·
    refine ⟨41595574008861069864785927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27730382672574046576523951 41595574008861069864785927)
    ·
      refine ⟨62393361013291604797178891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41595574008861069864785927 62393361013291604797178891)
      ·
        refine ⟨93590041519937407195768337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62393361013291604797178891 93590041519937407195768337)
        ·
          refine ⟨70192531139953055396826253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93590041519937407195768337 70192531139953055396826253)
          ·
            refine ⟨26322199177482395773809845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70192531139953055396826253 26322199177482395773809845)
            ·
              refine ⟨2467706172888974603794673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26322199177482395773809845 2467706172888974603794673)
              ·
                refine ⟨1850779629666730952846005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2467706172888974603794673 1850779629666730952846005)
                ·
                  refine ⟨173510590281256026829313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1850779629666730952846005 173510590281256026829313)
                  ·
                    rfl

theorem cell21_760299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 5].length) (baseStart_760299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760299 prefixEnd_760299 := by exact prefixLift 760299
  have htrace : WordTrace (prefixWord ++ tailWord_760299) baseStart_760299 baseEnd_760299 := by
    simpa [prefixWord, tailWord_760299, baseEnd_760299] using wordTrace_append hprefix tailTrace_760299
  have hstable : (prefixWord ++ tailWord_760299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760299).length < 2 ^ (prefixWord ++ tailWord_760299).sum := by decide
  have hdescent : baseEnd_760299 < baseStart_760299 := by decide
  rcases family_descends (prefixWord ++ tailWord_760299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760302 : List Nat := [4, 1, 2, 1, 2, 3, 3, 5]
def baseStart_760302 : Nat := 118140960795 + 760302 * 2 ^ 59
def prefixEnd_760302 : Nat := 4983230072969 + 3 ^ 40 * 760302 * 2
def baseEnd_760302 : Nat := 57837091640709562759769

theorem tailTrace_760302 : CollatzResearch.WordTrace tailWord_760302 prefixEnd_760302 57837091640709562759769 := by
  unfold tailWord_760302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3466311511445397261110395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18486994727708785392588773 3466311511445397261110395)
  ·
    refine ⟨5199467267168095891665593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3466311511445397261110395 5199467267168095891665593)
    ·
      refine ⟨3899600450376071918749195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5199467267168095891665593 3899600450376071918749195)
      ·
        refine ⟨5849400675564107878123793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3899600450376071918749195 5849400675564107878123793)
        ·
          refine ⟨4387050506673080908592845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5849400675564107878123793 4387050506673080908592845)
          ·
            refine ⟨1645143940002405340722317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4387050506673080908592845 1645143940002405340722317)
            ·
              refine ⟨616928977500902002770869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1645143940002405340722317 616928977500902002770869)
              ·
                refine ⟨57837091640709562759769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 616928977500902002770869 57837091640709562759769)
                ·
                  rfl

theorem cell21_760302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_760302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760302 prefixEnd_760302 := by exact prefixLift 760302
  have htrace : WordTrace (prefixWord ++ tailWord_760302) baseStart_760302 baseEnd_760302 := by
    simpa [prefixWord, tailWord_760302, baseEnd_760302] using wordTrace_append hprefix tailTrace_760302
  have hstable : (prefixWord ++ tailWord_760302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760302).length < 2 ^ (prefixWord ++ tailWord_760302).sum := by decide
  have hdescent : baseEnd_760302 < baseStart_760302 := by decide
  rcases family_descends (prefixWord ++ tailWord_760302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760322 : List Nat := [3, 4, 1, 2, 3, 1, 1, 2, 4]
def baseStart_760322 : Nat := 118140960795 + 760322 * 2 ^ 59
def prefixEnd_760322 : Nat := 4983230072969 + 3 ^ 40 * 760322 * 2
def baseEnd_760322 : Nat := 173515839194613097945933

theorem tailTrace_760322 : CollatzResearch.WordTrace tailWord_760322 prefixEnd_760322 173515839194613097945933 := by
  unfold tailWord_760322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6932805387872680376152805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18487481034327147669740813 6932805387872680376152805)
  ·
    refine ⟨1299901010226127570528651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6932805387872680376152805 1299901010226127570528651)
    ·
      refine ⟨1949851515339191355792977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299901010226127570528651 1949851515339191355792977)
      ·
        refine ⟨1462388636504393516844733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1949851515339191355792977 1462388636504393516844733)
        ·
          refine ⟨548395738689147568816775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1462388636504393516844733 548395738689147568816775)
          ·
            refine ⟨822593608033721353225163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548395738689147568816775 822593608033721353225163)
            ·
              refine ⟨1233890412050582029837745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822593608033721353225163 1233890412050582029837745)
              ·
                refine ⟨925417809037936522378309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1233890412050582029837745 925417809037936522378309)
                ·
                  refine ⟨173515839194613097945933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 925417809037936522378309 173515839194613097945933)
                  ·
                    rfl

theorem cell21_760322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_760322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760322 prefixEnd_760322 := by exact prefixLift 760322
  have htrace : WordTrace (prefixWord ++ tailWord_760322) baseStart_760322 baseEnd_760322 := by
    simpa [prefixWord, tailWord_760322, baseEnd_760322] using wordTrace_append hprefix tailTrace_760322
  have hstable : (prefixWord ++ tailWord_760322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760322).length < 2 ^ (prefixWord ++ tailWord_760322).sum := by decide
  have hdescent : baseEnd_760322 < baseStart_760322 := by decide
  rcases family_descends (prefixWord ++ tailWord_760322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760330 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_760330 : Nat := 118140960795 + 760330 * 2 ^ 59
def prefixEnd_760330 : Nat := 4983230072969 + 3 ^ 40 * 760330 * 2
def baseEnd_760330 : Nat := 173517664903606861812583

theorem tailTrace_760330 : CollatzResearch.WordTrace tailWord_760330 prefixEnd_760330 173517664903606861812583 := by
  unfold tailWord_760330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6932878333865434717725611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18487675556974492580601629 6932878333865434717725611)
  ·
    refine ⟨10399317500798152076588417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6932878333865434717725611 10399317500798152076588417)
    ·
      refine ⟨7799488125598614057441313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10399317500798152076588417 7799488125598614057441313)
      ·
        refine ⟨5849616094198960543080985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7799488125598614057441313 5849616094198960543080985)
        ·
          refine ⟨4387212070649220407310739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5849616094198960543080985 4387212070649220407310739)
          ·
            refine ⟨6580818105973830610966109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4387212070649220407310739 6580818105973830610966109)
            ·
              refine ⟨2467806789740186479112291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6580818105973830610966109 2467806789740186479112291)
              ·
                refine ⟨3701710184610279718668437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2467806789740186479112291 3701710184610279718668437)
                ·
                  refine ⟨173517664903606861812583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3701710184610279718668437 173517664903606861812583)
                  ·
                    rfl

theorem cell21_760330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_760330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760330 prefixEnd_760330 := by exact prefixLift 760330
  have htrace : WordTrace (prefixWord ++ tailWord_760330) baseStart_760330 baseEnd_760330 := by
    simpa [prefixWord, tailWord_760330, baseEnd_760330] using wordTrace_append hprefix tailTrace_760330
  have hstable : (prefixWord ++ tailWord_760330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760330).length < 2 ^ (prefixWord ++ tailWord_760330).sum := by decide
  have hdescent : baseEnd_760330 < baseStart_760330 := by decide
  rcases family_descends (prefixWord ++ tailWord_760330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760392 : List Nat := [2, 1, 3, 1, 1, 1, 1, 8, 3]
def baseStart_760392 : Nat := 118140960795 + 760392 * 2 ^ 59
def prefixEnd_760392 : Nat := 4983230072969 + 3 ^ 40 * 760392 * 2
def baseEnd_760392 : Nat := 173531814148308531779123

theorem tailTrace_760392 : CollatzResearch.WordTrace tailWord_760392 prefixEnd_760392 173531814148308531779123 := by
  unfold tailWord_760392
  simp only [CollatzResearch.WordTrace]
  refine ⟨13866887330618561729829715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18489183107491415639772953 13866887330618561729829715)
  ·
    refine ⟨20800330995927842594744573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13866887330618561729829715 20800330995927842594744573)
    ·
      refine ⟨7800124123472940973029215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20800330995927842594744573 7800124123472940973029215)
      ·
        refine ⟨11700186185209411459543823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7800124123472940973029215 11700186185209411459543823)
        ·
          refine ⟨17550279277814117189315735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11700186185209411459543823 17550279277814117189315735)
          ·
            refine ⟨26325418916721175783973603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17550279277814117189315735 26325418916721175783973603)
            ·
              refine ⟨39488128375081763675960405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26325418916721175783973603 39488128375081763675960405)
              ·
                refine ⟨462751504395489418077661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 39488128375081763675960405 462751504395489418077661)
                ·
                  refine ⟨173531814148308531779123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462751504395489418077661 173531814148308531779123)
                  ·
                    rfl

theorem cell21_760392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 3].length) (baseStart_760392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760392 prefixEnd_760392 := by exact prefixLift 760392
  have htrace : WordTrace (prefixWord ++ tailWord_760392) baseStart_760392 baseEnd_760392 := by
    simpa [prefixWord, tailWord_760392, baseEnd_760392] using wordTrace_append hprefix tailTrace_760392
  have hstable : (prefixWord ++ tailWord_760392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760392).length < 2 ^ (prefixWord ++ tailWord_760392).sum := by decide
  have hdescent : baseEnd_760392 < baseStart_760392 := by decide
  rcases family_descends (prefixWord ++ tailWord_760392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760420 : List Nat := [2, 3, 1, 1, 2, 2, 1, 9]
def baseStart_760420 : Nat := 118140960795 + 760420 * 2 ^ 59
def prefixEnd_760420 : Nat := 4983230072969 + 3 ^ 40 * 760420 * 2
def baseEnd_760420 : Nat := 57846068043262235104133

theorem tailTrace_760420 : CollatzResearch.WordTrace tailWord_760420 prefixEnd_760420 57846068043262235104133 := by
  unfold tailWord_760420
  simp only [CollatzResearch.WordTrace]
  refine ⟨13867397952567842120839357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18489863936757122827785809 13867397952567842120839357)
  ·
    refine ⟨5200274232212940795314759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13867397952567842120839357 5200274232212940795314759)
    ·
      refine ⟨7800411348319411192972139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5200274232212940795314759 7800411348319411192972139)
      ·
        refine ⟨11700617022479116789458209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7800411348319411192972139 11700617022479116789458209)
        ·
          refine ⟨8775462766859337592093657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11700617022479116789458209 8775462766859337592093657)
          ·
            refine ⟨6581597075144503194070243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8775462766859337592093657 6581597075144503194070243)
            ·
              refine ⟨9872395612716754791105365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6581597075144503194070243 9872395612716754791105365)
              ·
                refine ⟨57846068043262235104133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9872395612716754791105365 57846068043262235104133)
                ·
                  rfl

theorem cell21_760420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_760420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760420 prefixEnd_760420 := by exact prefixLift 760420
  have htrace : WordTrace (prefixWord ++ tailWord_760420) baseStart_760420 baseEnd_760420 := by
    simpa [prefixWord, tailWord_760420, baseEnd_760420] using wordTrace_append hprefix tailTrace_760420
  have hstable : (prefixWord ++ tailWord_760420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760420).length < 2 ^ (prefixWord ++ tailWord_760420).sum := by decide
  have hdescent : baseEnd_760420 < baseStart_760420 := by decide
  rcases family_descends (prefixWord ++ tailWord_760420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760437 : List Nat := [1, 3, 4, 2, 2, 9]
def baseStart_760437 : Nat := 118140960795 + 760437 * 2 ^ 59
def prefixEnd_760437 : Nat := 4983230072969 + 3 ^ 40 * 760437 * 2
def baseEnd_760437 : Nat := 6427484583755498278853

theorem tailTrace_760437 : CollatzResearch.WordTrace tailWord_760437 prefixEnd_760437 6427484583755498278853 := by
  unfold tailWord_760437
  simp only [CollatzResearch.WordTrace]
  refine ⟨27735415946074096145047565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18490277297382730763365043 27735415946074096145047565)
  ·
    refine ⟨10400780979777786054392837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27735415946074096145047565 10400780979777786054392837)
    ·
      refine ⟨1950146433708334885198657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10400780979777786054392837 1950146433708334885198657)
      ·
        refine ⟨1462609825281251163898993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1950146433708334885198657 1462609825281251163898993)
        ·
          refine ⟨1096957368960938372924245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1462609825281251163898993 1096957368960938372924245)
          ·
            refine ⟨6427484583755498278853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1096957368960938372924245 6427484583755498278853)
            ·
              rfl

theorem cell21_760437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 9].length) (baseStart_760437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760437 prefixEnd_760437 := by exact prefixLift 760437
  have htrace : WordTrace (prefixWord ++ tailWord_760437) baseStart_760437 baseEnd_760437 := by
    simpa [prefixWord, tailWord_760437, baseEnd_760437] using wordTrace_append hprefix tailTrace_760437
  have hstable : (prefixWord ++ tailWord_760437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760437).length < 2 ^ (prefixWord ++ tailWord_760437).sum := by decide
  have hdescent : baseEnd_760437 < baseStart_760437 := by decide
  rcases family_descends (prefixWord ++ tailWord_760437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760468 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 7]
def baseStart_760468 : Nat := 118140960795 + 760468 * 2 ^ 59
def prefixEnd_760468 : Nat := 4983230072969 + 3 ^ 40 * 760468 * 2
def baseEnd_760468 : Nat := 173549158383749288512301

theorem tailTrace_760468 : CollatzResearch.WordTrace tailWord_760468 prefixEnd_760468 173549158383749288512301 := by
  unfold tailWord_760468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13868273304480894219713029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18491031072641192292950705 13868273304480894219713029)
  ·
    refine ⟨2600301244590167666196193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13868273304480894219713029 2600301244590167666196193)
    ·
      refine ⟨1950225933442625749647145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2600301244590167666196193 1950225933442625749647145)
      ·
        refine ⟨1462669450081969312235359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1950225933442625749647145 1462669450081969312235359)
        ·
          refine ⟨2194004175122953968353039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1462669450081969312235359 2194004175122953968353039)
          ·
            refine ⟨3291006262684430952529559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194004175122953968353039 3291006262684430952529559)
            ·
              refine ⟨4936509394026646428794339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3291006262684430952529559 4936509394026646428794339)
              ·
                refine ⟨7404764091039969643191509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936509394026646428794339 7404764091039969643191509)
                ·
                  refine ⟨173549158383749288512301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7404764091039969643191509 173549158383749288512301)
                  ·
                    rfl

theorem cell21_760468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_760468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760468 prefixEnd_760468 := by exact prefixLift 760468
  have htrace : WordTrace (prefixWord ++ tailWord_760468) baseStart_760468 baseEnd_760468 := by
    simpa [prefixWord, tailWord_760468, baseEnd_760468] using wordTrace_append hprefix tailTrace_760468
  have hstable : (prefixWord ++ tailWord_760468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760468).length < 2 ^ (prefixWord ++ tailWord_760468).sum := by decide
  have hdescent : baseEnd_760468 < baseStart_760468 := by decide
  rcases family_descends (prefixWord ++ tailWord_760468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760499 : List Nat := [1, 1, 1, 2, 3, 6, 1, 2, 4]
def baseStart_760499 : Nat := 118140960795 + 760499 * 2 ^ 59
def prefixEnd_760499 : Nat := 4983230072969 + 3 ^ 40 * 760499 * 2
def baseEnd_760499 : Nat := 173556233006100123495571

theorem tailTrace_760499 : CollatzResearch.WordTrace tailWord_760499 prefixEnd_760499 173556233006100123495571 := by
  unfold tailWord_760499
  simp only [CollatzResearch.WordTrace]
  refine ⟨27737677271849480733804551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18491784847899653822536367 27737677271849480733804551)
  ·
    refine ⟨41606515907774221100706827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27737677271849480733804551 41606515907774221100706827)
    ·
      refine ⟨62409773861661331651060241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41606515907774221100706827 62409773861661331651060241)
      ·
        refine ⟨46807330396245998738295181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62409773861661331651060241 46807330396245998738295181)
        ·
          refine ⟨17552748898592249526860693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46807330396245998738295181 17552748898592249526860693)
          ·
            refine ⟨822785104621511696571595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17552748898592249526860693 822785104621511696571595)
            ·
              refine ⟨1234177656932267544857393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822785104621511696571595 1234177656932267544857393)
              ·
                refine ⟨925633242699200658643045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234177656932267544857393 925633242699200658643045)
                ·
                  refine ⟨173556233006100123495571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 925633242699200658643045 173556233006100123495571)
                  ·
                    rfl

theorem cell21_760499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 4].length) (baseStart_760499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760499 prefixEnd_760499 := by exact prefixLift 760499
  have htrace : WordTrace (prefixWord ++ tailWord_760499) baseStart_760499 baseEnd_760499 := by
    simpa [prefixWord, tailWord_760499, baseEnd_760499] using wordTrace_append hprefix tailTrace_760499
  have hstable : (prefixWord ++ tailWord_760499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760499).length < 2 ^ (prefixWord ++ tailWord_760499).sum := by decide
  have hdescent : baseEnd_760499 < baseStart_760499 := by decide
  rcases family_descends (prefixWord ++ tailWord_760499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760502 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_760502 : Nat := 118140960795 + 760502 * 2 ^ 59
def prefixEnd_760502 : Nat := 4983230072969 + 3 ^ 40 * 760502 * 2
def baseEnd_760502 : Nat := 173556917646972784945565

theorem tailTrace_760502 : CollatzResearch.WordTrace tailWord_760502 prefixEnd_760502 173556917646972784945565 := by
  unfold tailWord_760502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733611668177413265385235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18491857793892408164109173 1733611668177413265385235)
  ·
    refine ⟨2600417502266119898077853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1733611668177413265385235 2600417502266119898077853)
    ·
      refine ⟨975156563349794961779195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2600417502266119898077853 975156563349794961779195)
      ·
        refine ⟨1462734845024692442668793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 975156563349794961779195 1462734845024692442668793)
        ·
          refine ⟨1097051133768519332001595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1462734845024692442668793 1097051133768519332001595)
          ·
            refine ⟨1645576700652778998002393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097051133768519332001595 1645576700652778998002393)
            ·
              refine ⟨1234182525489584248501795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1645576700652778998002393 1234182525489584248501795)
              ·
                refine ⟨1851273788234376372752693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234182525489584248501795 1851273788234376372752693)
                ·
                  refine ⟨173556917646972784945565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1851273788234376372752693 173556917646972784945565)
                  ·
                    rfl

theorem cell21_760502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_760502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760502 prefixEnd_760502 := by exact prefixLift 760502
  have htrace : WordTrace (prefixWord ++ tailWord_760502) baseStart_760502 baseEnd_760502 := by
    simpa [prefixWord, tailWord_760502, baseEnd_760502] using wordTrace_append hprefix tailTrace_760502
  have hstable : (prefixWord ++ tailWord_760502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760502).length < 2 ^ (prefixWord ++ tailWord_760502).sum := by decide
  have hdescent : baseEnd_760502 < baseStart_760502 := by decide
  rcases family_descends (prefixWord ++ tailWord_760502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760516 : List Nat := [2, 3, 3, 1, 1, 3, 3, 1, 4]
def baseStart_760516 : Nat := 118140960795 + 760516 * 2 ^ 59
def prefixEnd_760516 : Nat := 4983230072969 + 3 ^ 40 * 760516 * 2
def baseEnd_760516 : Nat := 173560112637711871712203

theorem tailTrace_760516 : CollatzResearch.WordTrace tailWord_760516 prefixEnd_760516 173560112637711871712203 := by
  unfold tailWord_760516
  simp only [CollatzResearch.WordTrace]
  refine ⟨13869148656393946318586701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18492198208525261758115601 13869148656393946318586701)
  ·
    refine ⟨5200930746147729869470013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13869148656393946318586701 5200930746147729869470013)
    ·
      refine ⟨1950349029805398701051255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5200930746147729869470013 1950349029805398701051255)
      ·
        refine ⟨2925523544708098051576883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1950349029805398701051255 2925523544708098051576883)
        ·
          refine ⟨4388285317062147077365325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2925523544708098051576883 4388285317062147077365325)
          ·
            refine ⟨1645606993898305154011997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4388285317062147077365325 1645606993898305154011997)
            ·
              refine ⟨617102622711864432754499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1645606993898305154011997 617102622711864432754499)
              ·
                refine ⟨925653934067796649131749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617102622711864432754499 925653934067796649131749)
                ·
                  refine ⟨173560112637711871712203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 925653934067796649131749 173560112637711871712203)
                  ·
                    rfl

theorem cell21_760516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_760516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760516 prefixEnd_760516 := by exact prefixLift 760516
  have htrace : WordTrace (prefixWord ++ tailWord_760516) baseStart_760516 baseEnd_760516 := by
    simpa [prefixWord, tailWord_760516, baseEnd_760516] using wordTrace_append hprefix tailTrace_760516
  have hstable : (prefixWord ++ tailWord_760516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760516).length < 2 ^ (prefixWord ++ tailWord_760516).sum := by decide
  have hdescent : baseEnd_760516 < baseStart_760516 := by decide
  rcases family_descends (prefixWord ++ tailWord_760516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760558 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_760558 : Nat := 118140960795 + 760558 * 2 ^ 59
def prefixEnd_760558 : Nat := 4983230072969 + 3 ^ 40 * 760558 * 2
def baseEnd_760558 : Nat := 173569697609929132012117

theorem tailTrace_760558 : CollatzResearch.WordTrace tailWord_760558 prefixEnd_760558 173569697609929132012117 := by
  unfold tailWord_760558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3467478647329466726275291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18493219452423822540134885 3467478647329466726275291)
  ·
    refine ⟨5201217970994200089412937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3467478647329466726275291 5201217970994200089412937)
    ·
      refine ⟨3900913478245650067059703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5201217970994200089412937 3900913478245650067059703)
      ·
        refine ⟨5851370217368475100589555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3900913478245650067059703 5851370217368475100589555)
        ·
          refine ⟨8777055326052712650884333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5851370217368475100589555 8777055326052712650884333)
          ·
            refine ⟨3291395747269767244081625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8777055326052712650884333 3291395747269767244081625)
            ·
              refine ⟨2468546810452325433061219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3291395747269767244081625 2468546810452325433061219)
              ·
                refine ⟨3702820215678488149591829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468546810452325433061219 3702820215678488149591829)
                ·
                  refine ⟨173569697609929132012117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3702820215678488149591829 173569697609929132012117)
                  ·
                    rfl

theorem cell21_760558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_760558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760558 prefixEnd_760558 := by exact prefixLift 760558
  have htrace : WordTrace (prefixWord ++ tailWord_760558) baseStart_760558 baseEnd_760558 := by
    simpa [prefixWord, tailWord_760558, baseEnd_760558] using wordTrace_append hprefix tailTrace_760558
  have hstable : (prefixWord ++ tailWord_760558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760558).length < 2 ^ (prefixWord ++ tailWord_760558).sum := by decide
  have hdescent : baseEnd_760558 < baseStart_760558 := by decide
  rcases family_descends (prefixWord ++ tailWord_760558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760561 : List Nat := [1, 2, 2, 2, 2, 2, 5, 2, 3]
def baseStart_760561 : Nat := 118140960795 + 760561 * 2 ^ 59
def prefixEnd_760561 : Nat := 4983230072969 + 3 ^ 40 * 760561 * 2
def baseEnd_760561 : Nat := 173570382250801793462111

theorem tailTrace_760561 : CollatzResearch.WordTrace tailWord_760561 prefixEnd_760561 173570382250801793462111 := by
  unfold tailWord_760561
  simp only [CollatzResearch.WordTrace]
  refine ⟨27739938597624865322561537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18493292398416576881707691 27739938597624865322561537)
  ·
    refine ⟨20804953948218648991921153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27739938597624865322561537 20804953948218648991921153)
    ·
      refine ⟨15603715461163986743940865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20804953948218648991921153 15603715461163986743940865)
      ·
        refine ⟨11702786595872990057955649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15603715461163986743940865 11702786595872990057955649)
        ·
          refine ⟨8777089946904742543466737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11702786595872990057955649 8777089946904742543466737)
          ·
            refine ⟨6582817460178556907600053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8777089946904742543466737 6582817460178556907600053)
            ·
              refine ⟨617139136891739710087505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6582817460178556907600053 617139136891739710087505)
              ·
                refine ⟨462854352668804782565629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617139136891739710087505 462854352668804782565629)
                ·
                  refine ⟨173570382250801793462111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462854352668804782565629 173570382250801793462111)
                  ·
                    rfl

theorem cell21_760561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 3].length) (baseStart_760561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760561 prefixEnd_760561 := by exact prefixLift 760561
  have htrace : WordTrace (prefixWord ++ tailWord_760561) baseStart_760561 baseEnd_760561 := by
    simpa [prefixWord, tailWord_760561, baseEnd_760561] using wordTrace_append hprefix tailTrace_760561
  have hstable : (prefixWord ++ tailWord_760561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760561).length < 2 ^ (prefixWord ++ tailWord_760561).sum := by decide
  have hdescent : baseEnd_760561 < baseStart_760561 := by decide
  rcases family_descends (prefixWord ++ tailWord_760561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760572 : List Nat := [2, 2, 2, 1, 3, 2, 1, 8]
def baseStart_760572 : Nat := 118140960795 + 760572 * 2 ^ 59
def prefixEnd_760572 : Nat := 4983230072969 + 3 ^ 40 * 760572 * 2
def baseEnd_760572 : Nat := 57857630866889406259585

theorem tailTrace_760572 : CollatzResearch.WordTrace tailWord_760572 prefixEnd_760572 57857630866889406259585 := by
  unfold tailWord_760572
  simp only [CollatzResearch.WordTrace]
  refine ⟨13870169900292507100605985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18493559867056676134141313 13870169900292507100605985)
  ·
    refine ⟨10402627425219380325454489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13870169900292507100605985 10402627425219380325454489)
    ·
      refine ⟨7801970568914535244090867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10402627425219380325454489 7801970568914535244090867)
      ·
        refine ⟨11702955853371802866136301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7801970568914535244090867 11702955853371802866136301)
        ·
          refine ⟨4388608445014426074801113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11702955853371802866136301 4388608445014426074801113)
          ·
            refine ⟨3291456333760819556100835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4388608445014426074801113 3291456333760819556100835)
            ·
              refine ⟨4937184500641229334151253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3291456333760819556100835 4937184500641229334151253)
              ·
                refine ⟨57857630866889406259585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4937184500641229334151253 57857630866889406259585)
                ·
                  rfl

theorem cell21_760572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_760572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760572 prefixEnd_760572 := by exact prefixLift 760572
  have htrace : WordTrace (prefixWord ++ tailWord_760572) baseStart_760572 baseEnd_760572 := by
    simpa [prefixWord, tailWord_760572, baseEnd_760572] using wordTrace_append hprefix tailTrace_760572
  have hstable : (prefixWord ++ tailWord_760572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760572).length < 2 ^ (prefixWord ++ tailWord_760572).sum := by decide
  have hdescent : baseEnd_760572 < baseStart_760572 := by decide
  rcases family_descends (prefixWord ++ tailWord_760572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760620 : List Nat := [2, 2, 1, 1, 1, 4, 3, 4, 3]
def baseStart_760620 : Nat := 118140960795 + 760620 * 2 ^ 59
def prefixEnd_760620 : Nat := 4983230072969 + 3 ^ 40 * 760620 * 2
def baseEnd_760620 : Nat := 173583846854630801978657

theorem tailTrace_760620 : CollatzResearch.WordTrace tailWord_760620 prefixEnd_760620 173583846854630801978657 := by
  unfold tailWord_760620
  simp only [CollatzResearch.WordTrace]
  refine ⟨13871045252205559199479657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18494727002940745599306209 13871045252205559199479657)
  ·
    refine ⟨10403283939154169399609743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13871045252205559199479657 10403283939154169399609743)
    ·
      refine ⟨15604925908731254099414615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10403283939154169399609743 15604925908731254099414615)
      ·
        refine ⟨23407388863096881149121923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15604925908731254099414615 23407388863096881149121923)
        ·
          refine ⟨35111083294645321723682885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23407388863096881149121923 35111083294645321723682885)
          ·
            refine ⟨6583328117745997823190541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35111083294645321723682885 6583328117745997823190541)
            ·
              refine ⟨2468748044154749183696453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6583328117745997823190541 2468748044154749183696453)
              ·
                refine ⟨462890258279015471943085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2468748044154749183696453 462890258279015471943085)
                ·
                  refine ⟨173583846854630801978657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462890258279015471943085 173583846854630801978657)
                  ·
                    rfl

theorem cell21_760620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_760620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760620 prefixEnd_760620 := by exact prefixLift 760620
  have htrace : WordTrace (prefixWord ++ tailWord_760620) baseStart_760620 baseEnd_760620 := by
    simpa [prefixWord, tailWord_760620, baseEnd_760620] using wordTrace_append hprefix tailTrace_760620
  have hstable : (prefixWord ++ tailWord_760620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760620).length < 2 ^ (prefixWord ++ tailWord_760620).sum := by decide
  have hdescent : baseEnd_760620 < baseStart_760620 := by decide
  rcases family_descends (prefixWord ++ tailWord_760620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760668 : List Nat := [2, 2, 4, 2, 1, 3, 1, 2, 4]
def baseStart_760668 : Nat := 118140960795 + 760668 * 2 ^ 59
def prefixEnd_760668 : Nat := 4983230072969 + 3 ^ 40 * 760668 * 2
def baseEnd_760668 : Nat := 173594801108593385178559

theorem tailTrace_760668 : CollatzResearch.WordTrace tailWord_760668 prefixEnd_760668 173594801108593385178559 := by
  unfold tailWord_760668
  simp only [CollatzResearch.WordTrace]
  refine ⟨13871920604118611298353329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18495894138824815064471105 13871920604118611298353329)
  ·
    refine ⟨10403940453088958473764997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13871920604118611298353329 10403940453088958473764997)
    ·
      refine ⟨1950738834954179713830937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10403940453088958473764997 1950738834954179713830937)
      ·
        refine ⟨1463054126215634785373203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1950738834954179713830937 1463054126215634785373203)
        ·
          refine ⟨2194581189323452178059805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463054126215634785373203 2194581189323452178059805)
          ·
            refine ⟨822967945996294566772427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2194581189323452178059805 822967945996294566772427)
            ·
              refine ⟨1234451918994441850158641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822967945996294566772427 1234451918994441850158641)
              ·
                refine ⟨925838939245831387618981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234451918994441850158641 925838939245831387618981)
                ·
                  refine ⟨173594801108593385178559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 925838939245831387618981 173594801108593385178559)
                  ·
                    rfl

theorem cell21_760668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_760668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760668 prefixEnd_760668 := by exact prefixLift 760668
  have htrace : WordTrace (prefixWord ++ tailWord_760668) baseStart_760668 baseEnd_760668 := by
    simpa [prefixWord, tailWord_760668, baseEnd_760668] using wordTrace_append hprefix tailTrace_760668
  have hstable : (prefixWord ++ tailWord_760668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760668).length < 2 ^ (prefixWord ++ tailWord_760668).sum := by decide
  have hdescent : baseEnd_760668 < baseStart_760668 := by decide
  rcases family_descends (prefixWord ++ tailWord_760668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760679 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 5]
def baseStart_760679 : Nat := 118140960795 + 760679 * 2 ^ 59
def prefixEnd_760679 : Nat := 4983230072969 + 3 ^ 40 * 760679 * 2
def baseEnd_760679 : Nat := 173597311458459810495203

theorem tailTrace_760679 : CollatzResearch.WordTrace tailWord_760679 prefixEnd_760679 173597311458459810495203 := by
  unfold tailWord_760679
  simp only [CollatzResearch.WordTrace]
  refine ⟨27744242411197371475357091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18496161607464914316904727 27744242411197371475357091)
  ·
    refine ⟨41616363616796057213035637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27744242411197371475357091 41616363616796057213035637)
    ·
      refine ⟨3901534089074630363722091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41616363616796057213035637 3901534089074630363722091)
      ·
        refine ⟨5852301133611945545583137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3901534089074630363722091 5852301133611945545583137)
        ·
          refine ⟨4389225850208959159187353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5852301133611945545583137 4389225850208959159187353)
          ·
            refine ⟨3291919387656719369390515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4389225850208959159187353 3291919387656719369390515)
            ·
              refine ⟨4937879081485079054085773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3291919387656719369390515 4937879081485079054085773)
              ·
                refine ⟨1851704655556904645282165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4937879081485079054085773 1851704655556904645282165)
                ·
                  refine ⟨173597311458459810495203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1851704655556904645282165 173597311458459810495203)
                  ·
                    rfl

theorem cell21_760679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 5].length) (baseStart_760679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760679 prefixEnd_760679 := by exact prefixLift 760679
  have htrace : WordTrace (prefixWord ++ tailWord_760679) baseStart_760679 baseEnd_760679 := by
    simpa [prefixWord, tailWord_760679, baseEnd_760679] using wordTrace_append hprefix tailTrace_760679
  have hstable : (prefixWord ++ tailWord_760679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760679).length < 2 ^ (prefixWord ++ tailWord_760679).sum := by decide
  have hdescent : baseEnd_760679 < baseStart_760679 := by decide
  rcases family_descends (prefixWord ++ tailWord_760679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760713 : List Nat := [1, 2, 1, 1, 5, 4, 1, 3, 3]
def baseStart_760713 : Nat := 118140960795 + 760713 * 2 ^ 59
def prefixEnd_760713 : Nat := 4983230072969 + 3 ^ 40 * 760713 * 2
def baseEnd_760713 : Nat := 173605070721683306928467

theorem tailTrace_760713 : CollatzResearch.WordTrace tailWord_760713 prefixEnd_760713 173605070721683306928467 := by
  unfold tailWord_760713
  simp only [CollatzResearch.WordTrace]
  refine ⟨27745482493074195282094793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18496988328716130188063195 27745482493074195282094793)
  ·
    refine ⟨20809111869805646461571095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27745482493074195282094793 20809111869805646461571095)
    ·
      refine ⟨31213667804708469692356643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20809111869805646461571095 31213667804708469692356643)
      ·
        refine ⟨46820501707062704538534965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31213667804708469692356643 46820501707062704538534965)
        ·
          refine ⟨4389422035037128550487653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46820501707062704538534965 4389422035037128550487653)
          ·
            refine ⟨823016631569461603216435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4389422035037128550487653 823016631569461603216435)
            ·
              refine ⟨1234524947354192404824653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823016631569461603216435 1234524947354192404824653)
              ·
                refine ⟨462946855257822151809245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1234524947354192404824653 462946855257822151809245)
                ·
                  refine ⟨173605070721683306928467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462946855257822151809245 173605070721683306928467)
                  ·
                    rfl

theorem cell21_760713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 3].length) (baseStart_760713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760713 prefixEnd_760713 := by exact prefixLift 760713
  have htrace : WordTrace (prefixWord ++ tailWord_760713) baseStart_760713 baseEnd_760713 := by
    simpa [prefixWord, tailWord_760713, baseEnd_760713] using wordTrace_append hprefix tailTrace_760713
  have hstable : (prefixWord ++ tailWord_760713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760713).length < 2 ^ (prefixWord ++ tailWord_760713).sum := by decide
  have hdescent : baseEnd_760713 < baseStart_760713 := by decide
  rcases family_descends (prefixWord ++ tailWord_760713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760730 : List Nat := [3, 1, 1, 4, 3, 1, 3, 2, 3]
def baseStart_760730 : Nat := 118140960795 + 760730 * 2 ^ 59
def prefixEnd_760730 : Nat := 4983230072969 + 3 ^ 40 * 760730 * 2
def baseEnd_760730 : Nat := 173608950353295055145099

theorem tailTrace_760730 : CollatzResearch.WordTrace tailWord_760730 prefixEnd_760730 173608950353295055145099 := by
  unfold tailWord_760730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6936525633503151796365911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18497401689341738123642429 6936525633503151796365911)
  ·
    refine ⟨10404788450254727694548867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6936525633503151796365911 10404788450254727694548867)
    ·
      refine ⟨15607182675382091541823301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10404788450254727694548867 15607182675382091541823301)
      ·
        refine ⟨2926346751634142164091869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15607182675382091541823301 2926346751634142164091869)
        ·
          refine ⟨1097380031862803311534451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2926346751634142164091869 1097380031862803311534451)
          ·
            refine ⟨1646070047794204967301677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097380031862803311534451 1646070047794204967301677)
            ·
              refine ⟨617276267922826862738129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1646070047794204967301677 617276267922826862738129)
              ·
                refine ⟨462957200942120147053597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617276267922826862738129 462957200942120147053597)
                ·
                  refine ⟨173608950353295055145099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462957200942120147053597 173608950353295055145099)
                  ·
                    rfl

theorem cell21_760730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_760730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760730 prefixEnd_760730 := by exact prefixLift 760730
  have htrace : WordTrace (prefixWord ++ tailWord_760730) baseStart_760730 baseEnd_760730 := by
    simpa [prefixWord, tailWord_760730, baseEnd_760730] using wordTrace_append hprefix tailTrace_760730
  have hstable : (prefixWord ++ tailWord_760730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760730).length < 2 ^ (prefixWord ++ tailWord_760730).sum := by decide
  have hdescent : baseEnd_760730 < baseStart_760730 := by decide
  rcases family_descends (prefixWord ++ tailWord_760730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760781 : List Nat := [1, 6, 3, 1, 1, 2, 2, 2, 3]
def baseStart_760781 : Nat := 118140960795 + 760781 * 2 ^ 59
def prefixEnd_760781 : Nat := 4983230072969 + 3 ^ 40 * 760781 * 2
def baseEnd_760781 : Nat := 173620589248130299794995

theorem tailTrace_760781 : CollatzResearch.WordTrace tailWord_760781 prefixEnd_760781 173620589248130299794995 := by
  unfold tailWord_760781
  simp only [CollatzResearch.WordTrace]
  refine ⟨27747962656827842895570197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18498641771218561930380131 27747962656827842895570197)
  ·
    refine ⟨1300685749538805135729853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27747962656827842895570197 1300685749538805135729853)
    ·
      refine ⟨487757156077051925898695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1300685749538805135729853 487757156077051925898695)
      ·
        refine ⟨731635734115577888848043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487757156077051925898695 731635734115577888848043)
        ·
          refine ⟨1097453601173366833272065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731635734115577888848043 1097453601173366833272065)
          ·
            refine ⟨823090200880025124954049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1097453601173366833272065 823090200880025124954049)
            ·
              refine ⟨617317650660018843715537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 823090200880025124954049 617317650660018843715537)
              ·
                refine ⟨462988237995014132786653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617317650660018843715537 462988237995014132786653)
                ·
                  refine ⟨173620589248130299794995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462988237995014132786653 173620589248130299794995)
                  ·
                    rfl

theorem cell21_760781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_760781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760781 prefixEnd_760781 := by exact prefixLift 760781
  have htrace : WordTrace (prefixWord ++ tailWord_760781) baseStart_760781 baseEnd_760781 := by
    simpa [prefixWord, tailWord_760781, baseEnd_760781] using wordTrace_append hprefix tailTrace_760781
  have hstable : (prefixWord ++ tailWord_760781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760781).length < 2 ^ (prefixWord ++ tailWord_760781).sum := by decide
  have hdescent : baseEnd_760781 < baseStart_760781 := by decide
  rcases family_descends (prefixWord ++ tailWord_760781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760783 : List Nat := [1, 1, 2, 1, 1, 15]
def baseStart_760783 : Nat := 118140960795 + 760783 * 2 ^ 59
def prefixEnd_760783 : Nat := 4983230072969 + 3 ^ 40 * 760783 * 2
def baseEnd_760783 : Nat := 6430409099088101509691

theorem tailTrace_760783 : CollatzResearch.WordTrace tailWord_760783 prefixEnd_760783 6430409099088101509691 := by
  unfold tailWord_760783
  simp only [CollatzResearch.WordTrace]
  refine ⟨27748035602820597237143003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18498690401880398158095335 27748035602820597237143003)
  ·
    refine ⟨41622053404230895855714505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27748035602820597237143003 41622053404230895855714505)
    ·
      refine ⟨31216540053173171891785879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41622053404230895855714505 31216540053173171891785879)
      ·
        refine ⟨46824810079759757837678819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31216540053173171891785879 46824810079759757837678819)
        ·
          refine ⟨70237215119639636756518229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46824810079759757837678819 70237215119639636756518229)
          ·
            refine ⟨6430409099088101509691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 70237215119639636756518229 6430409099088101509691)
            ·
              rfl

theorem cell21_760783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 15].length) (baseStart_760783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760783 prefixEnd_760783 := by exact prefixLift 760783
  have htrace : WordTrace (prefixWord ++ tailWord_760783) baseStart_760783 baseEnd_760783 := by
    simpa [prefixWord, tailWord_760783, baseEnd_760783] using wordTrace_append hprefix tailTrace_760783
  have hstable : (prefixWord ++ tailWord_760783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760783).length < 2 ^ (prefixWord ++ tailWord_760783).sum := by decide
  have hdescent : baseEnd_760783 < baseStart_760783 := by decide
  rcases family_descends (prefixWord ++ tailWord_760783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760789 : List Nat := [1, 3, 2, 3, 3, 1, 1, 4, 3]
def baseStart_760789 : Nat := 118140960795 + 760789 * 2 ^ 59
def prefixEnd_760789 : Nat := 4983230072969 + 3 ^ 40 * 760789 * 2
def baseEnd_760789 : Nat := 173622414957124063661645

theorem tailTrace_760789 : CollatzResearch.WordTrace tailWord_760789 prefixEnd_760789 173622414957124063661645 := by
  unfold tailWord_760789
  simp only [CollatzResearch.WordTrace]
  refine ⟨27748254440798860261861421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18498836293865906841240947 27748254440798860261861421)
  ·
    refine ⟨10405595415299572598198033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27748254440798860261861421 10405595415299572598198033)
    ·
      refine ⟨7804196561474679448648525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10405595415299572598198033 7804196561474679448648525)
      ·
        refine ⟨2926573710553004793243197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7804196561474679448648525 2926573710553004793243197)
        ·
          refine ⟨1097465141457376797466199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2926573710553004793243197 1097465141457376797466199)
          ·
            refine ⟨1646197712186065196199299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097465141457376797466199 1646197712186065196199299)
            ·
              refine ⟨2469296568279097794298949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1646197712186065196199299 2469296568279097794298949)
              ·
                refine ⟨462993106552330836431053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2469296568279097794298949 462993106552330836431053)
                ·
                  refine ⟨173622414957124063661645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462993106552330836431053 173622414957124063661645)
                  ·
                    rfl

theorem cell21_760789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_760789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760789 prefixEnd_760789 := by exact prefixLift 760789
  have htrace : WordTrace (prefixWord ++ tailWord_760789) baseStart_760789 baseEnd_760789 := by
    simpa [prefixWord, tailWord_760789, baseEnd_760789] using wordTrace_append hprefix tailTrace_760789
  have hstable : (prefixWord ++ tailWord_760789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760789).length < 2 ^ (prefixWord ++ tailWord_760789).sum := by decide
  have hdescent : baseEnd_760789 < baseStart_760789 := by decide
  rcases family_descends (prefixWord ++ tailWord_760789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760817 : List Nat := [1, 2, 2, 2, 4, 2, 3, 5]
def baseStart_760817 : Nat := 118140960795 + 760817 * 2 ^ 59
def prefixEnd_760817 : Nat := 4983230072969 + 3 ^ 40 * 760817 * 2
def baseEnd_760817 : Nat := 57876268312867412398307

theorem tailTrace_760817 : CollatzResearch.WordTrace tailWord_760817 prefixEnd_760817 57876268312867412398307 := by
  unfold tailWord_760817
  simp only [CollatzResearch.WordTrace]
  refine ⟨27749275684697421043880705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18499517123131614029253803 27749275684697421043880705)
  ·
    refine ⟨20811956763523065782910529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27749275684697421043880705 20811956763523065782910529)
    ·
      refine ⟨15608967572642299337182897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20811956763523065782910529 15608967572642299337182897)
      ·
        refine ⟨11706725679481724502887173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15608967572642299337182897 11706725679481724502887173)
        ·
          refine ⟨2195011064902823344291345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11706725679481724502887173 2195011064902823344291345)
          ·
            refine ⟨1646258298677117508218509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2195011064902823344291345 1646258298677117508218509)
            ·
              refine ⟨617346862003919065581941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1646258298677117508218509 617346862003919065581941)
              ·
                refine ⟨57876268312867412398307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 617346862003919065581941 57876268312867412398307)
                ·
                  rfl

theorem cell21_760817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 5].length) (baseStart_760817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760817 prefixEnd_760817 := by exact prefixLift 760817
  have htrace : WordTrace (prefixWord ++ tailWord_760817) baseStart_760817 baseEnd_760817 := by
    simpa [prefixWord, tailWord_760817, baseEnd_760817] using wordTrace_append hprefix tailTrace_760817
  have hstable : (prefixWord ++ tailWord_760817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760817).length < 2 ^ (prefixWord ++ tailWord_760817).sum := by decide
  have hdescent : baseEnd_760817 < baseStart_760817 := by decide
  rcases family_descends (prefixWord ++ tailWord_760817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760834 : List Nat := [3, 4, 1, 3, 1, 1, 8]
def baseStart_760834 : Nat := 118140960795 + 760834 * 2 ^ 59
def prefixEnd_760834 : Nat := 4983230072969 + 3 ^ 40 * 760834 * 2
def baseEnd_760834 : Nat := 19292520507801553934617

theorem tailTrace_760834 : CollatzResearch.WordTrace tailWord_760834 prefixEnd_760834 19292520507801553934617 := by
  unfold tailWord_760834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6937473931408958236812389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18499930483757221964833037 6937473931408958236812389)
  ·
    refine ⟨1300776362139179669402323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6937473931408958236812389 1300776362139179669402323)
    ·
      refine ⟨1951164543208769504103485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1300776362139179669402323 1951164543208769504103485)
      ·
        refine ⟨731686703703288564038807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1951164543208769504103485 731686703703288564038807)
        ·
          refine ⟨1097530055554932846058211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731686703703288564038807 1097530055554932846058211)
          ·
            refine ⟨1646295083332399269087317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097530055554932846058211 1646295083332399269087317)
            ·
              refine ⟨19292520507801553934617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1646295083332399269087317 19292520507801553934617)
              ·
                rfl

theorem cell21_760834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 8].length) (baseStart_760834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760834 prefixEnd_760834 := by exact prefixLift 760834
  have htrace : WordTrace (prefixWord ++ tailWord_760834) baseStart_760834 baseEnd_760834 := by
    simpa [prefixWord, tailWord_760834, baseEnd_760834] using wordTrace_append hprefix tailTrace_760834
  have hstable : (prefixWord ++ tailWord_760834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760834).length < 2 ^ (prefixWord ++ tailWord_760834).sum := by decide
  have hdescent : baseEnd_760834 < baseStart_760834 := by decide
  rcases family_descends (prefixWord ++ tailWord_760834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760890 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_760890 : Nat := 118140960795 + 760890 * 2 ^ 59
def prefixEnd_760890 : Nat := 4983230072969 + 3 ^ 40 * 760890 * 2
def baseEnd_760890 : Nat := 173645464533170332478105

theorem tailTrace_760890 : CollatzResearch.WordTrace tailWord_760890 prefixEnd_760890 173645464533170332478105 := by
  unfold tailWord_760890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6937984553358238627822031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18501292142288636340858749 6937984553358238627822031)
  ·
    refine ⟨10406976830037357941733047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6937984553358238627822031 10406976830037357941733047)
    ·
      refine ⟨15610465245056036912599571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10406976830037357941733047 15610465245056036912599571)
      ·
        refine ⟨23415697867584055368899357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15610465245056036912599571 23415697867584055368899357)
        ·
          refine ⟨8780886700344020763337259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23415697867584055368899357 8780886700344020763337259)
          ·
            refine ⟨13171330050516031145005889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8780886700344020763337259 13171330050516031145005889)
            ·
              refine ⟨9878497537887023358754417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13171330050516031145005889 9878497537887023358754417)
              ·
                refine ⟨7408873153415267519065813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9878497537887023358754417 7408873153415267519065813)
                ·
                  refine ⟨173645464533170332478105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7408873153415267519065813 173645464533170332478105)
                  ·
                    rfl

theorem cell21_760890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_760890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760890 prefixEnd_760890 := by exact prefixLift 760890
  have htrace : WordTrace (prefixWord ++ tailWord_760890) baseStart_760890 baseEnd_760890 := by
    simpa [prefixWord, tailWord_760890, baseEnd_760890] using wordTrace_append hprefix tailTrace_760890
  have hstable : (prefixWord ++ tailWord_760890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760890).length < 2 ^ (prefixWord ++ tailWord_760890).sum := by decide
  have hdescent : baseEnd_760890 < baseStart_760890 := by decide
  rcases family_descends (prefixWord ++ tailWord_760890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760983 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 5]
def baseStart_760983 : Nat := 118140960795 + 760983 * 2 ^ 59
def prefixEnd_760983 : Nat := 4983230072969 + 3 ^ 40 * 760983 * 2
def baseEnd_760983 : Nat := 173666688400222837427915

theorem tailTrace_760983 : CollatzResearch.WordTrace tailWord_760983 prefixEnd_760983 173666688400222837427915 := by
  unfold tailWord_760983
  simp only [CollatzResearch.WordTrace]
  refine ⟨27755330202096031394423603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18503553468064020929615735 27755330202096031394423603)
  ·
    refine ⟨41632995303144047091635405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27755330202096031394423603 41632995303144047091635405)
    ·
      refine ⟨15612373238679017659363277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41632995303144047091635405 15612373238679017659363277)
      ·
        refine ⟨5854639964504631622261229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15612373238679017659363277 5854639964504631622261229)
        ·
          refine ⟨2195489986689236858347961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5854639964504631622261229 2195489986689236858347961)
          ·
            refine ⟨1646617490016927643760971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2195489986689236858347961 1646617490016927643760971)
            ·
              refine ⟨2469926235025391465641457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1646617490016927643760971 2469926235025391465641457)
              ·
                refine ⟨1852444676269043599231093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469926235025391465641457 1852444676269043599231093)
                ·
                  refine ⟨173666688400222837427915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1852444676269043599231093 173666688400222837427915)
                  ·
                    rfl

theorem cell21_760983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 5].length) (baseStart_760983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_760983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_760983 prefixEnd_760983 := by exact prefixLift 760983
  have htrace : WordTrace (prefixWord ++ tailWord_760983) baseStart_760983 baseEnd_760983 := by
    simpa [prefixWord, tailWord_760983, baseEnd_760983] using wordTrace_append hprefix tailTrace_760983
  have hstable : (prefixWord ++ tailWord_760983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760983).length < 2 ^ (prefixWord ++ tailWord_760983).sum := by decide
  have hdescent : baseEnd_760983 < baseStart_760983 := by decide
  rcases family_descends (prefixWord ++ tailWord_760983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761045 : List Nat := [1, 3, 2, 4, 1, 1, 4, 5]
def baseStart_761045 : Nat := 118140960795 + 761045 * 2 ^ 59
def prefixEnd_761045 : Nat := 4983230072969 + 3 ^ 40 * 761045 * 2
def baseEnd_761045 : Nat := 57893612548308169131485

theorem tailTrace_761045 : CollatzResearch.WordTrace tailWord_761045 prefixEnd_761045 57893612548308169131485 := by
  unfold tailWord_761045
  simp only [CollatzResearch.WordTrace]
  refine ⟨27757591527871415983180589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18505061018580943988787059 27757591527871415983180589)
  ·
    refine ⟨10409096822951780993692721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27757591527871415983180589 10409096822951780993692721)
    ·
      refine ⟨7806822617213835745269541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10409096822951780993692721 7806822617213835745269541)
      ·
        refine ⟨1463779240727594202238039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7806822617213835745269541 1463779240727594202238039)
        ·
          refine ⟨2195668861091391303357059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463779240727594202238039 2195668861091391303357059)
          ·
            refine ⟨3293503291637086955035589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195668861091391303357059 3293503291637086955035589)
            ·
              refine ⟨617531867181953804069173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3293503291637086955035589 617531867181953804069173)
              ·
                refine ⟨57893612548308169131485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 617531867181953804069173 57893612548308169131485)
                ·
                  rfl

theorem cell21_761045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 5].length) (baseStart_761045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761045 prefixEnd_761045 := by exact prefixLift 761045
  have htrace : WordTrace (prefixWord ++ tailWord_761045) baseStart_761045 baseEnd_761045 := by
    simpa [prefixWord, tailWord_761045, baseEnd_761045] using wordTrace_append hprefix tailTrace_761045
  have hstable : (prefixWord ++ tailWord_761045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761045).length < 2 ^ (prefixWord ++ tailWord_761045).sum := by decide
  have hdescent : baseEnd_761045 < baseStart_761045 := by decide
  rcases family_descends (prefixWord ++ tailWord_761045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761073 : List Nat := [1, 2, 2, 2, 2, 1, 1, 6, 4]
def baseStart_761073 : Nat := 118140960795 + 761073 * 2 ^ 59
def prefixEnd_761073 : Nat := 4983230072969 + 3 ^ 40 * 761073 * 2
def baseEnd_761073 : Nat := 173687227626402680927731

theorem tailTrace_761073 : CollatzResearch.WordTrace tailWord_761073 prefixEnd_761073 173687227626402680927731 := by
  unfold tailWord_761073
  simp only [CollatzResearch.WordTrace]
  refine ⟨27758612771769976765199873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18505741847846651176799915 27758612771769976765199873)
  ·
    refine ⟨20818959578827482573899905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27758612771769976765199873 20818959578827482573899905)
    ·
      refine ⟨15614219684120611930424929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20818959578827482573899905 15614219684120611930424929)
      ·
        refine ⟨11710664763090458947818697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15614219684120611930424929 11710664763090458947818697)
        ·
          refine ⟨8782998572317844210864023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11710664763090458947818697 8782998572317844210864023)
          ·
            refine ⟨13174497858476766316296035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8782998572317844210864023 13174497858476766316296035)
            ·
              refine ⟨19761746787715149474444053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13174497858476766316296035 19761746787715149474444053)
              ·
                refine ⟨926331880674147631614565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19761746787715149474444053 926331880674147631614565)
                ·
                  refine ⟨173687227626402680927731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 926331880674147631614565 173687227626402680927731)
                  ·
                    rfl

theorem cell21_761073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_761073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761073 prefixEnd_761073 := by exact prefixLift 761073
  have htrace : WordTrace (prefixWord ++ tailWord_761073) baseStart_761073 baseEnd_761073 := by
    simpa [prefixWord, tailWord_761073, baseEnd_761073] using wordTrace_append hprefix tailTrace_761073
  have hstable : (prefixWord ++ tailWord_761073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761073).length < 2 ^ (prefixWord ++ tailWord_761073).sum := by decide
  have hdescent : baseEnd_761073 < baseStart_761073 := by decide
  rcases family_descends (prefixWord ++ tailWord_761073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761087 : List Nat := [1, 1, 2, 2, 1, 5, 1, 8]
def baseStart_761087 : Nat := 118140960795 + 761087 * 2 ^ 59
def prefixEnd_761087 : Nat := 4983230072969 + 3 ^ 40 * 761087 * 2
def baseEnd_761087 : Nat := 57896807539047255898123

theorem tailTrace_761087 : CollatzResearch.WordTrace tailWord_761087 prefixEnd_761087 57896807539047255898123 := by
  unfold tailWord_761087
  simp only [CollatzResearch.WordTrace]
  refine ⟨27759123393719257156209515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18506082262479504770806343 27759123393719257156209515)
  ·
    refine ⟨41638685090578885734314273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27759123393719257156209515 41638685090578885734314273)
    ·
      refine ⟨31229013817934164300735705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41638685090578885734314273 31229013817934164300735705)
      ·
        refine ⟨23421760363450623225551779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31229013817934164300735705 23421760363450623225551779)
        ·
          refine ⟨35132640545175934838327669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23421760363450623225551779 35132640545175934838327669)
          ·
            refine ⟨3293685051110243891093219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35132640545175934838327669 3293685051110243891093219)
            ·
              refine ⟨4940527576665365836639829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3293685051110243891093219 4940527576665365836639829)
              ·
                refine ⟨57896807539047255898123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4940527576665365836639829 57896807539047255898123)
                ·
                  rfl

theorem cell21_761087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 8].length) (baseStart_761087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761087 prefixEnd_761087 := by exact prefixLift 761087
  have htrace : WordTrace (prefixWord ++ tailWord_761087) baseStart_761087 baseEnd_761087 := by
    simpa [prefixWord, tailWord_761087, baseEnd_761087] using wordTrace_append hprefix tailTrace_761087
  have hstable : (prefixWord ++ tailWord_761087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761087).length < 2 ^ (prefixWord ++ tailWord_761087).sum := by decide
  have hdescent : baseEnd_761087 < baseStart_761087 := by decide
  rcases family_descends (prefixWord ++ tailWord_761087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761214 : List Nat := [4, 2, 3, 2, 1, 1, 1, 7]
def baseStart_761214 : Nat := 118140960795 + 761214 * 2 ^ 59
def prefixEnd_761214 : Nat := 4983230072969 + 3 ^ 40 * 761214 * 2
def baseEnd_761214 : Nat := 57906468582472589692481

theorem tailTrace_761214 : CollatzResearch.WordTrace tailWord_761214 prefixEnd_761214 57906468582472589692481 := by
  unfold tailWord_761214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3470469433032394730760337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18509170309506105230721797 3470469433032394730760337)
  ·
    refine ⟨2602852074774296048070253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3470469433032394730760337 2602852074774296048070253)
    ·
      refine ⟨976069528040361018026345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2602852074774296048070253 976069528040361018026345)
      ·
        refine ⟨732052146030270763519759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 976069528040361018026345 732052146030270763519759)
        ·
          refine ⟨1098078219045406145279639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732052146030270763519759 1098078219045406145279639)
          ·
            refine ⟨1647117328568109217919459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098078219045406145279639 1647117328568109217919459)
            ·
              refine ⟨2470675992852163826879189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647117328568109217919459 2470675992852163826879189)
              ·
                refine ⟨57906468582472589692481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2470675992852163826879189 57906468582472589692481)
                ·
                  rfl

theorem cell21_761214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_761214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761214 prefixEnd_761214 := by exact prefixLift 761214
  have htrace : WordTrace (prefixWord ++ tailWord_761214) baseStart_761214 baseEnd_761214 := by
    simpa [prefixWord, tailWord_761214, baseEnd_761214] using wordTrace_append hprefix tailTrace_761214
  have hstable : (prefixWord ++ tailWord_761214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761214).length < 2 ^ (prefixWord ++ tailWord_761214).sum := by decide
  have hdescent : baseEnd_761214 < baseStart_761214 := by decide
  rcases family_descends (prefixWord ++ tailWord_761214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761245 : List Nat := [1, 4, 2, 1, 3, 2, 3, 2, 3]
def baseStart_761245 : Nat := 118140960795 + 761245 * 2 ^ 59
def prefixEnd_761245 : Nat := 4983230072969 + 3 ^ 40 * 761245 * 2
def baseEnd_761245 : Nat := 173726480369768604060713

theorem tailTrace_761245 : CollatzResearch.WordTrace tailWord_761245 prefixEnd_761245 173726480369768604060713 := by
  unfold tailWord_761245
  simp only [CollatzResearch.WordTrace]
  refine ⟨27764886127146850140461189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18509924084764566760307459 27764886127146850140461189)
  ·
    refine ⟨5205916148840034401336473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27764886127146850140461189 5205916148840034401336473)
    ·
      refine ⟨3904437111630025801002355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5205916148840034401336473 3904437111630025801002355)
      ·
        refine ⟨5856655667445038701503533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3904437111630025801002355 5856655667445038701503533)
        ·
          refine ⟨2196245875291889513063825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5856655667445038701503533 2196245875291889513063825)
          ·
            refine ⟨1647184406468917134797869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2196245875291889513063825 1647184406468917134797869)
            ·
              refine ⟨617694152425843925549201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1647184406468917134797869 617694152425843925549201)
              ·
                refine ⟨463270614319382944161901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617694152425843925549201 463270614319382944161901)
                ·
                  refine ⟨173726480369768604060713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463270614319382944161901 173726480369768604060713)
                  ·
                    rfl

theorem cell21_761245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_761245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761245 prefixEnd_761245 := by exact prefixLift 761245
  have htrace : WordTrace (prefixWord ++ tailWord_761245) baseStart_761245 baseEnd_761245 := by
    simpa [prefixWord, tailWord_761245, baseEnd_761245] using wordTrace_append hprefix tailTrace_761245
  have hstable : (prefixWord ++ tailWord_761245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761245).length < 2 ^ (prefixWord ++ tailWord_761245).sum := by decide
  have hdescent : baseEnd_761245 < baseStart_761245 := by decide
  rcases family_descends (prefixWord ++ tailWord_761245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761287 : List Nat := [1, 1, 4, 1, 1, 3, 2, 5, 3]
def baseStart_761287 : Nat := 118140960795 + 761287 * 2 ^ 59
def prefixEnd_761287 : Nat := 4983230072969 + 3 ^ 40 * 761287 * 2
def baseEnd_761287 : Nat := 173736065341985864360627

theorem tailTrace_761287 : CollatzResearch.WordTrace tailWord_761287 prefixEnd_761287 173736065341985864360627 := by
  unfold tailWord_761287
  simp only [CollatzResearch.WordTrace]
  refine ⟨27766417992994691313490115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18510945328663127542326743 27766417992994691313490115)
  ·
    refine ⟨41649626989492036970235173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27766417992994691313490115 41649626989492036970235173)
    ·
      refine ⟨7809305060529756931919095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41649626989492036970235173 7809305060529756931919095)
      ·
        refine ⟨11713957590794635397878643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7809305060529756931919095 11713957590794635397878643)
        ·
          refine ⟨17570936386191953096817965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11713957590794635397878643 17570936386191953096817965)
          ·
            refine ⟨6589101144821982411306737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17570936386191953096817965 6589101144821982411306737)
            ·
              refine ⟨4941825858616486808480053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6589101144821982411306737 4941825858616486808480053)
              ·
                refine ⟨463296174245295638295005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4941825858616486808480053 463296174245295638295005)
                ·
                  refine ⟨173736065341985864360627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463296174245295638295005 173736065341985864360627)
                  ·
                    rfl

theorem cell21_761287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 3].length) (baseStart_761287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761287 prefixEnd_761287 := by exact prefixLift 761287
  have htrace : WordTrace (prefixWord ++ tailWord_761287) baseStart_761287 baseEnd_761287 := by
    simpa [prefixWord, tailWord_761287, baseEnd_761287] using wordTrace_append hprefix tailTrace_761287
  have hstable : (prefixWord ++ tailWord_761287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761287).length < 2 ^ (prefixWord ++ tailWord_761287).sum := by decide
  have hdescent : baseEnd_761287 < baseStart_761287 := by decide
  rcases family_descends (prefixWord ++ tailWord_761287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761304 : List Nat := [2, 1, 2, 2, 2, 1, 6, 2, 3]
def baseStart_761304 : Nat := 118140960795 + 761304 * 2 ^ 59
def prefixEnd_761304 : Nat := 4983230072969 + 3 ^ 40 * 761304 * 2
def baseEnd_761304 : Nat := 173739944973597612577259

theorem tailTrace_761304 : CollatzResearch.WordTrace tailWord_761304 prefixEnd_761304 173739944973597612577259 := by
  unfold tailWord_761304
  simp only [CollatzResearch.WordTrace]
  refine ⟨13883519016966551608429483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18511358689288735477905977 13883519016966551608429483)
  ·
    refine ⟨20825278525449827412644225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13883519016966551608429483 20825278525449827412644225)
    ·
      refine ⟨15618958894087370559483169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20825278525449827412644225 15618958894087370559483169)
      ·
        refine ⟨11714219170565527919612377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15618958894087370559483169 11714219170565527919612377)
        ·
          refine ⟨8785664377924145939709283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11714219170565527919612377 8785664377924145939709283)
          ·
            refine ⟨13178496566886218909563925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8785664377924145939709283 13178496566886218909563925)
            ·
              refine ⟨617742026572791511385809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13178496566886218909563925 617742026572791511385809)
              ·
                refine ⟨463306519929593633539357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617742026572791511385809 463306519929593633539357)
                ·
                  refine ⟨173739944973597612577259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463306519929593633539357 173739944973597612577259)
                  ·
                    rfl

theorem cell21_761304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 3].length) (baseStart_761304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761304 prefixEnd_761304 := by exact prefixLift 761304
  have htrace : WordTrace (prefixWord ++ tailWord_761304) baseStart_761304 baseEnd_761304 := by
    simpa [prefixWord, tailWord_761304, baseEnd_761304] using wordTrace_append hprefix tailTrace_761304
  have hstable : (prefixWord ++ tailWord_761304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761304).length < 2 ^ (prefixWord ++ tailWord_761304).sum := by decide
  have hdescent : baseEnd_761304 < baseStart_761304 := by decide
  rcases family_descends (prefixWord ++ tailWord_761304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761363 : List Nat := [1, 1, 1, 2, 1, 6, 2, 4, 3]
def baseStart_761363 : Nat := 118140960795 + 761363 * 2 ^ 59
def prefixEnd_761363 : Nat := 4983230072969 + 3 ^ 40 * 761363 * 2
def baseEnd_761363 : Nat := 173753409577426621093805

theorem tailTrace_761363 : CollatzResearch.WordTrace tailWord_761363 prefixEnd_761363 173753409577426621093805 := by
  unfold tailWord_761363
  simp only [CollatzResearch.WordTrace]
  refine ⟨27769189940719356293256743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18512793293812904195504495 27769189940719356293256743)
  ·
    refine ⟨41653784911079034439885115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27769189940719356293256743 41653784911079034439885115)
    ·
      refine ⟨62480677366618551659827673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41653784911079034439885115 62480677366618551659827673)
      ·
        refine ⟨46860508024963913744870755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62480677366618551659827673 46860508024963913744870755)
        ·
          refine ⟨70290762037445870617306133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46860508024963913744870755 70290762037445870617306133)
          ·
            refine ⟨3294879470505275185186225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70290762037445870617306133 3294879470505275185186225)
            ·
              refine ⟨2471159602878956388889669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3294879470505275185186225 2471159602878956388889669)
              ·
                refine ⟨463342425539804322916813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2471159602878956388889669 463342425539804322916813)
                ·
                  refine ⟨173753409577426621093805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463342425539804322916813 173753409577426621093805)
                  ·
                    rfl

theorem cell21_761363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 3].length) (baseStart_761363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761363 prefixEnd_761363 := by exact prefixLift 761363
  have htrace : WordTrace (prefixWord ++ tailWord_761363) baseStart_761363 baseEnd_761363 := by
    simpa [prefixWord, tailWord_761363, baseEnd_761363] using wordTrace_append hprefix tailTrace_761363
  have hstable : (prefixWord ++ tailWord_761363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761363).length < 2 ^ (prefixWord ++ tailWord_761363).sum := by decide
  have hdescent : baseEnd_761363 < baseStart_761363 := by decide
  rcases family_descends (prefixWord ++ tailWord_761363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761414 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_761414 : Nat := 118140960795 + 761414 * 2 ^ 59
def prefixEnd_761414 : Nat := 4983230072969 + 3 ^ 40 * 761414 * 2
def baseEnd_761414 : Nat := 173765048472261865743701

theorem tailTrace_761414 : CollatzResearch.WordTrace tailWord_761414 prefixEnd_761414 173765048472261865743701 := by
  unfold tailWord_761414
  simp only [CollatzResearch.WordTrace]
  refine ⟨867845314485456000105103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18514033375689728002242197 867845314485456000105103)
  ·
    refine ⟨1301767971728184000157655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 867845314485456000105103 1301767971728184000157655)
    ·
      refine ⟨1952651957592276000236483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301767971728184000157655 1952651957592276000236483)
      ·
        refine ⟨2928977936388414000354725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1952651957592276000236483 2928977936388414000354725)
        ·
          refine ⟨549183363072827625066511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2928977936388414000354725 549183363072827625066511)
          ·
            refine ⟨823775044609241437599767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549183363072827625066511 823775044609241437599767)
            ·
              refine ⟨1235662566913862156399651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823775044609241437599767 1235662566913862156399651)
              ·
                refine ⟨1853493850370793234599477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235662566913862156399651 1853493850370793234599477)
                ·
                  refine ⟨173765048472261865743701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1853493850370793234599477 173765048472261865743701)
                  ·
                    rfl

theorem cell21_761414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_761414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761414 prefixEnd_761414 := by exact prefixLift 761414
  have htrace : WordTrace (prefixWord ++ tailWord_761414) baseStart_761414 baseEnd_761414 := by
    simpa [prefixWord, tailWord_761414, baseEnd_761414] using wordTrace_append hprefix tailTrace_761414
  have hstable : (prefixWord ++ tailWord_761414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761414).length < 2 ^ (prefixWord ++ tailWord_761414).sum := by decide
  have hdescent : baseEnd_761414 < baseStart_761414 := by decide
  rcases family_descends (prefixWord ++ tailWord_761414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761473 : List Nat := [1, 2, 4, 2, 1, 4, 2, 2, 3]
def baseStart_761473 : Nat := 118140960795 + 761473 * 2 ^ 59
def prefixEnd_761473 : Nat := 4983230072969 + 3 ^ 40 * 761473 * 2
def baseEnd_761473 : Nat := 173778513076090874260247

theorem tailTrace_761473 : CollatzResearch.WordTrace tailWord_761473 prefixEnd_761473 173778513076090874260247 := by
  unfold tailWord_761473
  simp only [CollatzResearch.WordTrace]
  refine ⟨27773201970320845079761073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18515467980213896719840715 27773201970320845079761073)
  ·
    refine ⟨20829901477740633809820805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27773201970320845079761073 20829901477740633809820805)
    ·
      refine ⟨3905606527076368839341401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20829901477740633809820805 3905606527076368839341401)
      ·
        refine ⟨2929204895307276629506051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3905606527076368839341401 2929204895307276629506051)
        ·
          refine ⟨4393807342960914944259077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2929204895307276629506051 4393807342960914944259077)
          ·
            refine ⟨823838876805171552048577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4393807342960914944259077 823838876805171552048577)
            ·
              refine ⟨617879157603878664036433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 823838876805171552048577 617879157603878664036433)
              ·
                refine ⟨463409368202908998027325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617879157603878664036433 463409368202908998027325)
                ·
                  refine ⟨173778513076090874260247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463409368202908998027325 173778513076090874260247)
                  ·
                    rfl

theorem cell21_761473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 3].length) (baseStart_761473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761473 prefixEnd_761473 := by exact prefixLift 761473
  have htrace : WordTrace (prefixWord ++ tailWord_761473) baseStart_761473 baseEnd_761473 := by
    simpa [prefixWord, tailWord_761473, baseEnd_761473] using wordTrace_append hprefix tailTrace_761473
  have hstable : (prefixWord ++ tailWord_761473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761473).length < 2 ^ (prefixWord ++ tailWord_761473).sum := by decide
  have hdescent : baseEnd_761473 < baseStart_761473 := by decide
  rcases family_descends (prefixWord ++ tailWord_761473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761529 : List Nat := [1, 2, 1, 4, 1, 1, 5, 2, 4]
def baseStart_761529 : Nat := 118140960795 + 761529 * 2 ^ 59
def prefixEnd_761529 : Nat := 4983230072969 + 3 ^ 40 * 761529 * 2
def baseEnd_761529 : Nat := 173791293039047221326799

theorem tailTrace_761529 : CollatzResearch.WordTrace tailWord_761529 prefixEnd_761529 173791293039047221326799 := by
  unfold tailWord_761529
  simp only [CollatzResearch.WordTrace]
  refine ⟨27775244458117966643799641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18516829638745311095866427 27775244458117966643799641)
  ·
    refine ⟨20831433343588474982849731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27775244458117966643799641 20831433343588474982849731)
    ·
      refine ⟨31247150015382712474274597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20831433343588474982849731 31247150015382712474274597)
      ·
        refine ⟨5858840627884258588926487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31247150015382712474274597 5858840627884258588926487)
        ·
          refine ⟨8788260941826387883389731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5858840627884258588926487 8788260941826387883389731)
          ·
            refine ⟨13182391412739581825084597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8788260941826387883389731 13182391412739581825084597)
            ·
              refine ⟨1235849194944335796101681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13182391412739581825084597 1235849194944335796101681)
              ·
                refine ⟨926886896208251847076261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235849194944335796101681 926886896208251847076261)
                ·
                  refine ⟨173791293039047221326799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 926886896208251847076261 173791293039047221326799)
                  ·
                    rfl

theorem cell21_761529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_761529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761529 prefixEnd_761529 := by exact prefixLift 761529
  have htrace : WordTrace (prefixWord ++ tailWord_761529) baseStart_761529 baseEnd_761529 := by
    simpa [prefixWord, tailWord_761529, baseEnd_761529] using wordTrace_append hprefix tailTrace_761529
  have hstable : (prefixWord ++ tailWord_761529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761529).length < 2 ^ (prefixWord ++ tailWord_761529).sum := by decide
  have hdescent : baseEnd_761529 < baseStart_761529 := by decide
  rcases family_descends (prefixWord ++ tailWord_761529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761653 : List Nat := [1, 3, 3, 1, 5, 1, 1, 6]
def baseStart_761653 : Nat := 118140960795 + 761653 * 2 ^ 59
def prefixEnd_761653 : Nat := 4983230072969 + 3 ^ 40 * 761653 * 2
def baseEnd_761653 : Nat := 57939863842816853753293

theorem tailTrace_761653 : CollatzResearch.WordTrace tailWord_761653 prefixEnd_761653 57939863842816853753293 := by
  unfold tailWord_761653
  simp only [CollatzResearch.WordTrace]
  refine ⟨27779767109668735821313613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18519844739779157214209075 27779767109668735821313613)
  ·
    refine ⟨10417412666125775932992605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27779767109668735821313613 10417412666125775932992605)
    ·
      refine ⟨3906529749797165974872227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10417412666125775932992605 3906529749797165974872227)
      ·
        refine ⟨5859794624695748962308341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3906529749797165974872227 5859794624695748962308341)
        ·
          refine ⟨549355746065226465216407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5859794624695748962308341 549355746065226465216407)
          ·
            refine ⟨824033619097839697824611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549355746065226465216407 824033619097839697824611)
            ·
              refine ⟨1236050428646759546736917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824033619097839697824611 1236050428646759546736917)
              ·
                refine ⟨57939863842816853753293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1236050428646759546736917 57939863842816853753293)
                ·
                  rfl

theorem cell21_761653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 6].length) (baseStart_761653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761653 prefixEnd_761653 := by exact prefixLift 761653
  have htrace : WordTrace (prefixWord ++ tailWord_761653) baseStart_761653 baseEnd_761653 := by
    simpa [prefixWord, tailWord_761653, baseEnd_761653] using wordTrace_append hprefix tailTrace_761653
  have hstable : (prefixWord ++ tailWord_761653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761653).length < 2 ^ (prefixWord ++ tailWord_761653).sum := by decide
  have hdescent : baseEnd_761653 < baseStart_761653 := by decide
  rcases family_descends (prefixWord ++ tailWord_761653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761670 : List Nat := [6, 1, 1, 2, 1, 2, 3, 5]
def baseStart_761670 : Nat := 118140960795 + 761670 * 2 ^ 59
def prefixEnd_761670 : Nat := 4983230072969 + 3 ^ 40 * 761670 * 2
def baseEnd_761670 : Nat := 57941157053354103158837

theorem tailTrace_761670 : CollatzResearch.WordTrace tailWord_761670 prefixEnd_761670 57941157053354103158837 := by
  unfold tailWord_761670
  simp only [CollatzResearch.WordTrace]
  refine ⟨868137098456473366396327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18520258100404765149788309 868137098456473366396327)
  ·
    refine ⟨1302205647684710049594491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 868137098456473366396327 1302205647684710049594491)
    ·
      refine ⟨1953308471527065074391737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302205647684710049594491 1953308471527065074391737)
      ·
        refine ⟨1464981353645298805793803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1953308471527065074391737 1464981353645298805793803)
        ·
          refine ⟨2197472030467948208690705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1464981353645298805793803 2197472030467948208690705)
          ·
            refine ⟨1648104022850961156518029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2197472030467948208690705 1648104022850961156518029)
            ·
              refine ⟨618039008569110433694261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1648104022850961156518029 618039008569110433694261)
              ·
                refine ⟨57941157053354103158837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 618039008569110433694261 57941157053354103158837)
                ·
                  rfl

theorem cell21_761670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_761670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761670 prefixEnd_761670 := by exact prefixLift 761670
  have htrace : WordTrace (prefixWord ++ tailWord_761670) baseStart_761670 baseEnd_761670 := by
    simpa [prefixWord, tailWord_761670, baseEnd_761670] using wordTrace_append hprefix tailTrace_761670
  have hstable : (prefixWord ++ tailWord_761670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761670).length < 2 ^ (prefixWord ++ tailWord_761670).sum := by decide
  have hdescent : baseEnd_761670 < baseStart_761670 := by decide
  rcases family_descends (prefixWord ++ tailWord_761670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761684 : List Nat := [2, 4, 1, 1, 3, 2, 2, 3, 3]
def baseStart_761684 : Nat := 118140960795 + 761684 * 2 ^ 59
def prefixEnd_761684 : Nat := 4983230072969 + 3 ^ 40 * 761684 * 2
def baseEnd_761684 : Nat := 173826666150801396243149

theorem tailTrace_761684 : CollatzResearch.WordTrace tailWord_761684 prefixEnd_761684 173826666150801396243149 := by
  unfold tailWord_761684
  simp only [CollatzResearch.WordTrace]
  refine ⟨13890448886278214057846053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18520598515037618743794737 13890448886278214057846053)
  ·
    refine ⟨2604459166177165135846135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13890448886278214057846053 2604459166177165135846135)
    ·
      refine ⟨3906688749265747703769203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2604459166177165135846135 3906688749265747703769203)
      ·
        refine ⟨5860033123898621555653805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3906688749265747703769203 5860033123898621555653805)
        ·
          refine ⟨2197512421461983083370177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5860033123898621555653805 2197512421461983083370177)
          ·
            refine ⟨1648134316096487312527633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2197512421461983083370177 1648134316096487312527633)
            ·
              refine ⟨1236100737072365484395725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1648134316096487312527633 1236100737072365484395725)
              ·
                refine ⟨463537776402137056648397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1236100737072365484395725 463537776402137056648397)
                ·
                  refine ⟨173826666150801396243149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463537776402137056648397 173826666150801396243149)
                  ·
                    rfl

theorem cell21_761684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_761684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761684 prefixEnd_761684 := by exact prefixLift 761684
  have htrace : WordTrace (prefixWord ++ tailWord_761684) baseStart_761684 baseEnd_761684 := by
    simpa [prefixWord, tailWord_761684, baseEnd_761684] using wordTrace_append hprefix tailTrace_761684
  have hstable : (prefixWord ++ tailWord_761684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761684).length < 2 ^ (prefixWord ++ tailWord_761684).sum := by decide
  have hdescent : baseEnd_761684 < baseStart_761684 := by decide
  rcases family_descends (prefixWord ++ tailWord_761684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761698 : List Nat := [3, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_761698 : Nat := 118140960795 + 761698 * 2 ^ 59
def prefixEnd_761698 : Nat := 4983230072969 + 3 ^ 40 * 761698 * 2
def baseEnd_761698 : Nat := 173829861141540483009787

theorem tailTrace_761698 : CollatzResearch.WordTrace tailWord_761698 prefixEnd_761698 173829861141540483009787 := by
  unfold tailWord_761698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6945352098626427126675437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18520938929670472337801165 6945352098626427126675437)
  ·
    refine ⟨2604507036984910172503289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6945352098626427126675437 2604507036984910172503289)
    ·
      refine ⟨1953380277738682629377467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2604507036984910172503289 1953380277738682629377467)
      ·
        refine ⟨2930070416608023944066201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953380277738682629377467 2930070416608023944066201)
        ·
          refine ⟨2197552812456017958049651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2930070416608023944066201 2197552812456017958049651)
          ·
            refine ⟨3296329218684026937074477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197552812456017958049651 3296329218684026937074477)
            ·
              refine ⟨1236123457006510101402929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3296329218684026937074477 1236123457006510101402929)
              ·
                refine ⟨927092592754882576052197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1236123457006510101402929 927092592754882576052197)
                ·
                  refine ⟨173829861141540483009787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 927092592754882576052197 173829861141540483009787)
                  ·
                    rfl

theorem cell21_761698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_761698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761698 prefixEnd_761698 := by exact prefixLift 761698
  have htrace : WordTrace (prefixWord ++ tailWord_761698) baseStart_761698 baseEnd_761698 := by
    simpa [prefixWord, tailWord_761698, baseEnd_761698] using wordTrace_append hprefix tailTrace_761698
  have hstable : (prefixWord ++ tailWord_761698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761698).length < 2 ^ (prefixWord ++ tailWord_761698).sum := by decide
  have hdescent : baseEnd_761698 < baseStart_761698 := by decide
  rcases family_descends (prefixWord ++ tailWord_761698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761785 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 7]
def baseStart_761785 : Nat := 118140960795 + 761785 * 2 ^ 59
def prefixEnd_761785 : Nat := 4983230072969 + 3 ^ 40 * 761785 * 2
def baseEnd_761785 : Nat := 173849715726847665059609

theorem tailTrace_761785 : CollatzResearch.WordTrace tailWord_761785 prefixEnd_761785 173849715726847665059609 := by
  unfold tailWord_761785
  simp only [CollatzResearch.WordTrace]
  refine ⟨27784581545190522365118809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18523054363460348243412539 27784581545190522365118809)
  ·
    refine ⟨20838436158892891773839107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27784581545190522365118809 20838436158892891773839107)
    ·
      refine ⟨31257654238339337660758661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20838436158892891773839107 31257654238339337660758661)
      ·
        refine ⟨5860810169688625811392249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31257654238339337660758661 5860810169688625811392249)
        ·
          refine ⟨4395607627266469358544187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5860810169688625811392249 4395607627266469358544187)
          ·
            refine ⟨6593411440899704037816281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4395607627266469358544187 6593411440899704037816281)
            ·
              refine ⟨4945058580674778028362211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6593411440899704037816281 4945058580674778028362211)
              ·
                refine ⟨7417587871012167042543317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4945058580674778028362211 7417587871012167042543317)
                ·
                  refine ⟨173849715726847665059609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7417587871012167042543317 173849715726847665059609)
                  ·
                    rfl

theorem cell21_761785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_761785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761785 prefixEnd_761785 := by exact prefixLift 761785
  have htrace : WordTrace (prefixWord ++ tailWord_761785) baseStart_761785 baseEnd_761785 := by
    simpa [prefixWord, tailWord_761785, baseEnd_761785] using wordTrace_append hprefix tailTrace_761785
  have hstable : (prefixWord ++ tailWord_761785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761785).length < 2 ^ (prefixWord ++ tailWord_761785).sum := by decide
  have hdescent : baseEnd_761785 < baseStart_761785 := by decide
  rcases family_descends (prefixWord ++ tailWord_761785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761912 : List Nat := [2, 1, 2, 1, 6, 2, 1, 3, 3]
def baseStart_761912 : Nat := 118140960795 + 761912 * 2 ^ 59
def prefixEnd_761912 : Nat := 4983230072969 + 3 ^ 40 * 761912 * 2
def baseEnd_761912 : Nat := 173878698857123666442683

theorem tailTrace_761912 : CollatzResearch.WordTrace tailWord_761912 prefixEnd_761912 173878698857123666442683 := by
  unfold tailWord_761912
  simp only [CollatzResearch.WordTrace]
  refine ⟨13894606807865211527495995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18526142410486948703327993 13894606807865211527495995)
  ·
    refine ⟨20841910211797817291243993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13894606807865211527495995 20841910211797817291243993)
    ·
      refine ⟨15631432658848362968432995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20841910211797817291243993 15631432658848362968432995)
      ·
        refine ⟨23447148988272544452649493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15631432658848362968432995 23447148988272544452649493)
        ·
          refine ⟨1099085108825275521217945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23447148988272544452649493 1099085108825275521217945)
          ·
            refine ⟨824313831618956640913459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1099085108825275521217945 824313831618956640913459)
            ·
              refine ⟨1236470747428434961370189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824313831618956640913459 1236470747428434961370189)
              ·
                refine ⟨463676530285663110513821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1236470747428434961370189 463676530285663110513821)
                ·
                  refine ⟨173878698857123666442683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463676530285663110513821 173878698857123666442683)
                  ·
                    rfl

theorem cell21_761912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 3].length) (baseStart_761912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761912 prefixEnd_761912 := by exact prefixLift 761912
  have htrace : WordTrace (prefixWord ++ tailWord_761912) baseStart_761912 baseEnd_761912 := by
    simpa [prefixWord, tailWord_761912, baseEnd_761912] using wordTrace_append hprefix tailTrace_761912
  have hstable : (prefixWord ++ tailWord_761912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761912).length < 2 ^ (prefixWord ++ tailWord_761912).sum := by decide
  have hdescent : baseEnd_761912 < baseStart_761912 := by decide
  rcases family_descends (prefixWord ++ tailWord_761912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761926 : List Nat := [6, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_761926 : Nat := 118140960795 + 761926 * 2 ^ 59
def prefixEnd_761926 : Nat := 4983230072969 + 3 ^ 40 * 761926 * 2
def baseEnd_761926 : Nat := 173881893847862753209321

theorem tailTrace_761926 : CollatzResearch.WordTrace tailWord_761926 prefixEnd_761926 173881893847862753209321 := by
  unfold tailWord_761926
  simp only [CollatzResearch.WordTrace]
  refine ⟨868428882427490732687551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18526482825119802297334421 868428882427490732687551)
  ·
    refine ⟨1302643323641236099031327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 868428882427490732687551 1302643323641236099031327)
    ·
      refine ⟨1953964985461854148546991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302643323641236099031327 1953964985461854148546991)
      ·
        refine ⟨2930947478192781222820487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953964985461854148546991 2930947478192781222820487)
        ·
          refine ⟨4396421217289171834230731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2930947478192781222820487 4396421217289171834230731)
          ·
            refine ⟨6594631825933757751346097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396421217289171834230731 6594631825933757751346097)
            ·
              refine ⟨4945973869450318313509573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6594631825933757751346097 4945973869450318313509573)
              ·
                refine ⟨927370100521934683783045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4945973869450318313509573 927370100521934683783045)
                ·
                  refine ⟨173881893847862753209321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 927370100521934683783045 173881893847862753209321)
                  ·
                    rfl

theorem cell21_761926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_761926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761926 prefixEnd_761926 := by exact prefixLift 761926
  have htrace : WordTrace (prefixWord ++ tailWord_761926) baseStart_761926 baseEnd_761926 := by
    simpa [prefixWord, tailWord_761926, baseEnd_761926] using wordTrace_append hprefix tailTrace_761926
  have hstable : (prefixWord ++ tailWord_761926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761926).length < 2 ^ (prefixWord ++ tailWord_761926).sum := by decide
  have hdescent : baseEnd_761926 < baseStart_761926 := by decide
  rcases family_descends (prefixWord ++ tailWord_761926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761951 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 8]
def baseStart_761951 : Nat := 118140960795 + 761951 * 2 ^ 59
def prefixEnd_761951 : Nat := 4983230072969 + 3 ^ 40 * 761951 * 2
def baseEnd_761951 : Nat := 173887599188468265292603

theorem tailTrace_761951 : CollatzResearch.WordTrace tailWord_761951 prefixEnd_761951 173887599188468265292603 := by
  unfold tailWord_761951
  simp only [CollatzResearch.WordTrace]
  refine ⟨27790636062589132715661707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18527090708392755143774471 27790636062589132715661707)
  ·
    refine ⟨41685954093883699073492561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27790636062589132715661707 41685954093883699073492561)
    ·
      refine ⟨31264465570412774305119421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41685954093883699073492561 31264465570412774305119421)
      ·
        refine ⟨11724174588904790364419783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31264465570412774305119421 11724174588904790364419783)
        ·
          refine ⟨17586261883357185546629675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11724174588904790364419783 17586261883357185546629675)
          ·
            refine ⟨26379392825035778319944513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17586261883357185546629675 26379392825035778319944513)
            ·
              refine ⟨19784544618776833739958385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26379392825035778319944513 19784544618776833739958385)
              ·
                refine ⟨14838408464082625304968789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19784544618776833739958385 14838408464082625304968789)
                ·
                  refine ⟨173887599188468265292603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14838408464082625304968789 173887599188468265292603)
                  ·
                    rfl

theorem cell21_761951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_761951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_761951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_761951 prefixEnd_761951 := by exact prefixLift 761951
  have htrace : WordTrace (prefixWord ++ tailWord_761951) baseStart_761951 baseEnd_761951 := by
    simpa [prefixWord, tailWord_761951, baseEnd_761951] using wordTrace_append hprefix tailTrace_761951
  have hstable : (prefixWord ++ tailWord_761951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761951).length < 2 ^ (prefixWord ++ tailWord_761951).sum := by decide
  have hdescent : baseEnd_761951 < baseStart_761951 := by decide
  rcases family_descends (prefixWord ++ tailWord_761951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762013 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 7]
def baseStart_762013 : Nat := 118140960795 + 762013 * 2 ^ 59
def prefixEnd_762013 : Nat := 4983230072969 + 3 ^ 40 * 762013 * 2
def baseEnd_762013 : Nat := 173901748433169935259143

theorem tailTrace_762013 : CollatzResearch.WordTrace tailWord_762013 prefixEnd_762013 173901748433169935259143 := by
  unfold tailWord_762013
  simp only [CollatzResearch.WordTrace]
  refine ⟨27792897388364517304418693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18528598258909678202945795 27792897388364517304418693)
  ·
    refine ⟨5211168260318346994578505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27792897388364517304418693 5211168260318346994578505)
    ·
      refine ⟨3908376195238760245933879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5211168260318346994578505 3908376195238760245933879)
      ·
        refine ⟨5862564292858140368900819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3908376195238760245933879 5862564292858140368900819)
        ·
          refine ⟨8793846439287210553351229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5862564292858140368900819 8793846439287210553351229)
          ·
            refine ⟨3297692414732703957506711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8793846439287210553351229 3297692414732703957506711)
            ·
              refine ⟨4946538622099055936260067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3297692414732703957506711 4946538622099055936260067)
              ·
                refine ⟨7419807933148583904390101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4946538622099055936260067 7419807933148583904390101)
                ·
                  refine ⟨173901748433169935259143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7419807933148583904390101 173901748433169935259143)
                  ·
                    rfl

theorem cell21_762013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_762013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762013 prefixEnd_762013 := by exact prefixLift 762013
  have htrace : WordTrace (prefixWord ++ tailWord_762013) baseStart_762013 baseEnd_762013 := by
    simpa [prefixWord, tailWord_762013, baseEnd_762013] using wordTrace_append hprefix tailTrace_762013
  have hstable : (prefixWord ++ tailWord_762013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762013).length < 2 ^ (prefixWord ++ tailWord_762013).sum := by decide
  have hdescent : baseEnd_762013 < baseStart_762013 := by decide
  rcases family_descends (prefixWord ++ tailWord_762013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762058 : List Nat := [3, 1, 2, 1, 3, 1, 2, 8]
def baseStart_762058 : Nat := 118140960795 + 762058 * 2 ^ 59
def prefixEnd_762058 : Nat := 4983230072969 + 3 ^ 40 * 762058 * 2
def baseEnd_762058 : Nat := 57970672682086619003017

theorem tailTrace_762058 : CollatzResearch.WordTrace tailWord_762058 prefixEnd_762058 57970672682086619003017 := by
  unfold tailWord_762058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6948634668300372497451707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18529692448800993326537885 6948634668300372497451707)
  ·
    refine ⟨10422952002450558746177561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6948634668300372497451707 10422952002450558746177561)
    ·
      refine ⟨7817214001837919059633171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10422952002450558746177561 7817214001837919059633171)
      ·
        refine ⟨11725821002756878589449757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7817214001837919059633171 11725821002756878589449757)
        ·
          refine ⟨4397182876033829471043659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11725821002756878589449757 4397182876033829471043659)
          ·
            refine ⟨6595774314050744206565489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4397182876033829471043659 6595774314050744206565489)
            ·
              refine ⟨4946830735538058154924117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6595774314050744206565489 4946830735538058154924117)
              ·
                refine ⟨57970672682086619003017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4946830735538058154924117 57970672682086619003017)
                ·
                  rfl

theorem cell21_762058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_762058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762058 prefixEnd_762058 := by exact prefixLift 762058
  have htrace : WordTrace (prefixWord ++ tailWord_762058) baseStart_762058 baseEnd_762058 := by
    simpa [prefixWord, tailWord_762058, baseEnd_762058] using wordTrace_append hprefix tailTrace_762058
  have hstable : (prefixWord ++ tailWord_762058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762058).length < 2 ^ (prefixWord ++ tailWord_762058).sum := by decide
  have hdescent : baseEnd_762058 < baseStart_762058 := by decide
  rcases family_descends (prefixWord ++ tailWord_762058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762106 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_762106 : Nat := 118140960795 + 762106 * 2 ^ 59
def prefixEnd_762106 : Nat := 4983230072969 + 3 ^ 40 * 762106 * 2
def baseEnd_762106 : Nat := 173922972300222440208953

theorem tailTrace_762106 : CollatzResearch.WordTrace tailWord_762106 prefixEnd_762106 173922972300222440208953 := by
  unfold tailWord_762106
  simp only [CollatzResearch.WordTrace]
  refine ⟨6949072344256898546888543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18530859584685062791702781 6949072344256898546888543)
  ·
    refine ⟨10423608516385347820332815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6949072344256898546888543 10423608516385347820332815)
    ·
      refine ⟨15635412774578021730499223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10423608516385347820332815 15635412774578021730499223)
      ·
        refine ⟨23453119161867032595748835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15635412774578021730499223 23453119161867032595748835)
        ·
          refine ⟨35179678742800548893623253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23453119161867032595748835 35179678742800548893623253)
          ·
            refine ⟨824523720534387864694295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35179678742800548893623253 824523720534387864694295)
            ·
              refine ⟨1236785580801581797041443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824523720534387864694295 1236785580801581797041443)
              ·
                refine ⟨1855178371202372695562165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236785580801581797041443 1855178371202372695562165)
                ·
                  refine ⟨173922972300222440208953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1855178371202372695562165 173922972300222440208953)
                  ·
                    rfl

theorem cell21_762106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_762106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762106 prefixEnd_762106 := by exact prefixLift 762106
  have htrace : WordTrace (prefixWord ++ tailWord_762106) baseStart_762106 baseEnd_762106 := by
    simpa [prefixWord, tailWord_762106, baseEnd_762106] using wordTrace_append hprefix tailTrace_762106
  have hstable : (prefixWord ++ tailWord_762106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762106).length < 2 ^ (prefixWord ++ tailWord_762106).sum := by decide
  have hdescent : baseEnd_762106 < baseStart_762106 := by decide
  rcases family_descends (prefixWord ++ tailWord_762106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762154 : List Nat := [3, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_762154 : Nat := 118140960795 + 762154 * 2 ^ 59
def prefixEnd_762154 : Nat := 4983230072969 + 3 ^ 40 * 762154 * 2
def baseEnd_762154 : Nat := 173933926554185023408855

theorem tailTrace_762154 : CollatzResearch.WordTrace tailWord_762154 prefixEnd_762154 173933926554185023408855 := by
  unfold tailWord_762154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6949510020213424596325379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18532026720569132256867677 6949510020213424596325379)
  ·
    refine ⟨10424265030320136894488069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6949510020213424596325379 10424265030320136894488069)
    ·
      refine ⟨1954549693185025667716513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10424265030320136894488069 1954549693185025667716513)
      ·
        refine ⟨1465912269888769250787385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1954549693185025667716513 1465912269888769250787385)
        ·
          refine ⟨1099434202416576938090539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1465912269888769250787385 1099434202416576938090539)
          ·
            refine ⟨1649151303624865407135809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099434202416576938090539 1649151303624865407135809)
            ·
              refine ⟨1236863477718649055351857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1649151303624865407135809 1236863477718649055351857)
              ·
                refine ⟨927647608288986791513893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1236863477718649055351857 927647608288986791513893)
                ·
                  refine ⟨173933926554185023408855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 927647608288986791513893 173933926554185023408855)
                  ·
                    rfl

theorem cell21_762154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_762154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_762154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_762154 prefixEnd_762154 := by exact prefixLift 762154
  have htrace : WordTrace (prefixWord ++ tailWord_762154) baseStart_762154 baseEnd_762154 := by
    simpa [prefixWord, tailWord_762154, baseEnd_762154] using wordTrace_append hprefix tailTrace_762154
  have hstable : (prefixWord ++ tailWord_762154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762154).length < 2 ^ (prefixWord ++ tailWord_762154).sum := by decide
  have hdescent : baseEnd_762154 < baseStart_762154 := by decide
  rcases family_descends (prefixWord ++ tailWord_762154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
